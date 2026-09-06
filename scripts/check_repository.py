#!/usr/bin/env python3
"""Check research-artifact consistency using only the Python standard library.

This validates the manifest's coverage and syntax, not mathematical equivalence
between manuscript and Lean statements. TeX parsing follows this repository's
literal environments and labels; macro-generated results are not supported.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
RESULT_KINDS = "theorem|lemma|proposition|corollary|conjecture"
RESULT = re.compile(
    rf"\\begin\{{({RESULT_KINDS})\}}(.*?)\\end\{{\1\}}", re.DOTALL
)
LABEL = re.compile(r"\\label\{([^{}]+)\}")
ROW = re.compile(r"^\| `([^`]+)` \| (.*?) \| (\w+) \| (.*?) \|$", re.MULTILINE)
IMPORT = re.compile(r"^import (KLocality(?:\.\w+)+)\s*$", re.MULTILINE)
PLACEHOLDER = re.compile(r"\b(?:sorry|admit)\b|^\s*(?:private\s+)?axiom\b", re.MULTILINE)
LINK = re.compile(r"\[[^\]\n]+\]\((<[^>]+>|[^\s)]+)(?:\s+\"[^\"]*\")?\)")


def tex_without_comments(source: str) -> str:
    """Remove comments while preserving line numbers and escaped percent signs."""
    lines = []
    for line in source.splitlines(keepends=True):
        for index, char in enumerate(line):
            if char != "%":
                continue
            preceding = line[:index]
            slashes = len(preceding) - len(preceding.rstrip("\\"))
            if slashes % 2 == 0:
                line = line[:index] + ("\n" if line.endswith("\n") else "")
                break
        lines.append(line)
    return "".join(lines)


def check_manifest(root: Path) -> tuple[list[str], Counter]:
    errors = []
    tex = tex_without_comments((root / "main.tex").read_text())
    manifest = (root / "FORMALIZATION.md").read_text()
    duplicate_labels = [label for label, count in Counter(LABEL.findall(tex)).items() if count > 1]
    if duplicate_labels:
        errors.append(f"Duplicate LaTeX labels: {duplicate_labels}")

    results = list(RESULT.finditer(tex))
    begin_count = len(re.findall(rf"\\begin\{{(?:{RESULT_KINDS})\}}", tex))
    if len(results) != begin_count:
        errors.append("Unmatched theorem-like environments in main.tex")
    paper_labels = {}
    for result in results:
        labels = LABEL.findall(result.group(2))
        primary = [label for label in labels if re.match(r"(?:thm|lem|prop|cor|conj):", label)]
        if len(primary) != 1:
            line = tex.count("\n", 0, result.start()) + 1
            errors.append(f"main.tex:{line}: result needs exactly one primary theorem label")
            continue
        paper_labels[primary[0]] = result.group(1)

    rows = ROW.findall(manifest)
    row_labels = [row[0] for row in rows]
    for label, count in Counter(row_labels).items():
        if count != 1:
            errors.append(f"Manifest label {label} occurs {count} times")
    for label in sorted(paper_labels.keys() - set(row_labels)):
        errors.append(f"Missing manifest row: {label}")
    for label in sorted(set(row_labels) - paper_labels.keys()):
        errors.append(f"Stale manifest row: {label}")
    statuses = Counter()
    for label, _, status, boundary in rows:
        statuses[status] += 1
        if status not in {"checked", "partial", "open", "conjecture"}:
            errors.append(f"Invalid status for {label}: {status}")
        if (paper_labels.get(label) == "conjecture") != (status == "conjecture"):
            errors.append(f"Conjecture status mismatch: {label}")
        if status == "checked" and not re.search(r"`[A-Za-z]\w*`", boundary):
            errors.append(f"Checked row needs a named Lean declaration: {label}")
    if not rows or not results:
        errors.append("The manuscript and manifest must contain results")
    return errors, statuses


def check_sources(root: Path) -> list[str]:
    errors = []
    library = sorted((root / "KLocality").rglob("*.lean"))
    umbrella = root / "KLocality.lean"
    expected = {str(path.relative_to(root).with_suffix("")).replace("/", ".") for path in library}
    imported = IMPORT.findall(umbrella.read_text())
    if set(imported) != expected:
        errors.append(f"Umbrella imports missing={sorted(expected - set(imported))}, "
                      f"unknown={sorted(set(imported) - expected)}")
    if len(imported) != len(set(imported)):
        errors.append("Duplicate imports in KLocality.lean")
    lean_files = library + [umbrella]
    for directory in ("research", "scripts"):
        lean_files.extend((root / directory).rglob("*.lean"))
        for path in sorted((root / directory).rglob("*.py")):
            try:
                compile(path.read_text(), str(path), "exec")
            except SyntaxError as error:
                errors.append(f"{path.relative_to(root)}:{error.lineno}: {error.msg}")
    for path in lean_files:
        source = path.read_text()
        for match in PLACEHOLDER.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(root)}:{line}: proof placeholder or declared axiom")
    return errors


def check_links(root: Path) -> list[str]:
    errors = []
    documents = sorted(root.glob("*.md"))
    for directory in ("docs", "research", "notes"):
        documents.extend(sorted((root / directory).rglob("*.md")))
    for path in documents:
        source = path.read_text()
        # Ignore examples inside fenced code blocks.
        source = re.sub(r"^```[^\n]*\n.*?^```\s*$", "", source, flags=re.MULTILINE | re.DOTALL)
        for match in LINK.finditer(source):
            target = urlsplit(match.group(1).strip("<>"))
            if target.scheme or target.netloc or not target.path:
                continue
            local = path.parent / unquote(target.path)
            if not local.exists():
                errors.append(f"{path.relative_to(root)}: missing link target {target.path}")
    return errors


def check_tex_log(path: Path) -> list[str]:
    if not path.is_file():
        return [f"Missing TeX log: {path}"]
    failures = re.compile(
        r"undefined|multiply[- ]defined|Rerun to get cross-references|"
        r"Please \(re\)run Biber|Overfull \\[hv]box|Missing character:|^!",
        re.IGNORECASE | re.MULTILINE,
    )
    return [f"{path}:{number}: {line.strip()}"
            for number, line in enumerate(path.read_text(errors="replace").splitlines(), 1)
            if failures.search(line)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex-log", type=Path, help="also reject unresolved references and layout overflow")
    args = parser.parse_args()
    errors, statuses = check_manifest(ROOT)
    errors.extend(check_sources(ROOT))
    errors.extend(check_links(ROOT))
    if args.tex_log:
        errors.extend(check_tex_log(args.tex_log))
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    summary = ", ".join(f"{status}={statuses[status]}" for status in ("checked", "partial", "open", "conjecture"))
    print(f"Manifest: {sum(statuses.values())} results ({summary}).")
    print("Source, import, and local-link checks passed.")
    if args.tex_log:
        print(f"TeX log checks passed: {args.tex_log}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
