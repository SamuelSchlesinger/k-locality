#!/usr/bin/env python3
"""Reproduce the explicit pairing used by the kernel-checked sextic trade.

The 192 positive expanded profiles are paired with the first unused equal
negative profile, in term/mask order. This is deterministic integer arithmetic.
The resulting permutation and its inverse are independently checked in Lean.
Run with --check to compare the stored Lean tables, or without it to print them.
"""

import argparse
from collections import defaultdict, deque
from itertools import combinations
from pathlib import Path
import re


POSITIVE = ((0, 6, 9, 19, 21, 28), (1, 2, 12, 20, 23, 25), (3, 4, 8, 17, 22, 29))
NEGATIVE = ((0, 3, 12, 21, 22, 25), (1, 6, 8, 19, 20, 29), (2, 4, 9, 17, 23, 28))
LEAN_SOURCE = Path(__file__).resolve().parents[1] / "KLocality" / "NonzeroHiddenCertificateExample.lean"


def profile(term, mask):
    states = [visible | (((mask >> index) & 1) << 5) for index, visible in enumerate(term)]
    return tuple(sum(all((state >> coordinate) & 1 for coordinate in scope) for state in states)
                 for size in range(3) for scope in combinations(range(6), size))


def matching_codes():
    remaining = defaultdict(deque)
    for term_index, term in enumerate(NEGATIVE):
        for mask in range(64):
            remaining[profile(term, mask)].append(64 * term_index + mask)
    forward = []
    for term in POSITIVE:
        for mask in range(64):
            matches = remaining[profile(term, mask)]
            if not matches:
                raise ValueError("Positive profile has no unused negative match")
            forward.append(matches.popleft())
    if any(remaining.values()) or sorted(forward) != list(range(192)):
        raise ValueError("Profile matching is not a permutation")
    inverse = [0] * 192
    for source, target in enumerate(forward):
        inverse[target] = source
    return forward, inverse


def lean_tables():
    parts = []
    for name, codes in zip(("sexticProfileForwardCodes", "sexticProfileInverseCodes"), matching_codes()):
        rows = [", ".join(map(str, codes[start:start + 16])) for start in range(0, len(codes), 16)]
        parts.append(f"private def {name} : List Nat :=\n  [" + ",\n   ".join(rows) + "]\n")
    return "\n".join(parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare generated tables with the Lean source")
    args = parser.parse_args()
    if not args.check:
        print(lean_tables(), end="")
        return
    source = LEAN_SOURCE.read_text()
    for name, expected in zip(("sexticProfileForwardCodes", "sexticProfileInverseCodes"), matching_codes()):
        match = re.search(rf"private def {name} : List Nat :=\s*\[([\d,\s]+)\]", source)
        if not match or [int(value) for value in match.group(1).split(",")] != expected:
            raise ValueError(f"Stored Lean table differs from deterministic matching: {name}")
    print("Sextic matching: all 192 expanded profiles paired; both stored permutations reproduced.")


if __name__ == "__main__":
    main()
