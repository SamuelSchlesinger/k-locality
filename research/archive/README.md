# Historical material

These files preserve the project's development history. For the current
mathematics and proof status, read [main.tex](../../main.tex),
[FORMALIZATION.md](../../FORMALIZATION.md), and
[VERIFICATION.md](../../VERIFICATION.md).

- [Revival memo](revival.md): July 2026 reconstruction of the original
  support argument and its repair. Its progress reports describe that checkpoint.
- [Interior-feasibility writeup](interior-feasibility.tex): the longer record
  of the failed local-positivity implication. A compact version remains in the
  manuscript, and the [Lean example](../../KLocality/InteriorFeasibilityCounterexample.lean)
  is still part of the checked library. Build this historical writeup with
  `make archive`.
- [Literature history bundle](literature-transfer-history.bundle): preserved
  Git history for the imported literature corpus. Inspect its advertised refs
  with `git bundle list-heads research/archive/literature-transfer-history.bundle`
  from the repository root. The current notes live in
  [literature-transfer](../literature-transfer/index.md).
