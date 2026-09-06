# Research notes and experiments

The [manuscript](../main.tex) is the current mathematical account;
[FORMALIZATION.md](../FORMALIZATION.md) records its Lean coverage. This directory
contains supporting notes, finite validators, and exploratory programs.

## Reading map

- [Explicit lower bounds](../notes/explicit-lower-bounds.tex): a companion to
  the Lean base-coded, Boolean-tilt, and block-parity constructions.
- [Block-parity fiber](block-parity-fiber.md): the structured Fourier route,
  canonical finite-search result, and remaining efficient-explicitness problem.
- [Support invariants](support-invariants.md): development notes on facial
  covers, filtered witness slices, and related lower-bound methods.
- [Literature and transfer notes](literature-transfer/index.md): comparisons
  with hierarchical models, RBMs, quadratization, and circuits. These record
  earlier source checks, not a current certification of priority.
- [Archive](archive/README.md): the revival memo, the standalone boundary
  counterexample, and the literature corpus's original Git history.

## Default finite validation

Run `make check-finite` from the repository root with Python 3.10 or newer.
These six scripts use only the standard library. Assertions must be enabled;
the Make target sets `PYTHONOPTIMIZE=0`.

| Script | Scope and interpretation |
|---|---|
| [Sextic profile matching](generate_sextic_matching.py) | Reproduce the explicit permutation of all 192 expanded profiles and its inverse, as stored and independently kernel-checked in `NonzeroHiddenCertificateExample.lean` |
| [Block lift](literature-transfer/quadratization/data/validate_block_lift.py) | All `0 <= n <= 8`, `2 <= k <= 5`; quadratic penalty truth table and every visible monomial. Hidden assignments are exhausted only when there are at most 10 feature bits |
| [RBM bound arithmetic](literature-transfer/rbm/data/check_bounds.py) | Integer parameter counts and transcribed published bounds for `2 <= n <= 14`; no unrestricted-localization lower-bound claim |
| [Exchangeable construction](literature-transfer/flagship-routes/data/validate_eisenstein_radial.py) | By default `1 <= n <= 64`, lookup orders `2 <= k <= 5`; encoding, dimension threshold, Eisenstein coefficient conditions, and exact energy-range inequalities. Printed decimal values are illustrative |
| [Selector block layers](literature-transfer/flagship-routes/data/validate_selector_block_layers.py) | The explicitly listed small block systems; primitive-line margins, hidden-witness uniqueness, and nonnegative polynomial zero sets |
| [Full-support recognition identities](literature-transfer/flagship-routes/data/validate_full_support_recognition_reduction.py) | Exact rational identities on representative quadratic one-hidden-bit faces; this is not an implementation of the asymptotic recognition algorithm |

The scripts print their parameters or tested cases. Their outputs establish
those finite statements only. The Lean identity executions in
[check_universal_marginal.lean](check_universal_marginal.lean) run under
`make check-lean` and have a separate uniform soundness/completeness theorem.

The sextic pairing generator prints the Lean data declarations when run
without `--check`. The checked permutation replaces a costly search for
multiset equality; its inverse laws and every paired profile equality are
verified in Lean without compiler-backed proof evaluation.

## Optional discovery programs

SageMath supplies exact matrices and finite fields to the four programs below.
Invoke them with `sage -python`; `--help` lists all parameters. Seed zero and
prime `1000003` are their defaults. Record the Sage version, full command,
seed, field, sample counts, and output when citing a run.

| Program | Purpose |
|---|---|
| [analyze_block_parity_fiber.py](analyze_block_parity_fiber.py) | Exhaustive visible-moment and agreement-kernel identities for `q <= 3`, followed by optional sampled finite-field rank evaluation |
| [search_cubic_one_hidden_certificate.py](search_cubic_one_hidden_certificate.py) | Search homogeneous cubic marginal identities; the Hamming-family mode uses sampled finite-field evaluations |
| [search_hamming_fiber_relations.py](search_hamming_fiber_relations.py) | Search relations among Hamming-coset monomials using sampled evaluations |
| [search_cubic_markov_fiber.py](search_cubic_markov_fiber.py) | Sample one visible cubic-moment fiber and search for candidate relations |

The reproducible block-parity commands are:

```sh
sage -python research/analyze_block_parity_fiber.py --prefix-bits 2 --seed 0
sage -python research/analyze_block_parity_fiber.py --prefix-bits 3 --samples 280 --seed 0
```

`make check-sage` runs both and keeps Sage's writable state under `output/sage/`.
Use `--skip-rank` for only the exhaustive kernel
identities. A sampled matrix's rank is a lower bound on the polynomial-map
rank; a vector in its sampled kernel still needs an exact identity check.

[search_cubic_code_transport.py](search_cubic_code_transport.py) instead needs
the Python package `z3-solver`. It searches encoding widths 5 through 8, with
no time limit, when run as a script. Solver output is discovery data and must
be checked against `MarginalTradeCertificate.profileBalance` before use as a
certificate. These discovery programs are not required to build the paper or
check the Lean library.
