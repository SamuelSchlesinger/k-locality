# Structured families and recognition

This dossier develops three mathematical routes: well-conditioned full-support
families, explicit selector obstructions, and circuit or recognition consequences.
The completed arguments feed into the [manuscript](../../../main.tex).
The [formalization manifest](../../../FORMALIZATION.md) records their Lean coverage.

## Routes

- [Natural full-support families](natural-full-support.md): exchangeable laws
  with a bounded likelihood ratio and a superlogarithmic localization lower bound.
- [Explicit selector obstructions](selector-explicit.md): filtered witness-slice
  bounds for structured supports and the limits of block symmetry.
- [Circuit consequences](circuit-consequences.md): dense-table recognition,
  simulation bounds, and barriers to circuit applications.

## Mathematical status

| Route | Result | Remaining boundary |
|---|---|---|
| Natural full support | The radial law `D_n(x)` proportional to `exp(-2^(abs(x)/r_n))` has `LC_k(D_n)=Theta_k(n^(1/k))` for every fixed `k>=2`, with likelihood ratio below `e^3` | Manuscript proof and finite checks; Lean formalization remains open |
| Explicit selector | Exact one-block complexity `r` and exact block-symmetric `m`-block complexity `mr` for separated block-layer supports | The unrestricted direct sum remains open |
| Recognition | Quasipolynomial dense exact recognition for fixed locality and a linear latent budget, with a sharper fixed-budget full-support bound and an ETH barrier | Manuscript proof and exact finite identities; polynomial-time global recognition and Lean formalization remain open |

Here `abs(x)` denotes Hamming weight and `r_n=2^floor(log_2(n+1))`.
The scripts under `data/` check finite instances or identities only. The source
comparisons record the original literature audit and do not establish priority.
