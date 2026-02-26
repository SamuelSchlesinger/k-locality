# Localization Complexity

This repository contains the paper **"Localization Complexity: Core Definitions and Circuit Connections"** by Samuel Schlesinger and Joshua Grochow.

## Scope

This draft focuses on:

- Core definitions: marginal models, *k*-local distributions, *k*-localizations, and localization complexity `L_k(D)`.
- A central **local verification theorem** that certifies when a uniform trace distribution is maximum-entropy under local constraints.
- Three circuit-to-localization upper bounds:
  - `L_k(D) <= G_{k-1}(D)` (generator complexity),
  - `L_k(D) <= C_{k-1}(S)` for flat `D` on support `S`,
  - `L_k(D) <= W_{k-1}(D)` (witness-counting complexity).
- A conditional converse section linking `L_k` to nondeterministic support complexity
  under an explicit maximal-support hypothesis.

## Building

Requires a TeX distribution with `pdflatex` and `biber`:

```
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```

## Lean Formalization

This repository also contains a Lean 4 project (`KLocality`) for formalizing the current core results.

- `lakefile.toml` depends on the `SamuelSchlesinger/cslib` fork.
- `KLocality/Core.lean` re-exports the Cslib foundations and includes:
  - support-level `k`-locality and localization definitions,
  - entropy lemmas (`H(p) <= log |S|` for support-constrained `p`, exact entropy of `uniformOn`),
  - a finite local-verification max-entropy certificate,
  - marginal-constraint foundations (`MarginalConstraint`, `FeasibleMarginals`, and
    max-entropy `k`-local marginal certificates),
  - a formal `localizationComplexity` (`Nat.find`) API with monotonicity.
- `KLocality/CircuitConnections.lean` contains witness-level circuit bridges and derived
  `localizationComplexity` upper bounds from those witnesses.
- `KLocality/NondeterministicConverse.lean` contains the formal conditional converse
  framework (projection + local-check compilation assumptions) and the resulting
  support-complexity upper bound at both witness level and `localizationComplexity`.

Build with:

```bash
lake build
```
