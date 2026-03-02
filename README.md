# Localization Complexity

This repository contains the paper **"Localization Complexity: Core Definitions and Circuit Connections"** by Samuel Schlesinger and Joshua Grochow.

## Scope

This draft focuses on:

- Core definitions: marginal models, *k*-local distributions, *k*-localizations, and localization complexity `L_k(D)`.
- A central **local verification theorem** that certifies when a uniform trace distribution is maximum-entropy under local constraints.
- Two deterministic circuit-to-localization upper bounds:
  - `L_k(D) <= G_{k-1}(D)` (generator complexity),
  - `L_k(D) <= C_{k-1}(S)` for flat `D` on support `S`.

## Building

Requires a TeX distribution with `pdflatex` and `biber`:

```
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```

## Lean Formalization

This repository also contains a Lean 4 project (`KLocality`) formalizing the deterministic results in the paper and the interior-feasibility counterexample.

- `lakefile.toml` depends on the `SamuelSchlesinger/cslib` fork for circuit formalization.
- `KLocality/Core.lean` now defines locality internals locally in this repository:
  - scoped marginal constraints over finite variable sets,
  - `k`-locality via maximum-entropy under those constraints,
  - a proved local-verification theorem in the marginal setting:
    `localVerificationMaximumEntropyMarginalsOnFinset` and
    `localVerificationIsKLocalMarginalOnFinset`,
  - a concrete witness format `LocalVerificationWitness` and constructor
    `kLocalizationOfWitness`,
  - marginal models, `k`-localizations, and localization complexity (`Nat.find`) with monotonicity lemmas.
- `KLocality/CircuitConnections.lean` contains deterministic witness-level bridges and derived
  paper-shaped complexity definitions and upper-bound statements:
  - `CComplexity` for fan-in-`r` recognizer size (`C_r(S)`),
  - `GComplexity` for fan-in-`r` generator complexity (`G_r(D)`),
  - paper-notation aliases `C_r`, `G_r`, and `LC_k`,
  - bridge assumptions are now concrete local-verification witness builders
    (`GeneratorToLocalizationBridge`, `FlatRecognizerToLocalizationBridge`)
    instead of opaque existence maps,
  - `localizationComplexity_le_GComplexity` and
    `localizationComplexity_le_CComplexity_of_flat_bridge`,
  - paper-notation theorem aliases `LC_k_le_G_r` and `LC_k_le_C_r_of_flat`, which line up with
    `LC_k(D) ≤ G_{k-1}(D)` and `LC_k(D) ≤ C_{k-1}(S)` once the corresponding
    circuit-to-localization bridge hypotheses are supplied.
- `KLocality/InteriorFeasibilityCounterexample.lean` contains a concrete finite-dimensional
  counterexample showing that pairwise-local feasibility does not imply a strictly positive
  global feasible point (interior feasibility can fail).

Build with:

```bash
lake build
```
