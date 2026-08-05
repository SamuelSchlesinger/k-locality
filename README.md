# Localization Complexity

This repository contains the paper **"Localization Complexity of Hidden-Variable Gibbs Models"** by Samuel Schlesinger and Joshua Grochow.

## Model convention

`L_k(D)` counts binary latent coordinates only.  The lifted law belongs to the
topological closure of the fully connected order-at-most-`k` hierarchical
exponential family: coefficients may be arbitrary reals, hidden variables may
interact with one another, and the joint law may lie on a boundary face even
when `D` has full support.  In particular, `L_2` is not restricted-Boltzmann-
machine hidden-unit complexity, and it is not a coefficient-bounded or
finite-precision resource.

The manuscript uses “fixed temperature” only for a target visible family.
Competing localizations are still allowed to use boundary joint lifts.

## Gibbs reductions

A `k`-Gibbs reduction uses a source distribution as a free base measure,
multiplies it by an order-at-most-`k` Gibbs factor on the source and fresh
coordinates, and reads the target from designated coordinates.  Its cost is
the number of fresh coordinates.  These reductions compose additively, and
the cost from the zero-variable distribution to an `n`-bit law `D` is exactly
`n + L_k(D)`.  Facial conditioning and the circuit-trace constructions are
instances of this calculus.

This is projective access to the source's probability weights, not a
sample-preserving stochastic channel.  Like `L_k`, the reduction notion is
nonuniform unless coefficient descriptions and construction algorithms are
separately bounded.

## Main results

- **Sharp worst-case scale.**  A balanced block-feature graph gives
  `L_k(D)=O_k(2^(n/k))` for every distribution.  A boundary-safe projective
  marginal-variety obstruction gives the matching generic full-support lower
  bound, so the worst-case and almost-everywhere scale is
  `Theta_k(2^(n/k))`.
- **Structured full-support lower bound.**  Every exchangeable law satisfies
  `L_k(D)=O_k(n^(1/k))`, while
  `D_n(x) proportional to exp(-2^(|x|/r_n))`, with
  `r_n=2^floor(log_2(n+1))`, has `L_k(D_n)=Theta_k(n^(1/k))` and likelihood
  ratio below `e^3`.
- **Certificates and transfer.**  Marginal ideals give exact hidden-budget
  certificates and effective rational hard Gibbs rays.  A closed tropical
  image proves the zero-temperature lower-bound transfer from unrestricted
  degree-`k` pseudo-Boolean auxiliary complexity.

## Secondary results and boundaries

- Dense exact rational tables admit deterministic quasipolynomial recognition
  for every linear latent budget, with a sharper exponent for fixed-budget
  full-support tables and a polynomial-time zero-latent case.  Under ETH this
  rules out ordinary polynomial-output NP-hardness reductions in the dense
  input model.
- Quadratic NAND traces give circuit-to-localization upper bounds, while every
  exposed support face compiles back to a nondeterministic support circuit.
  This yields circuit and natural-proofs barriers, not new circuit lower
  bounds.  Full-support weighted lower bounds avoid those barriers.
- The appendices develop `GSE_k`, filtered witness slices, facial covers,
  sign-definite degree, exact parity localization, almost-all-support bounds,
  and adjacent hierarchy separations.
- Interior, coefficient-bounded, finite-precision, approximate, sampled, and
  succinct-input versions remain separate open problems.

## Repository map

- `main.tex`: authoritative manuscript.
- `VERIFICATION.md`: theorem-by-theorem evidence and reproducible checks.
- `REVIVAL.md`: commit-history audit and the repair of the failed
  support-intersection converse.
- `INVARIANTS.md`: support invariants and further lower-bound routes.
- `research/literature-transfer/`: primary-source transfer and novelty audit,
  with finite validation programs under its `data/` directories.

## Building

Requires a TeX distribution with `pdflatex`, `biber`, and `latexmk`.  The
recommended build is:

```bash
latexmk -pdf main.tex
```

Equivalently, run the underlying tools directly:

```bash
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```

## Lean Formalization

This repository also contains a partial Lean 4 development (`KLocality`).  Its checked and unchecked boundaries are:

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
- `KLocality/GroundState.lean` supplies the first Hamiltonian-to-locality layer:
  - finite PMF expectations and preservation under marginalization,
  - scoped local energy terms and their canonical marginal constraints,
  - `uniformOn_isKLocalMarginal_of_localEnergy`: a nonnegative sum of
    scope-at-most-`k` terms makes the uniform law on any nonempty exact ground
    space `k`-local.  This certificate permits cancellation among local terms,
    unlike the older zero-cell `LocalVerificationWitness` route.
- `KLocality/QuadraticNAND.lean` formalizes the algebraic kernel of quadratic
  NAND synthesis:
  - a datatype whose only terms are constant, unary, or pairwise, so degree at
    most two is enforced syntactically,
  - the exact NAND polynomial, nonnegativity, and its zero-set truth table,
  - summed NAND Hamiltonians, output-one and equality penalties,
  - `uniformOn_nandGroundStates_isTwoLocal` and
    `uniformOn_nandAcceptingGroundStates_isTwoLocal` for arbitrary finite NAND
    constraint systems with nonempty ground spaces.
- `KLocality/GroundStateProjection.lean` proves the finite counting bridge:
  a bijection, or equivalently one unique lifted extension per visible state,
  sends the uniform lifted law to the uniform visible law.
- `KLocality/NANDCircuit.lean` gives a typed sequential NAND circuit model:
  - acyclicity is enforced by the gate-indexed `nil`/`snoc` syntax,
  - every gate compiles to one quadratic NAND constraint,
  - the computed trace satisfies all constraints, and any satisfying assignment
    extending fixed inputs is proved equal to that trace.
- `KLocality/NANDCircuitLocalization.lean` completes the constant-free recognizer
  construction:
  - total wires are transported to `Sum (Fin n) (Fin s)`, with exactly `s`
    latent gate bits,
  - accepting ground states are proved to be the unique traces over accepted inputs,
  - their uniform law is both 2-local and a marginal model of the uniform accepted-input law,
  - `localizationComplexityBits_le_CNAND` checks
    `LC_2(U_S) <= C_NAND(S)` for the typed constant-free sequential NAND convention.
- `KLocality/NANDCircuitWithConstants.lean` matches the manuscript's hardwired-input-
  constant convention without adding fake constant wires:
  - a gate source is either a prior wire or a Boolean constant,
  - literal substitution into the exact NAND polynomial remains syntactically quadratic,
  - the substituted penalty is nonnegative and vanishes exactly on the NAND relation,
  - typed traces, one-constraint-per-gate compilation, and trace uniqueness are checked.
- `KLocality/NANDCircuitWithConstantsLocalization.lean` proves the paper-facing
  recognizer construction:
  - constants contribute no assignment coordinate and every NAND gate contributes
    exactly one latent bit,
  - accepting quadratic ground states have exactly one extension over each accepted input,
  - `localizationComplexityBits_le_CNAND` checks the constants-allowed
    `LC_2(U_S) <= C_NAND(S)` bound, conditional only on the explicit recognizer-existence
    witness required by the current `Nat.find` API.
- `KLocality/CircuitConnections.lean` contains deterministic witness-level bridges and derived
  paper-shaped complexity definitions and upper-bound statements:
  - `CComplexity` for fan-in-`r` recognizer size (`C_r(S)`),
  - `GComplexity` for fan-in-`r` generator complexity (`G_r(D)`),
  - `support_eq_range_of_generates` and the seed-witness characterization of
    support membership for exact uniform-seed generators,
  - paper-notation aliases `C_r`, `G_r`, and `LC_k`,
  - bridge assumptions are now concrete local-verification witness builders
    (`GeneratorToLocalizationBridge`, `FlatRecognizerToLocalizationBridge`)
    instead of opaque existence maps, but the builders themselves remain assumptions rather than constructed proofs,
  - `localizationComplexity_le_GComplexity` and
    `localizationComplexity_le_CComplexity_of_flat_bridge`,
  - paper-notation theorem aliases `LC_k_le_G_r` and `LC_k_le_C_r_of_flat`, which line up with
    `LC_k(D) ≤ G_{k-1}(D)` and `LC_k(D) ≤ C_{k-1}(S)` once the corresponding
    circuit-to-localization bridge hypotheses are supplied.
- `KLocality/InteriorFeasibilityCounterexample.lean` contains a concrete finite-dimensional
  counterexample showing that pairwise-local feasibility does not imply a strictly positive
  global feasible point, together with its quadratic exposing-energy certificate and a proof
  that the displayed boundary witness is the unique feasible global table.

The checked recognizer theorem now includes the paper's hardwired-input-constant
accounting.  A translation from cslib's permissive raw DAG representation, NAND
universality/existence inside Lean, and the generator theorem `LC_2 <= G_NAND`
remain to be done.  The older generic fan-in circuit bounds in
`CircuitConnections.lean` still use explicit bridge hypotheses; the concrete NAND
theorems are deliberately separate.
The full face--Gibbs equivalence, including exposing energies and nonuniform
within-face Gibbs weights, universal and balanced feature lifts,
algebraic certificates, support invariants, recognition algorithms,
zero-temperature transfer, exchangeable bounds, and circuit converses are also
not yet Lean-formalized.  Universal existence is still missing, so the current
`LC_k` API requires an explicit existence proof.

The cslib dependency is pinned to reachable commit `8961914`, which uses the same Lean `v4.29.0-rc2` toolchain and contains the circuit modules imported here.  A clean dependency refresh followed by `lake build` succeeds at this revision.

Build with:

```bash
lake build
```
