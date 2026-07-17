# Localization Complexity

This repository contains the paper **"Localization Complexity of Hidden-Variable Gibbs Models"** by Samuel Schlesinger and Joshua Grochow.

## Scope

The revived draft focuses on:

- Core definitions: marginal models, *k*-local distributions, *k*-localizations, and localization complexity `L_k(D)`.
- A **face--Gibbs characterization**: the support of a *k*-local distribution is the ground-state set of a degree-*k* pseudo-Boolean Hamiltonian.
- The original **local verification theorem** and two circuit-to-localization upper bounds:
  - `L_k(D) <= G_{k-1}(D)` (generator complexity),
  - `L_k(D) <= C_{k-1}(S)` for flat `D` on support `S`.
- A sharper **quadratic NAND synthesis**:
  `L_2(U_S) <= C_NAND(S)`, with exact generator and unambiguous-verifier
  variants.  Thus a quadratic lower bound for a flat support is already an
  ordinary circuit lower bound (up to the constant choice of gate basis).
- An unconditional converse from a small localization to a nondeterministic circuit for the visible support.
- A support-only lower-bound invariant: the ground-state extension complexity
  `GSE_k(S)`, its facial-cover relaxation, and an exact characterization by a
  filtered real Reed--Muller family of witness slices.  A Shannon count gives
  `GSE_k(S) = Omega_k(2^(n/(k+1)))` for almost every support.
- A sign-sensitive polynomial lower bound
  `ndeg_+(complement(supp(D))) <= k * 2^L_k(D)`, the exact identity
  `L_2(U_even) = ceil(log_2 n)-1`, and matching `log_2(n)+O_k(1)` behavior for
  every fixed `k`.
- A universal balanced-block feature lift
  `L_k(D)=O_k(2^(n/k))` for every distribution and fixed `k>=2`, matched by
  the generic full-support lower bound.
- A boundary-safe algebraic lower-bound method: nonvanishing polynomials in a
  computable marginal ideal certify `L_k(D)>ell`, yielding effectively
  constructible rational hard tables at the optimal scale.
- A zero-temperature transfer from degree-`k` pseudo-Boolean auxiliary
  complexity to full-support localization complexity for arbitrary real
  objectives, using closedness of a finite tropical image; noisy parity and
  explicit superincreasing Gibbs rays are applications.
- A sharp exchangeable theory: every exchangeable law has
  `L_k(D)=O_k(n^(1/k))`, while the closed-form full-support family
  `D_n(x) proportional to exp(-2^(|x|/r_n))`,
  `r_n=2^floor(log_2(n+1))`, has `L_k(D_n)=Theta_k(n^(1/k))` and likelihood
  ratio below `e^3`.
- Deterministic quasipolynomial recognition from dense exact rational tables:
  `L^{O_(k,c)(log^k L)}` for `ell<=cn`, with the sharper
  `L^{O_(k,ell)(log^(k-1) L)}` bound for full-support tables at fixed latent
  budget.  Under ETH, these bounds exclude ordinary polynomial-output
  NP-hardness reductions in the dense-table model.
- A strict adjacent hierarchy: for every `k >= 3`, an explicit flat distribution
  has `L_k = 1` and `L_(k+1) = 0`.
- A full-support theory: an explicit one-hidden-bit adjacent hierarchy for every
  `k >= 2`, the generic lower bound `L_k(D) >= Omega_k(2^(n/k)) - n`, and
  both well-conditioned structured lower bounds and computable optimal-scale
  cold Gibbs rays.
- A reinterpretation of the interior-feasibility counterexample: it refutes local support intersection, but its global zeros are exposed by a quadratic energy.
- A Razborov--Rudich natural-proofs barrier for the support program: any
  efficiently computable, large property certifying superpolynomial
  `GSE_2(S)` is a natural property useful against `P/poly`; largeness is
  automatic at the generic scale, so the barrier prices constructivity alone.
- An extended-formulations comparison: latent class models embed at
  logarithmic interaction order, rectangle and common-information lower
  bounds do not descend to `LC_2` (they do constrain RBMs), and a
  slack-matrix-style factorization theorem for marginal-polytope faces is
  posed as an open problem.
- An interior localization complexity `LC_k^int(D) >= LC_k(D)` for
  full-support laws, with a conjectured strict separation ("boundary lifts
  help"), the localization analogue of rank versus border rank.
- Explicit marginal-ideal certificate degrees: below the halved dimension
  threshold `d_k(n+ell) <= 2^(n-1)`, a certificate of degree `2^(2n+2)`
  exists and is computable by exact rational linear algebra.

`REVIVAL.md` records the commit-by-commit audit, the repaired proof route, novelty boundaries, and formalization gates.
`INVARIANTS.md` develops the exact filtered-slice invariant and further
relaxations beyond the marginal ideal and zero-temperature methods, including
common-leading-form covers and quadratic ground-state zonotope dimension.

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
