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
- `KLocality/MarginalTradeCertificate.lean` supplies a boundary-safe exact
  marginal-polynomial certificate checker, uniform in the locality order,
  homogeneous degree, and finite observed and latent types.  It expands visible
  products over latent fibers and checks equality of the resulting multisets of
  joint feature profiles; face--Gibbs geometry proves soundness even for boundary
  joint laws.
- `KLocality/NonzeroHiddenCertificateExample.lean` instantiates that checker on
  a full-support rational five-bit law.  A sextic certificate rules out every
  quadratic lift with one hidden bit, while six pairwise implication penalties
  construct a lift with two hidden bits, proving the exact identity `LC_2(D)=2`.
- `KLocality/CubicFullSupportExample.lean` gives a weight-only cubic result.
  The four-bit rational law with probability `2/17` at `1111` and `1/17`
  elsewhere has full support.  Its nonzero four-way log interaction rules out
  zero-hidden cubic locality, while a 17-state pairwise lift supplies one
  hidden bit, proving the exact identity `LC_3(D)=1`.
- `KLocality/WitnessProductCertificate.lean` packages a reusable
  sign-definite witness-product obstruction: a finite rational direction that
  annihilates every expanded hidden-slice monomial rules out a localization
  uniformly for every distribution with the certified support.
- `KLocality/UniformParityLowerBound.lean` constructs those certificates
  symbolically for the even-parity family.  For all natural `k`, `n`, and
  `ell`, Lean proves that a `k`-localization with `ell` hidden bits implies
  `n <= k * 2^ell`; hence, for example,
  `3 * 2^ell < n` implies `LC_3(U_even,n) > ell`.
- `KLocality/UniformParityUpperBound.lean` gives the matching symbolic
  Hamming-weight-square lift.  If `n < 2^(ell+1)`, `ell` hidden bits suffice
  already at locality two.  Combining the bounds yields the infinite exact
  cubic family `LC_3(U_even, 3 * 2^ell + 1) = ell + 1` for every `ell >= 1`.
- `KLocality/CubicParityExample.lean` gives an explicit nontrivial cubic
  localization theorem: the uniform distribution on even-parity seven-bit
  strings has exactly `LC_3(D)=2`.  Its lower bound is now an instance of the
  uniform theorem, independently backed by the original finite cube identity;
  its matching upper bound is a concrete quadratic Hamming-weight-square lift.
- `KLocality/ExplicitCubicLowerBound.lean` proves a genuinely weight-sensitive
  cubic lower bound for an explicit full-support rational law on ten bits.  Its
  unnormalized cell weight is `2^(8^v)` at binary state `v < 1023` and `1` at
  state `1023`.  A finite pigeonhole argument produces two degree-8184
  candidate families with identical one-hidden cubic profile histograms;
  uniqueness of binary expansion makes their probability monomial sums
  unequal.  Together with a four-face log-interaction obstruction at zero
  hidden bits, this proves `LC_3(D) > 1`.  The collided families are selected
  noncomputably from the finite counting proof rather than printed as a
  practical certificate.
- `KLocality/UniformExplicitCubicLowerBound.lean` upgrades that mechanism to
  a superlinear family.  For every natural `m`, the explicit rational law
  `D_m` on `4m+24` bits has unnormalized weight `2^(2^v)` at every binary state
  except the final state, which has weight `1`.  Lean proves full support and
  `LC_3(D_m) > 2^m`, equivalently an exponential lower bound
  `2^((n-24)/4)` along this sequence of visible dimensions.  It also proves
  the literal corollary `LC_3(D_m) > (4m+24)^2` for `m>=13`.  A parameterized
  scope encoding gives the cubic feature bound `(q+1)^3`; finite profile
  pigeonholing supplies a boundary-safe trade against every hidden count
  through `2^m`, and binary uniqueness detects every selected trade on the
  same table.  The proof is axiom-clean.  The largest rational entries have
  doubly exponential binary length (and hence still larger numerical value),
  while the certificates have degree `2(2^(4m+24)-1)` and their collisions
  are selected noncomputably.  These parameters are intentionally
  unoptimized: the counting threshold suggests exponent `1/3`, while the
  checked specialization uses `1/4` for simple arithmetic.
- `KLocality/BooleanTilt.lean`, `KLocality/BooleanTiltCircuit.lean`, and
  `KLocality/BooleanTiltTrade.lean` develop the bounded-precision full-support
  law `D_f(x) proportional to 2^(f(x))`.  A size-`s` sequential NAND circuit
  for `f` gives a quadratic localization of `D_f` with exactly `s` hidden gate
  wires, so `LC_3(D_f) <= s`.  On the lower-bound side, every homogeneous
  marginal trade evaluates after cancellation of the common normalizer as an
  equality between finite sums of powers `2^(number of true tuple entries)`.
- `KLocality/LatentPadding.lean`, `KLocality/BinarySubsetTransform.lean`, and
  `KLocality/BooleanTiltExistenceLowerBound.lean` combine that bridge with the
  uniform cubic profile collision.  Lean proves that for every `m` there
  exists a Boolean function on `4m+24` bits whose two-level rational tilt has
  `LC_3(D_f) > 2^m`; hence every sequential NAND circuit computing that
  function has more than `2^m` gates.  The separating function is chosen from
  a noncomputable profile collision via the invertible kernel
  `K(T,C)=2^|T intersect C|`.  This is an exponential existence/counting
  lower bound, not an explicit circuit lower bound.  Producing a uniform
  low-description-complexity separating test remains the central open step.
  The formal sanity theorem
  `booleanTiltCodes_eq_of_nandCircuit_le` also proves that no trade at hidden
  budget `ell` can separate `D_f` when a supplied NAND circuit computes `f`
  with at most `ell` gates.
- `KLocality/BlockParityFiber.lean` through
  `KLocality/BlockParityCertificate.lean` close the structured block-parity
  construction under a canonical finite-search notion of explicitness.  For
  prefix width `q>=64`, put `N=2^q` and use the `2^N` truth-table candidates
  `C_s={(0,a,z): parity(z)=s(a)}`.  Lean proves that all candidates share their
  cubic visible moments, constructs the lexicographically first pair of
  distinct subset histograms that collide after every assignment of `q^2`
  hidden bits, and sets `b_q` to their signed incidence vector.  Thus
  `b_q != 0` and `M_(q,q^2)b_q=0`.  Integer injectivity of the `256` agreement
  tensor then selects the first `t_q` satisfying
  `sum_s b_q(s) 256^(N-d_H(s,t_q)) != 0`.  The collision compiles to a
  boundary-safe `MarginalTradeCertificate`, yielding a full-support rational
  two-level law on `q+5` visible variables with `LC_3(D_q)>q^2`.
  The theorem `blockParityCanonicalDistribution_eventually_gt_linear`
  packages this as domination of every fixed linear function of the visible
  dimension.

  This is an exhaustive-search/diagonalization family, not an efficiently
  explicit circuit lower bound: neither `t_q` nor the colliding subsets have
  a polynomial-time, small-circuit, or low-description construction.  The
  remaining circuit frontier is to replace the first-witness searches by a
  uniformly efficient description while retaining the same separation.
  `research/block-parity-fiber.md` records the structural Fourier route and
  its current limitations.

The checked recognizer theorem now includes the paper's hardwired-input-constant
accounting.  A translation from cslib's permissive raw DAG representation, NAND
universality/existence inside Lean, and the generator theorem `LC_2 <= G_NAND`
remain to be done.  The older generic fan-in circuit bounds in
`CircuitConnections.lean` still use explicit bridge hypotheses; the concrete NAND
theorems are deliberately separate.
The face--Gibbs equivalence, universal support-cardinality construction,
selector closure, the finite marginal-trade certificate checker, and one
explicit full-support cubic family with unbounded `LC_3` are now
Lean-formalized.
The universal balanced block lift, the general elimination
and dimension theorems that guarantee marginal certificates, recognition
algorithms, zero-temperature transfer, exchangeable bounds, and circuit
converses remain open in Lean.  The explicit cubic family is a genuine
asymptotic lower bound, but it does not formalize the manuscript's generic
almost-everywhere theorem or its sharp `2^(n/3)` cubic scale.

The cslib dependency is pinned to reachable commit `8961914`, which uses the same Lean `v4.29.0-rc2` toolchain and contains the circuit modules imported here.  A clean dependency refresh followed by `lake build` succeeds at this revision.

Build with:

```bash
lake build
```
