# Paper-to-Lean theorem manifest

This file is the coverage contract between `main.tex` and the `KLocality`
library.  Every theorem-like environment in the manuscript appears exactly
once below.  A result is **checked** only when the full paper-facing statement
is proved without `sorry`, `admit`, or a project-local axiom.  A narrower
theorem, a derivation from an unconstructed bridge hypothesis, or a finite
validation is **partial**, not checked.

The manifest is intentionally label-driven: LaTeX labels are stable cross-file
identifiers, while prose names and Lean implementation names may evolve.

## Status vocabulary

- **checked** — the full manuscript statement has a kernel-checked Lean
  counterpart at the stated model boundary.
- **partial** — reusable Lean ingredients exist, but at least one conclusion,
  convention, construction, or quantified case from the manuscript is absent.
- **open** — no Lean counterpart of the full statement exists yet.
- **conjecture** — explicitly unproved in both the manuscript and Lean; it must
  not be promoted to a theorem merely to make the manifest green.

## Main text and appendices

| LaTeX label | Manuscript result | Status | Lean counterpart / remaining boundary |
|---|---|---:|---|
| `prop:existence` | Universal existence | checked | `hasTwoLocalization_supportCard`, `hasKLocalization_supportCard`, `localizationComplexity_le_supportCard`, and `localizationComplexity_le_two_le_supportCard` in `KLocality.UniversalExistence`. The paper-facing `localizationComplexity`/`LC_k` API is total and carries no proof argument. |
| `lem:canonical` | Canonical constraints | checked | `canonicalFeature`, `distribution_eq_of_monomialMoments_eq`, `sameFeatureMomentsUpTo_iff_sameMarginalsUpTo`, and `isKLocalMarginal_iff_maxEntropy_sameFeatureMoments` in `KLocality.Canonical`. |
| `lem:max-support` | Maximal feasible support | checked | `support_eq_iUnion_of_isMaxEntropyAmong` in `KLocality.MaxSupport` proves the stronger convex-family form; `support_eq_iUnion_sameFeatureMoments_of_isKLocal` specializes it to the paper's canonical affine fiber. |
| `thm:face-gibbs` | Face--Gibbs characterization | checked | `isKLocalMarginal_iff_marginalPolytopeFaceGibbs` in `KLocality.FaceGibbsCharacterization` states the literal exposed-face preimage and normalized Gibbs formula. Its proof factors through the checked two-sided entropy derivative and dual-span argument in `KLocality.GibbsOptimality` and the certificate/exposed-face equivalence in `KLocality.MarginalPolytope`. |
| `cor:ground-state` | Ground-state support | checked | `exists_nonnegative_featurePolynomial_zeroSet_of_isKLocalMarginal` in `KLocality.FaceGibbsCharacterization` gives the degree-at-most-`k` multilinear polynomial, pointwise nonnegativity, and exact support zero set. |
| `prop:gibbs-reduction-calculus` | Gibbs-reduction calculus | partial | `GibbsReductionWitness.identity`, `gibbsReductionCost_comp_le`, and `gibbsReductionCost_unit_eq` in `KLocality.GibbsReduction`, `KLocality.GibbsReductionComposition`, and `KLocality.GibbsReductionAbsolute` check the identity, composition, and absolute clauses. The tensor clause is still absent. |
| `cor:gibbs-reduction-compilation` | Compiling a source distribution | checked | `observed_add_localizationComplexity_le_compilation` proves the displayed minimum-cost inequality, and `localizationComplexity_le_of_hasGibbsReduction` proves its disjoint-output/workspace consequence in `KLocality.GibbsReductionAbsolute`. |
| `prop:sparse-no-lift` | Sparse distributions need no lift | open | Requires a formal proof of the relevant marginal-polytope neighborliness result. |
| `thm:universal-lift` | Universal block-feature lift | checked | `localizationComplexity_le_min_supportCard_balancedLiftBound` and `localizationComplexity_isBigO_exp` in `KLocality.BalancedUniversalLift` prove the exact balanced count and the real-exponent asymptotic for every distribution and `k>=2`, including empty blocks and boundary tables. `KLocality.BlockFeatureLift` constructs the graph lift and proves that its order-`k` moments uniquely determine the lifted probability law. |
| `thm:algebraic-certificate` | Marginal-ideal certificate | checked | `projectiveVariety_eq_zariskiClosure`, `projectiveParameterImage_eq_unscaled`, `projectiveDistribution_mem_of_localizationComplexity_le`, and `localizationComplexity_gt_of_homogeneous_polynomial` in `KLocality.MarginalVarietyProjective` give the literal complex projective variety and boundary-safe containment/certificate implication. `projectiveDimension_le` proves `dim <= d_k(n+ell)-1` using the coordinate-ring transcendence degree. `exists_homogeneous_integer_certificate` supplies a nonzero integer form under `d_k(n+ell)<2^n`. `ideal_eq_elimination` and `ideal_finitely_generated` identify the rational elimination ideal. The executable `checkIdentity`, proved sound and complete by `checkIdentity_iff_elimination`, decides membership for every rational polynomial expression; `RationalPolynomialExpression.value_surjective` covers every rational polynomial. This is an exact membership procedure, not a Groebner-basis generator or a running-time bound. The separate degree, genericity, and hard-table results below retain their own statuses. |
| `prop:certificate-degree` | Explicit certificate degree | open | The general substitution map and existence of homogeneous integer identities are now checked. The explicit degree bound still requires the exact dimensions of the homogeneous source and target spaces and the displayed binomial inequality. |
| `cor:effective-tables` | Effective rational hard tables and Gibbs rays | partial | `KLocality.UniformExplicitCubicLowerBound` checks a superlinear parameterized base-coded construction: for every `m`, a closed-form positive rational table on `4m+24` bits has `LC_3(D_m)>2^m`. The proof derives collisions by finite pigeonhole choice and gives degree `2(2^(4m+24)-1)` certificates rather than computing their terms. The largest probability numerators have doubly exponential binary length (and numerical value one exponential level larger), so this is mathematical explicitness rather than a polynomial-bit table generator. The all-`k` marginal ideal is now formalized separately; the sharp `2^(n/k)` hard-table construction, practical bit complexity, and Gibbs-ray statement remain. |
| `thm:generic-positive` | Generic full-support lower bound | open | The marginal-ideal dimension theorem and integer-certificate existence are now checked. A measure-zero theorem for proper real algebraic sets and its probability-simplex specialization remain. |
| `cor:worst-case` | Worst-case localization complexity | partial | `localizationComplexity_isBigO_exp` checks the universal upper bound. The matching generic lower bound remains open in Lean. |
| `conj:interior` | Boundary lifts help | conjecture | Must remain explicitly unproved unless new mathematics resolves it. |
| `lem:closed-tropical-image` | Closed finite tropical image | open | Requires a checked finite polyhedral-cone image/selector argument. |
| `thm:zero-temperature` | Zero-temperature transfer | open | Depends on face--Gibbs, the tropical-image lemma, and face penalization. |
| `lem:facial-conditioning` | Facial conditioning | checked | `localizationComplexity_filter_le` in `KLocality.FacialConditioning` proves the same-coordinate inequality. `localizationComplexity_facialConditionalPullback_le` in `KLocality.FacialConditioningPullback` proves the full duplication/fixing clause through `CoordinateParametrization`; the joint pullback preserves the latent type and commutes exactly with observed marginalization. |
| `thm:exchangeable-window` | Exchangeable scale and a well-conditioned analytic family | open | Requires the radial lookup, conditioning, marginal ideals, Eisenstein, and Lindemann--Weierstrass. |
| `thm:etr-recognition` | Exact rational-table recognition | open | The existential-real syntax, direct formula, correctness, and encoding size are not formalized. |
| `lem:face-enumeration` | Enumeration and recovery of facial supports | open | Requires finite polytope face bases and exact LP recovery. |
| `lem:etr-bit-bound` | Bit complexity of existential real feasibility | open | Requires an explicit bit-complexity model and the cited real-feasibility bound. |
| `thm:qp-recognition` | Quasipolynomial dense-table recognition | open | Depends on face enumeration and the bit-complexity lemma. |
| `thm:full-support-recognition` | Few-variable full-support recognition | open | Algebraic identities have finite validation only; the formula and running-time theorem are absent. |
| `cor:recognition-eth` | ETH barrier to dense-table hardness | open | Requires formal languages, reductions, dense input length, ETH, and the preceding algorithms. |
| `prop:zero-latent-p` | The zero-latent case is in P | open | Requires the dense rational-table algorithm and formal polynomial-time accounting. |
| `thm:local-verification` | Local verification | checked | `localVerificationMaximumEntropyMarginalsOnFinset` and `localVerificationIsKLocalMarginalOnFinset` in `KLocality.Core`. |
| `thm:upper-bounds` | Circuit traces | partial | `KLocality.CircuitConnections` derives the generic bounds from explicit but unconstructed bridge hypotheses. Independently, `BooleanTiltCircuit` checks an exact weighted trace theorem: a size-`s` sequential NAND circuit computing `f` gives a 2-localization, hence a 3-localization, of `D_f(x) proportional to 2^(f(x))` with exactly `s` hidden gate wires. |
| `thm:nand-synthesis` | Quadratic NAND synthesis | partial | The constants-aware uniform-support recognizer inequality and the constant-free weighted Boolean-tilt trace inequality are checked with exact gate-bit accounting. Generator and (un)ambiguous-verifier conclusions remain. |
| `prop:natural-proofs` | Natural-proofs status of the support program | open | Requires formal natural-property definitions and the conditional pseudorandom-function implication. |
| `lem:exact-threshold` | Exact-threshold compilation | open | Requires exact integerization and a checked fan-in-two adder/gate count. |
| `thm:converse` | Localization to nondeterministic circuits | open | Depends on exposing energies and exact-threshold compilation. |
| `thm:deterministic-converse` | Deterministic witness expansion | open | Depends on exposing energies, slice compilation, and circuit-size accounting. |
| `cor:lower-bound` | Support-complexity lower bound | open | Depends on the nondeterministic converse and an explicit inversion bound. |
| `prop:facial-cover` | Facial-cover lower bound | partial | `GroundStateExtension`, `groundStateExtensionComplexity`, and `groundStateExtensionComplexity_le_localizationComplexity` in `KLocality.SelectorLeakage` and `KLocality.GroundStateExtension` check `LC_k(D) >= GSE_k(supp D)`. The facial-cover definition, logarithmic bound, and singleton-cover cap remain. |
| `prop:filtered-slices` | Filtered slice criterion | open | Requires canonical pseudo-Boolean polynomials and real Reed--Muller evaluation spaces. |
| `thm:selector-closure` | Selector facial-closure duality | checked | `momentFacialClosure_isFacial` and `momentFacialClosure_minimal` in `KLocality.FacialClosure` identify the moment-fiber support union with the smallest facial support. `groundStateExtensionComplexity_le_iff_exists_selector_doesNotLeak`, `mem_selectorFacialClosure_iff_exists_sameMoments`, and `groundStateExtensionComplexity_gt_iff_every_selector_leaks` in `KLocality.SelectorLeakage` and `KLocality.GroundStateExtension` prove all three displayed equivalences, including exact latent-bit padding. |
| `prop:selector-lp` | Selector LP certificates | partial | `RationalSelectorDualCertificate` and `rationalSelectorDualCertificates_obstruct_localization` in `KLocality.SelectorTrade` check the displayed rational dual equations and compile one certificate per selector into genuine same-`k`-marginal leakage. The primal LP equivalence and theorem deriving a normalized rational dual certificate from every infeasible primal instance remain. |
| `lem:rank-obstruction` | Unfiltered rank loses the support | open | The injective binary code and three-dimensional coefficient-span construction are absent. |
| `thm:random-support` | Counting bound for uniform supports | open | Requires face counting and formal asymptotic probability estimates. |
| `cor:random-middle-layer` | Random thinning of one Hamming layer | open | Depends on the counting theorem and central-binomial asymptotics. |
| `thm:witness-product` | Nonnegative witness-product bound | partial | `WitnessProductCertificate` and `WitnessProductCertificate.obstructs_localization` in `KLocality.WitnessProductCertificate` give a generic finite rational version for a fixed finite hidden type and arbitrary visible distribution with the certified support. `evenParityWitnessProductCertificate` instantiates it uniformly. The abstract `ndeg_+` API, its minimization theorem, and the facial-cover inequality remain absent. |
| `prop:parity` | Parity localization | partial | `evenParity_size_le_of_hasKLocalization` and `evenParity_localizationComplexity_gt` in `KLocality.UniformParityLowerBound` prove the manuscript's lower bound uniformly: every `k`-localization with `ell` hidden bits satisfies `n <= k * 2^ell`. `evenParity_has_twoLocalization_of_lt_two_pow` in `KLocality.UniformParityUpperBound` constructs a symbolic quadratic Hamming-weight lift whenever `n < 2^(ell+1)`. Their overlap gives the infinite exact family `evenParity_cubic_exact_family`: `LC_3(U_even, 3*2^ell+1)=ell+1` for `ell>=1`. The proof is parameterized rather than bounded enumeration. The manuscript's improved upper bound using `floor(k/2)` weight classes and its exact general quadratic formula remain absent. |
| `prop:hierarchy` | Strict adjacent hierarchy | open | Requires the witness-product bound and a checked weighted one-bit lift. |
| `prop:positive-no-latent` | No-latent characterization | checked | `localizationComplexity_eq_zero_iff_fullSupport_normalizedGibbs` in `KLocality.NoLatent` proves the exact normalized degree-`k` Gibbs characterization; `isKLocalMarginal_iff_fullSupport_logDensity` gives the equivalent log-density formulation, and `hasKLocalization_zero_iff_isKLocalMarginal` checks the zero-latent coordinate identification. |
| `prop:positive-hierarchy` | Full-support adjacent hierarchy | partial | `boostedFourDistribution_localizationComplexity_eq_one` in `KLocality.CubicFullSupportExample` proves the concrete rational cubic instance `LC_3(D)=1` for the full-support four-bit law with weights `2/17` at `1111` and `1/17` elsewhere; the matching lift is even quadratic but lies on a proper support face. The manuscript's uniform theorem for every `k>=2` and `n>=k+1`, including its strictly positive one-hidden lift, still requires the soft-plus coefficient argument and tensoring with uniform coordinates. |
| `cor:noisy-parity` | Noisy parity | open | Depends on exact quadratization complexity and zero-temperature transfer. |
| `cor:superincreasing` | Superincreasing Gibbs rays | open | Requires the determinant/root-bound argument and zero-temperature transfer. |
| `lem:subcube-degree` | Boolean subcube degree test | open | Canonical multilinear Boolean expansion and iterated finite differences are not yet packaged. |

## Additional checked research corollary

`KLocality.BooleanTiltExistenceLowerBound` proves that for every `m`
there exists a Boolean function on `4m+24` bits whose full-support,
two-level rational tilt `D_f` satisfies `LC_3(D_f) > 2^m`.  Therefore
every sequential NAND circuit computing the selected function has more than
`2^m` gates.  This uses the integer-invertible binary subset transform
`K(T,C)=2^|T intersect C|` to choose a test separating the noncomputably
selected profile collision.  It is deliberately classified as an existential
counting lower bound, not an explicit circuit lower bound or a completed
counterpart of the manuscript's circuit-converse results.

`KLocality.BlockParityCertificate` gives a more structured canonical
diagonalization.  For every `q>=64`, it defines by lexicographically first
finite witnesses a truth table `t_q` and a nonzero signed incidence vector
`b_q` such that `M_(q,q^2)b_q=0` but
`sum_s b_q(s)256^(2^q-d_H(s,t_q)) != 0`.  The checked compilation produces a
full-support rational two-level law on a visible type of cardinality `q+5`
with `LC_3(D_q)>q^2`.  This is a uniform finite-search definition, not an
efficiently explicit circuit family: no useful running-time, description-size,
or circuit-size upper bound for computing `t_q` is claimed.  The declaration
`blockParityCanonicalDistribution_eventually_gt_linear` states the resulting
superlinear asymptotic directly.

## Completion gates

The companion is complete only when all rows other than `conj:interior` are
**checked**, every row names its Lean declaration, and all of the following
commands succeed on a clean worktree:

```bash
lake build -KwarningAsError=true
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' KLocality Main.lean KLocality.lean
```

The placeholder search must be empty.  The final audit must also compare this
table against the theorem-like environments in the current `main.tex`, so a
new manuscript result cannot silently fall outside the Lean coverage claim.
