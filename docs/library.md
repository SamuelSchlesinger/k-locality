# Lean library guide

[`KLocality.lean`](../KLocality.lean) imports the complete library. For the
paper's individual statements and remaining hypotheses, use the
[theorem manifest](../FORMALIZATION.md). This guide organizes the implementation
by mathematical role.

## Definitions and conventions

[`Core.lean`](../KLocality/Core.lean) defines scoped marginal constraints,
maximum-entropy locality, marginal models, `HasKLocalization`, and
`localizationComplexity`. Variables are finite types; visible and hidden
coordinates are represented by their disjoint sum. `BitVec n` is the local
Boolean-assignment notation.

`localizationComplexity` is a total natural-valued function with a fallback of
zero when no localization exists. [`UniversalExistence.lean`](../KLocality/UniversalExistence.lean)
proves existence for every finite Boolean law when `k >= 2`, so the fallback
is unreachable throughout the paper's regime. Do not interpret the fallback
as a localization theorem for `k = 0` or `k = 1`.

The dependencies include Mathlib through the pinned `cslib` fork. The generic
circuit definitions use `cslib`; the concrete NAND constructions use the
repository's typed sequential circuits. Hardwired constants in
`NANDCircuitWithConstants` are syntax and contribute no assignment coordinate.

## Main theorem chains

| Topic | Modules and entry points |
|---|---|
| Canonical moments | `Canonical`, `FeaturePolynomial`, `MaxSupport`: equivalence of monomial moments and scoped marginals; maximal feasible support |
| Face geometry and entropy | `FaceGibbs`, `FiniteSeparation`, `FacialSupport`, `GibbsOptimality`, `MarginalPolytope`, `FaceGibbsCharacterization`: `isKLocalMarginal_iff_marginalPolytopeFaceGibbs` |
| Universal lifts | `UniversalExistence`, `BlockFeatureLift`, `BalancedUniversalLift`: `localizationComplexity_le_min_supportCard_balancedLiftBound`, `localizationComplexity_isBigO_exp` |
| Marginal varieties | `MarginalVariety`, `MarginalVarietyDimension`, `MarginalVarietyElimination`, `MarginalVarietyProjective`: boundary-safe projective containment, `projectiveDimension_le`, `exists_homogeneous_integer_certificate` |
| Executable identities | `MarginalIdentityDecision`: `checkIdentity_iff_elimination` proves exact rational-expression membership; it does not implement a Groebner-basis generator or a complexity bound |
| Conditioning and reductions | `Reindex`, `NoLatent`, `FeatureEmbedding`, `CoordinateSubstitution`, `CoordinatePullback`, `FacialConditioning`, `FacialConditioningPullback`, `RelativeGibbs`, `GibbsReduction`, `GibbsReductionComposition`, `GibbsReductionAbsolute` |
| Ground states and circuits | `GroundState`, `GroundStateProjection`, `GroundStateExtension`, `QuadraticNAND`, `NANDCircuit`, `NANDCircuitLocalization`, `NANDCircuitWithConstants`, `NANDCircuitWithConstantsLocalization`, `Tactic` |
| Selector obstructions | `FacialClosure`, `SelectorLeakage`, `SelectorTrade`, `SelectorTradeExample`: facial closure, exact selector duality, and soundness of supplied rational dual certificates |

The generic fan-in statements in
[`CircuitConnections.lean`](../KLocality/CircuitConnections.lean) assume
`GeneratorToLocalizationBridge` or `FlatRecognizerToLocalizationBridge`.
The concrete NAND recognizer theorem constructs its lift, but takes an
explicit recognizer-existence witness. NAND universality, generator synthesis,
and transport from the permissive raw DAG representation are still missing.
Gibbs-reduction tensoring is also absent.

## Lower bounds and examples

| Family or method | Modules | Checked conclusion and limit |
|---|---|---|
| Log interactions | `LogInteractionCertificate`, `FullSupportCertificateExample`, `UniformBoostedPoint`, `CubicFullSupportExample` | Concrete full-support nonlocal laws; the four-bit boosted law has `LC_3 = 1` |
| Marginal trades | `MarginalTradeCertificate`, `NonzeroHiddenCertificateExample` | Uniform boundary-safe certificate soundness; an exact five-bit example with `LC_2 = 2` |
| Parity | `WitnessProductCertificate`, `UniformParityLowerBound`, `UniformParityUpperBound`, `CubicParityExample` | Every lift satisfies `n <= k * 2^ell`; symbolic quadratic upper lifts and an infinite exact cubic subfamily. The paper's full parity proposition is only partially formalized |
| Base-coded rational laws | `ExplicitCubicLowerBound`, `UniformExplicitCubicLowerBound` | `LC_3(D_m) > 2^m` on `4m+24` bits; doubly exponential entry bit lengths and noncomputably selected collisions |
| Boolean tilts | `BooleanTilt`, `QuadraticFeaturePolynomial`, `BooleanTiltCircuit`, `BooleanTiltTrade`, `LatentPadding`, `BinarySubsetTransform`, `BooleanTiltExistenceLowerBound` | NAND upper bounds for `D_f` proportional to `2^(f(x))` and exponential existence/counting lower bounds |
| Block parity | `BinaryAgreementTransform`, `BlockParityFiber`, `BlockParityMatrix`, `BlockParityCounting`, `BlockParityCanonicalTrade`, `BlockParityAgreementWitness`, `BlockParityCertificate` | A canonical finite-search two-level law on `q+5` bits with `LC_3 > q^2` for `q >= 64`; efficient explicitness remains open |

The [companion note](../notes/explicit-lower-bounds.tex) explains the encoding
and explicitness boundaries. The [block-parity note](../research/block-parity-fiber.md)
develops the Fourier route and reports the scope of exploratory computations.

[`InteriorFeasibilityCounterexample.lean`](../KLocality/InteriorFeasibilityCounterexample.lean)
is a supporting example for the paper's boundary discussion. Its quadratic
energy demonstrates that positive pairwise marginal cells can force zero
joint cells. It remains checked alongside the library.

## Trust checks

`make check-lean` builds with warnings as errors, audits the axiom dependencies
of every declaration originating in a `KLocality` module, and executes the
small rational-identity checks in
[`research/check_universal_marginal.lean`](../research/check_universal_marginal.lean).
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the audit.
This checks the proof dependencies; the manifest separately records whether
the statement matches the manuscript.
