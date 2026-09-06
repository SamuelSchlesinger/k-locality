# Verification and evidence ledger

This file records what kind of evidence supports each major claim in
`main.tex`.  It deliberately distinguishes a manuscript proof from a Lean
proof, a finite computation, and a literature check.  None of those categories
silently substitutes for another.

Status reflected here: 2026-09-05.  The Lean toolchain is
`leanprover/lean4:v4.29.0-rc2`; `cslib` is pinned to
`89619147bf2ef78b8f04c66cbb41546d4757554e`.

## Evidence vocabulary

- **Manuscript proof:** a mathematical argument appears in `main.tex`.  A
  successful PDF build checks typesetting and cross-references, not truth.
- **Lean checked:** Lean verifies the stated theorem in the formal model and
  at the cited API boundary.  This does not automatically identify that model
  with every convention used elsewhere in the manuscript.
- **Finite validation:** a script exhaustively or exactly checks specified
  finite instances or algebraic identities.  This is regression evidence, not
  an asymptotic proof.
- **Primary-source audit:** the cited statement, theorem number, and transfer
  direction were checked against an author or journal source.  This is not a
  certification of publication priority.
- **Open:** a construction, bridge, or research question is explicitly not
  proved.

## Major-claim ledger

| Manuscript result | Evidence in this repository | Current boundary |
|---|---|---|
| Definitions of marginal models, scoped marginal locality, localization complexity, and universal existence | Lean checked in `KLocality/Core.lean` and `KLocality/UniversalExistence.lean`; manuscript definitions and Proposition `prop:existence` in Section 2 | Universal existence and the exact support-cardinality bound are checked; the total Lean `LC_k` function has the same proof-free paper-facing interface |
| Canonical monomial features and entropy fibers | Lean checked in `KLocality/Canonical.lean`; Lemma `lem:canonical` | Boolean Möbius inversion, equivalence with all order-at-most-`k` marginals, and the exact maximum-entropy characterization are checked |
| Maximal feasible support | Lean checked in `KLocality/MaxSupport.lean`; Lemma `lem:max-support` | The convex-family theorem and its canonical affine feature-fiber specialization are checked, using an explicit entropy-improving mixture scale |
| Local verification and ground-state support | Lean checked in `KLocality/Core.lean`, `KLocality/GroundState.lean`, and `KLocality/FaceGibbsCharacterization.lean` | Covers both local verification/uniform ground-state constructions and the converse exposing polynomial for every local law |
| Face--Gibbs characterization | Lean checked in `KLocality/FaceGibbsCharacterization.lean`, with analytic and finite-dual infrastructure in `KLocality/GibbsOptimality.lean`, `KLocality/FacialSupport.lean`, and `KLocality/MarginalPolytope.lean` | The exact finite Boolean statement is checked: exposed marginal-polytope face, exact support preimage, normalized Gibbs formula, and both implications |
| Full-support no-latent characterization | Lean checked in `KLocality/NoLatent.lean` | Zero latent coordinates are transported through an explicit assignment equivalence; `LC_k(D)=0`, degree-at-most-`k` log density, and the normalized full-cube Gibbs formula are proved equivalent for `k ≥ 2` |
| Facial conditioning and duplication/fixing pullback | Lean checked in `KLocality/FacialConditioning.lean`, `KLocality/CoordinateSubstitution.lean`, `KLocality/CoordinatePullback.lean`, and `KLocality/FacialConditioningPullback.lean` | Filtering on a positive facial event preserves locality with the same latent type; a bijective Boolean-cube parametrization induced by duplicated variables and constants then preserves degree, support weights, and the observed marginal, yielding the exact localization-complexity inequality |
| Relative Gibbs reductions, composition, tensoring, and recovery of `n + L_k(D)` | Lean checked for the definition, identity, additive composition, absolute equality, and compilation corollary in `KLocality/RelativeGibbs.lean`, `KLocality/GibbsReduction.lean`, `KLocality/GibbsReductionComposition.lean`, and `KLocality/GibbsReductionAbsolute.lean`; manuscript proof for tensoring | The tensor clause is not yet Lean formalized; this remains a nonuniform projective weight reduction, not sample-preserving conversion or an efficient reduction between succinct inputs |
| Supporting example: positive marginals force boundary support | Lean checked in `KLocality/InteriorFeasibilityCounterexample.lean` | The compact manuscript example `ex:positive-marginals-boundary` illustrates a proper exposed support face. The longer development writeup is archived under `research/archive/` |
| Universal existence with at most `|supp(D)|` hidden bits | Lean checked in `KLocality/UniversalExistence.lean` | The construction uses one support-index bit per positive-mass visible point, a quadratic exact-one/consistency energy, and singleton hidden marginals to preserve arbitrary weights |
| Universal balanced block-feature lift | Lean checked in `KLocality/BlockFeatureLift.lean` and `KLocality/BalancedUniversalLift.lean`; independent finite validation by `validate_block_lift.py` | For all `n`, all `k>=2`, and every probability table, Lean proves `LC_k(D) <= min(supportCard(D), b_k(n))` and the uniform `O_k(2^(n/k))` corollary. The lift preserves the whole table; nonnegative quadratic penalties and packed visible monomials make its moment fiber a singleton. Empty blocks and boundary laws are included. |
| General marginal variety and integer certificates | Lean checked in `KLocality/MarginalVariety.lean`, `KLocality/MarginalVarietyDimension.lean`, `KLocality/MarginalVarietyElimination.lean`, `KLocality/MarginalVarietyProjective.lean`, and `KLocality/MarginalIdentityDecision.lean` | The complex projective Zariski closure, boundary-safe containment, homogeneous certificate implication, exact rational elimination ideal, finite generation, coordinate-ring dimension bound, and nonzero homogeneous integer identities below the parameter-count threshold are checked. Projective dimension uses homogeneous coordinate-ring transcendence degree minus one. A compiled rational-expression checker has a uniform soundness/completeness proof and decides the elimination ideal; no Groebner-basis generator or running-time bound is claimed. |
| Generic full-support lower bound and worst-case `Theta_k(2^(n/k))` scale | Manuscript proofs and primary-source audit; Lean-checked universal upper bound | The measure-zero argument on the probability simplex, hence the generic lower bound and matching worst-case scale, remain unformalized. The general explicit certificate-degree bound also remains separate. |
| Explicit weight-sensitive marginal certificates | Lean checked in `KLocality/MarginalTradeCertificate.lean`, `KLocality/NonzeroHiddenCertificateExample.lean`, `KLocality/ExplicitCubicLowerBound.lean`, and `KLocality/UniformExplicitCubicLowerBound.lean` | Lean proves `LC_2(D)=2` for the five-bit law `(1+1_123)(1+1_345)/41`, `LC_3(D)>1` for the explicit ten-bit law, and `LC_3(D_m)>2^m` for a positive rational law on `4m+24` bits; for `m>=13`, it also proves `LC_3(D_m)>(4m+24)^2`. The uniform proof selects finite profile collisions noncomputably and has degree `2(2^(4m+24)-1)` certificates. The largest rational entries have doubly exponential binary length. The sharp cubic scale and practical extraction are not implied by these constructions. |
| Full-support adjacent hierarchy | Lean checked for the boosted-point family in `KLocality/UniformBoostedPoint.lean`, with a separate four-bit instance in `KLocality/CubicFullSupportExample.lean`; manuscript proof of Proposition `prop:positive-hierarchy` | The rational boosted-point law has `LC_k(D)=1` whenever `2<=k<n`. Taking `n=k+1` gives an adjacent separation for every `k>=2`. These checked one-hidden lifts lie on proper support faces; the manuscript's strictly positive lift and its separation in every larger ambient dimension remain unformalized. |
| Effective rational hard tables and explicit certificate-degree bound | Manuscript proof | No end-to-end generated eliminant is checked for the asymptotic construction |
| Zero-temperature transfer | Manuscript proof using the closed finite selector-max image | Not Lean formalized; no finite script can establish the arbitrary-face limiting theorem |
| Exchangeable upper bound and explicit well-conditioned lower-bound family | Manuscript proof; exact finite validation by `validate_eisenstein_radial.py`; targeted primary-source audit | The script checks the encoding and algebraic preconditions on a finite range; Lindemann--Weierstrass and the marginal-ideal implication remain manuscript mathematics |
| Direct existential-real encoding | Manuscript proof | No standalone decision-procedure implementation |
| Quasipolynomial dense-table recognition | Manuscript proof from face enumeration plus a standard existential-real decision bound | No end-to-end recognizer implementation; complexity accounting is not Lean formalized |
| Few-variable full-support recognition | Manuscript proof; exact identities checked by `validate_full_support_recognition_reduction.py` | The script checks energy, minimizer, marginal-factorization, and conditional-odds identities, not the real-algebraic running-time theorem |
| Quadratic NAND recognizer synthesis with hardwired constants and exact gate-bit accounting | Lean checked through `KLocality/NANDCircuitWithConstantsLocalization.lean` | The generator half, NAND universality/existence, and transport from permissive raw `cslib` DAGs remain open in Lean |
| Full-support Boolean tilts and NAND lower-bound transfer | Lean checked in `KLocality/BooleanTilt.lean`, `KLocality/QuadraticFeaturePolynomial.lean`, `KLocality/BooleanTiltCircuit.lean`, `KLocality/BooleanTiltTrade.lean`, `KLocality/LatentPadding.lean`, `KLocality/BinarySubsetTransform.lean`, and `KLocality/BooleanTiltExistenceLowerBound.lean` | For `D_f(x) proportional to 2^(f(x))`, Lean checks `LC_3(D_f) <= s` for every supplied size-`s` sequential NAND circuit computing `f`. It also checks that for every `m` some `f` on `4m+24` bits has `LC_3(D_f)>2^m`, and hence every such NAND circuit has more than `2^m` gates. Conversely, `booleanTiltCodes_eq_of_nandCircuit_le` says every trade at budget `ell` vanishes on `D_f` whenever a supplied circuit for `f` has at most `ell` gates. The hard function is selected noncomputably from a profile collision by binary interpolation, so this is an existence/counting lower bound, not an explicit circuit lower bound. Universality of the sequential NAND API is still not checked. |
| Structured block-parity trade and canonical bounded-precision lower bound | Lean checked in `KLocality/BlockParityFiber.lean`, `KLocality/BinaryAgreementTransform.lean`, `KLocality/BlockParityMatrix.lean`, `KLocality/BlockParityCounting.lean`, `KLocality/BlockParityCanonicalTrade.lean`, `KLocality/BlockParityAgreementWitness.lean`, and `KLocality/BlockParityCertificate.lean`; executable discovery checks in `research/analyze_block_parity_fiber.py` | For every `q>=64`, Lean constructs by finite lexicographic search a nonzero signed incidence vector `b_q` with `M_(q,q^2)b_q=0`, then uses integer injectivity of the `256` agreement tensor to choose the first truth table `t_q` with `sum_s b_q(s)256^(2^q-d_H(s,t_q)) != 0`. The histogram collision compiles to a boundary-safe marginal-trade certificate, and the resulting full-support two-level rational law on a visible type of cardinality `q+5` satisfies `LC_3(D_q)>q^2`. The construction is effective only in the finite exhaustive-search sense; no polynomial-time, low-description, or small-circuit construction of `b_q` or `t_q` is claimed. The finite script still serves only as small-instance discovery evidence. |
| Generic fan-in generator and flat-recognizer bounds in `CircuitConnections.lean` | Lean derivations from `GeneratorToLocalizationBridge` and `FlatRecognizerToLocalizationBridge` | The bridge builders are explicit hypotheses, not constructed Lean proofs |
| Manuscript NAND generator and unambiguous-verifier variants | Manuscript proof | Not Lean formalized |
| Localization-to-circuit converse and natural-proofs proposition | Manuscript proofs; primary-source audit for exact-threshold integerization and Razborov--Rudich | Not Lean formalized |
| Parity localization and sign-definite-degree lower bound | Generic certificate soundness Lean checked in `KLocality/WitnessProductCertificate.lean`; uniform lower and upper bounds Lean checked in `KLocality/UniformParityLowerBound.lean` and `KLocality/UniformParityUpperBound.lean`; concrete cubic instance Lean checked in `KLocality/CubicParityExample.lean`; source-level check of the Boros--Crama--Rodríguez-Heck formulas | Lean proves symbolically that every `k`-localization of `U_even,n` with `ell` hidden bits satisfies `n <= k * 2^ell`. It also constructs a quadratic `ell`-hidden lift whenever `n < 2^(ell+1)`, with a proved injective binary half-weight encoding and unique uniform extension. Consequently `LC_3(U_even,3*2^ell+1)=ell+1` for every `ell>=1`; the earlier `LC_3(U_even,7)=2` result is the first case. The manuscript's stronger `floor(k/2)` upper construction and exact general quadratic formula remain manuscript-only. |
| Selector facial-closure duality, rational trade certificates, and block-layer examples | Lean checked in `KLocality/FacialClosure.lean`, `KLocality/SelectorLeakage.lean`, `KLocality/SelectorTrade.lean`, and `KLocality/GroundStateExtension.lean`; a three-cube alternating trade is checked in `KLocality/SelectorTradeExample.lean`; finite block-layer validation by `validate_selector_block_layers.py` | The full selector duality and compilation of a supplied normalized rational dual table into same-marginal leakage are checked. The general rational Farkas alternative, filtered-slice theorem, and unrestricted block-layer direct-sum conjecture remain open |
| Interior-versus-closure separation | Open conjecture | No example or debordering theorem is claimed |

## Reproducible checks

Run `make all` from the repository root for the complete default gate. The
[Makefile](Makefile) provides these individual targets:

| Target | What success establishes |
|---|---|
| `make check-source` | The manuscript's 49 theorem/lemma/proposition/corollary/conjecture environments match the manifest exactly once; statuses, local links, imports, and source checks pass. Regression tests exercise missing coverage, a misclassified conjecture, an orphaned module, and broken artifacts |
| `make check-lean` | The pinned library builds with warnings as errors; every project declaration passes the axiom audit; the selected theorem audit and eight rational-identity executions pass |
| `make check-finite` | Six Python standard-library validators pass on their declared finite ranges, including reproduction of the explicit sextic profile pairing |
| `make paper` | The main manuscript, bibliography, and references build to `output/pdf/main.pdf` with no unresolved references or overflowing boxes |
| `make notes` | The companion note builds to `output/pdf/explicit-lower-bounds.pdf` under the same log checks |
| `make check-sage` | Optional exact block-parity identities and seeded finite-field rank evaluations run for prefix widths 2 and 3; requires SageMath |

Python 3.10 or newer is sufficient for the default finite scripts. PDF builds
require `latexmk`, `pdflatex`, and `biber`. Optional SageMath and Z3 programs,
parameters, and interpretations are listed in [research/README.md](research/README.md).
Generated files stay under `output/`; the manuscript proof still needs human
review and the PDFs still need visual inspection.

### Lean trust boundary

The source scan rejects proof placeholders and explicit project axioms.
[`scripts/check_axioms.lean`](scripts/check_axioms.lean) then traverses the
compiled dependencies of every declaration originating in a `KLocality`
module, including private helpers. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. This also rejects compiler-backed proof-evaluation
axioms, which a text search for placeholders alone would miss.

The separate [theorem and identity check](research/check_universal_marginal.lean)
audits twelve named declarations for the balanced lift and general marginal
variety. Eight executions cover independence, the quadratic model's cubic
odds ratio, hidden-variable summation, a nonidentity, the empty cube, and the
cone's freely varying scale. Their uniform correctness theorem is independent
of these finite executions.

Manifest status counts describe coverage, not a completion score. The source
checker does not establish semantic equivalence between a paper statement and
its proposed Lean counterpart. Passing every build is compatible with open
and partial rows in [FORMALIZATION.md](FORMALIZATION.md).

### Local validation record: 2026-09-05

The cleanup worktree passed `make all`: 8,100 Lean build jobs, an axiom audit
of all 3,210 project declarations using only the three allowed standard
axioms, twelve selected theorem audits, eight executable identity cases,
nine repository-check regression tests, and all six finite validators.
The block-lift validator covered 2,044 visible instances, including the empty
cube and empty blocks. The sextic generator reproduced both permutations of
the 192 expanded profiles.

`make check-sage` passed with SageMath 10.7.beta0, seed 0, and prime 1000003:
prefix widths 2 and 3 gave agreement-kernel ranks 16 and 256, respectively.
The sampled toric evaluation matrices also had full column rank (40 by 16 and
280 by 256). These are finite calculations, with the interpretation given in
[the experiment guide](research/README.md).

The 42-page manuscript and nine-page companion note were rebuilt with TeX
Live 2025 and visually inspected. Both passed the reference and overflow
checks. Python validation used Python 3.14.5. The GitHub workflow runs the
default checks on future pushes and pull requests; no hosted CI run is claimed
for this uncommitted worktree.

## Publication and novelty boundary

The July--August 2026 literature corpus under `research/literature-transfer/`
records model-convention and transfer-direction checks against primary
sources. The searches recorded at that time found no prior statement matching either the exact full-table
balanced block lift or the Eisenstein--Lindemann exchangeable localization
theorem.  This is evidence for positioning, not a priority certificate;
expert review in algebraic statistics and pseudo-Boolean reformulation remains
appropriate before submission.

The paper's use of “Gibbs model” always includes the topological closure.  Its
principal upper constructions may use boundary joint laws, arbitrary real
coefficients, and hidden--hidden interactions.  Claims about positive
finite-parameter Boltzmann machines, restricted Boltzmann machines,
coefficient complexity, or approximate representation require separate
theorems and are not implied here.
