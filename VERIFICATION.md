# Verification and evidence ledger

This file records what kind of evidence supports each major claim in
`main.tex`.  It deliberately distinguishes a manuscript proof from a Lean
proof, a finite computation, and a literature check.  None of those categories
silently substitutes for another.

Status reflected here: 2026-08-12.  The Lean toolchain is
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
| Face--Gibbs characterization | Lean checked in `KLocality/FaceGibbsCharacterization.lean`, with analytic and finite-dual infrastructure in `KLocality/GibbsOptimality.lean`, `KLocality.FacialSupport.lean`, and `KLocality.MarginalPolytope.lean` | The exact finite Boolean statement is checked: exposed marginal-polytope face, exact support preimage, normalized Gibbs formula, and both implications |
| Full-support no-latent characterization | Lean checked in `KLocality/NoLatent.lean` | Zero latent coordinates are transported through an explicit assignment equivalence; `LC_k(D)=0`, degree-at-most-`k` log density, and the normalized full-cube Gibbs formula are proved equivalent for `k ≥ 2` |
| Facial conditioning and duplication/fixing pullback | Lean checked in `KLocality/FacialConditioning.lean`, `KLocality/CoordinateSubstitution.lean`, `KLocality/CoordinatePullback.lean`, and `KLocality/FacialConditioningPullback.lean` | Filtering on a positive facial event preserves locality with the same latent type; a bijective Boolean-cube parametrization induced by duplicated variables and constants then preserves degree, support weights, and the observed marginal, yielding the exact localization-complexity inequality |
| Relative Gibbs reductions, composition, tensoring, and recovery of `n + L_k(D)` | Lean checked for the definition, identity, additive composition, absolute equality, and compilation corollary in `KLocality/RelativeGibbs.lean`, `KLocality/GibbsReduction.lean`, `KLocality/GibbsReductionComposition.lean`, and `KLocality/GibbsReductionAbsolute.lean`; manuscript proof for tensoring | The tensor clause is not yet Lean formalized; this remains a nonuniform projective weight reduction, not sample-preserving conversion or an efficient reduction between succinct inputs |
| Boundary-feasibility counterexample | Lean checked in `KLocality/InteriorFeasibilityCounterexample.lean` | Refutes only the support-intersection/interior-feasibility converse; it does not refute face--Gibbs geometry |
| Universal existence with at most `|supp(D)|` hidden bits | Lean checked in `KLocality/UniversalExistence.lean` | The construction uses one support-index bit per positive-mass visible point, a quadratic exact-one/consistency energy, and singleton hidden marginals to preserve arbitrary weights |
| Universal balanced block-feature lift | Manuscript proof; finite validation by `validate_block_lift.py` | The script checks small cubes, Rosenberg penalties, latent counts, graph uniqueness where feasible, and monomial factorization; the theorem is not Lean formalized |
| Marginal-ideal certificates, generic full-support lower bound, and worst-case `Theta_k(2^(n/k))` scale | Manuscript proofs and primary-source audit for the general theorem; Lean-checked zero-hidden log-interaction API in `KLocality/LogInteractionCertificate.lean`; uniform boundary-safe marginal-trade checker in `KLocality/MarginalTradeCertificate.lean`; exact examples in `KLocality/FullSupportCertificateExample.lean`, `KLocality/CubicFullSupportExample.lean`, `KLocality/NonzeroHiddenCertificateExample.lean`, `KLocality/ExplicitCubicLowerBound.lean`, and `KLocality/UniformExplicitCubicLowerBound.lean` | Lean proves `LC_3(D)=1` for the rational four-bit boosted-point law and `LC_2(D)=2` for the five-bit law `(1+1_123)(1+1_345)/41`. It proves `LC_3(D)>1` for the explicit ten-bit powers-of-powers law, and now proves the superlinear uniform statement: for every `m`, the full-support rational law on `4m+24` bits with unnormalized weights `2^(2^v)` off the final state and `1` at the final state satisfies `LC_3(D_m)>2^m`; for `m>=13`, Lean also derives `LC_3(D_m)>(4m+24)^2`. The parameterized proof bounds cubic scopes by `(q+1)^3` and selects finite profile collisions noncomputably; certificate degree is `2(2^(4m+24)-1)`. The table is explicit but its largest integers have doubly exponential binary length (and numerical value one exponential level larger). The general all-`k` eliminant, generic almost-everywhere result, sharp `Theta_k(2^(n/k))` scale, practical certificate extraction, and general degree bounds remain unformalized. |
| Full-support adjacent hierarchy | Lean-checked fixed cubic instance in `KLocality/CubicFullSupportExample.lean`; manuscript proof of Proposition `prop:positive-hierarchy` | The exact rational visible law has `LC_3(D)=1` and `LC_4(D)=0` by locality monotonicity, but its displayed one-hidden lift is a boundary model. The uniform all-`k`, all-ambient-dimension statement and the manuscript's strictly positive lift remain unformalized. |
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
| Parity localization and sign-definite-degree lower bound | Generic certificate soundness Lean checked in `KLocality/WitnessProductCertificate.lean`; uniform lower and upper bounds Lean checked in `KLocality/UniformParityLowerBound.lean` and `KLocality/UniformParityUpperBound.lean`; exact cubic instance Lean checked independently in `KLocality/CubicParityExample.lean`; source-level check of the Boros--Crama--Rodríguez-Heck formulas | Lean proves symbolically that every `k`-localization of `U_even,n` with `ell` hidden bits satisfies `n <= k * 2^ell`. It also constructs a quadratic `ell`-hidden lift whenever `n < 2^(ell+1)`, with a proved injective binary half-weight encoding and unique uniform extension. Consequently `LC_3(U_even,3*2^ell+1)=ell+1` for every `ell>=1`; the earlier `LC_3(U_even,7)=2` result is the first case. The manuscript's stronger `floor(k/2)` upper construction and exact general quadratic formula remain manuscript-only. |
| Selector facial-closure duality, rational trade certificates, and block-layer examples | Lean checked in `KLocality/FacialClosure.lean`, `KLocality/SelectorLeakage.lean`, `KLocality/SelectorTrade.lean`, and `KLocality/GroundStateExtension.lean`; a three-cube alternating trade is checked in `KLocality/SelectorTradeExample.lean`; finite block-layer validation by `validate_selector_block_layers.py` | The full selector duality and compilation of a supplied normalized rational dual table into same-marginal leakage are checked. The general rational Farkas alternative, filtered-slice theorem, and unrestricted block-layer direct-sum conjecture remain open |
| Interior-versus-closure separation | Open conjecture | No example or debordering theorem is claimed |

## Reproducible checks

Run these commands from the repository root.

### Manuscript

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Success means that the bibliography, references, figures, and PDF build are
consistent.  Inspect `main.log` for warnings; a green build is not a proof
check.

### Lean

```bash
lake build -KwarningAsError=true
```

Also audit the source for placeholders:

```bash
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' KLocality Main.lean KLocality.lean
```

An empty placeholder search and a successful build establish only the Lean
claims listed above.

### Finite and exact-arithmetic validation

```bash
python3 research/literature-transfer/quadratization/data/validate_block_lift.py
python3 research/literature-transfer/rbm/data/check_bounds.py
python3 research/literature-transfer/flagship-routes/data/validate_eisenstein_radial.py
python3 research/literature-transfer/flagship-routes/data/validate_selector_block_layers.py
python3 research/literature-transfer/flagship-routes/data/validate_full_support_recognition_reduction.py
sage -python research/analyze_block_parity_fiber.py --prefix-bits 2
sage -python research/analyze_block_parity_fiber.py --prefix-bits 3 --samples 280
```

Each script prints its tested range or identities.  Those printed ranges are
the scope of the computation.

## Publication and novelty boundary

The literature corpus under `research/literature-transfer/` checks model
conventions and transfer directions against primary sources.  Targeted
searches found no prior statement matching either the exact full-table
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
