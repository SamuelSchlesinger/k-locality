# Statistical-model literature and circuit transfers

This corpus audits which results about hierarchical models, restricted
Boltzmann machines, marginal models, and pseudo-Boolean reformulations transfer
to localization complexity and, in turn, to deterministic or nondeterministic
Boolean circuits.

The governing rule is that a result is not called a transfer until its model
matches the paper's conventions: binary hidden variables, arbitrary
order-at-most-`k` interactions, exact representation in the closure, and cost
measured by hidden bits rather than parameters.

## Research map

- [Hierarchical and marginal models](hierarchical-models/index.md): closure,
  support faces, neighborliness, dimension, and hidden-state representations.
- [Restricted Boltzmann machines](rbm/index.md): exact/approximate universal
  approximation, support and mode results, and which bounds survive passage to
  unrestricted quadratic lifts.
- [Pseudo-Boolean reformulations](quadratization/index.md): auxiliary-variable
  upper and lower bounds, the universal monomial graph, and their relation to
  localization.
- [Circuit transfers](circuits/index.md): deterministic and nondeterministic
  simulations, converses, and a ledger of valid and invalid implications.
- [Flagship theorem routes](flagship-routes/index.md): three parallel attacks on
  the remaining significance gap---natural full-support lower bounds, explicit
  selector obstructions, and consequences for recognized circuit models.
- [Master bibliography](sources.md): canonical primary-source entries used by
  every subtopic.

## Main conclusions

1. The finite face--Gibbs characterization is the exact localization form of
   the classical facial stratification of finite exponential-family closures.
2. Neighborliness gives `|supp(D)| <= 2^k-1 => L_k(D)=0`.
3. RBM and hidden-hierarchical universality theorems give valid localization
   upper bounds after compactness, while their lower bounds generally remain
   restricted-model statements.
4. Universal monomial features yield an exact distributional transfer for
   every fixed `k>=2`: a balanced `k`-block graph gives
   `L_k(D)=O_k(2^(n/k))` for every `D`.
   Together with the parameter-dimension obstruction, this fixes the
   worst-case and almost-everywhere full-support scale at
   `Theta_k(2^(n/k))`.
5. Circuit traces transfer in both directions. An `ell`-bit localization gives,
   for fixed `k`, a polynomial-size nondeterministic support circuit in
   `n+ell` and a deterministic support circuit of size `2^ell poly_k(n)`.
   Conversely, the NAND truth-table graph has a nonnegative quadratic
   ground-state penalty, so an `s`-gate deterministic NAND recognizer gives
   `L_2(U_S)<=s`; generators transfer exactly, while arbitrary verifier traces
   weight visible inputs by accepting-witness multiplicity. Restricted-model
   lower bounds cannot be inserted into these implications as if they
   lower-bounded unrestricted localization.
6. Retaining the sign of an optimal facial-cover product gives the sharper
   chain `ndeg <= ndeg_+ <= k fc_k(supp D) <= k 2^L_k(D)` and the exact
   quadratic complexity of flat parity.
7. The support-only invariant `GSE_k(S)` is characterized exactly by a
   nonnegative witness-slice cover whose visible coefficient tables lie in the
   filtered spaces `RM_R(ell,k-|A|)`, equivalently by selector facial closure.
   Each selector has an exact rational LP/Farkas dual, while ordinary
   coefficient rank provably forgets the needed witness labels.  A face count
   proves `GSE_k(S)=Omega_k(2^(n/(k+1)))` for almost every support and remains
   exponential after random thinning of one Hamming layer.  For separated
   block-layer supports, the one-block complexity is exact and the direct sum
   is exact under block-symmetric slices; the unrestricted direct sum remains
   open and subject to the NAND-circuit barrier.
8. The explicit exchangeable law
   `D_n(x) proportional to exp(-2^(|x|/r_n))`, where
   `r_n=2^floor(log_2(n+1))`, has
   `L_k(D_n)=Theta_k(n^(1/k))` for every fixed `k>=2` even though
   `max D_n/min D_n<e^3`.  This fixed-temperature theorem combines a
   quadratically exposed binary-weight copy, an Eisenstein power basis,
   Lindemann--Weierstrass, and the boundary-safe marginal ideal.  The
   zero-temperature transfer also extends from integer to arbitrary real
   objectives by closedness of a finite selector-minimum image.
9. The projective marginal ideal is a boundary-safe invariant: nonvanishing of
   an eliminant is an exact certificate that `L_k(D)>ell`, turning generic
   dimension counting into an effective lower-bound method.  Base coding gives
   a computable rational cold interval on which the certificate stays nonzero.
10. For dense exact rational tables, recognition with `ell<=cn` is decidable
    in deterministic time `L^{O_(k,c)(log^k L)}`.  For full-support tables and
    fixed `ell`, this improves to `L^{O_(k,ell)(log^(k-1) L)}`; the trace test
    on a specified, promised facial graph support is polynomial time.  Under
    ETH these
    quasipolynomial algorithms rule out polynomial-output NP-hardness
    reductions, but they do not settle polynomial-time recognition or cover
    sparse, sampled, or succinct inputs.

## Question status

| Question | Status |
|---|---|
| Which published universality results transfer? | Resolved for the audited hierarchical/RBM sources; compactness turns their fixed-size approximation into exact closure localization. |
| Which lower bounds remain subclass-specific? | Resolved for RBM dimension, strong-mode, and threshold-code bounds: they do not bound unrestricted localization. |
| Can witnesses be expanded deterministically? | Resolved: `2^ell poly_k(n)` gates, with a `log(1+C_2)` converse. |
| Do ordinary fan-in-two circuits give quadratic localizations? | Resolved: a nonnegative NAND penalty gives exact deterministic-recognizer and generator transfers; verifier-to-uniform-law transfer additionally needs constant accepting-witness multiplicity. |
| Is there a genuinely stronger support invariant than nondeterministic degree? | Resolved structurally: `GSE_k` has an exact filtered Reed--Muller slice criterion and an exponential almost-all-supports bound. Explicit lower bounds remain circuit-hard at `k=2`. |
| Can optimization lower bounds transfer to full-support laws? | Resolved at zero temperature for arbitrary real objectives by the degree-reduction transfer theorem. |
| Can localization be recognized from an exact rational table? | Partially resolved: fixed-`k` linear latent budgets have a deterministic quasipolynomial algorithm; fixed-budget full-support tables have a sharper one, and a promised facial graph trace can be tested in `P`.  Polynomial-time global recognition remains open even if a successful lift might be graph-supported. |
| What remains open? | Sharper standard-gate compilation, polynomial-time versus quasipolynomial dense fixed-budget recognition, succinct-input algorithms, general sparse architectures beyond the audited models, the unrestricted block-layer selector direct sum, a rational analogue of the well-conditioned radial family, and comparable lower bounds for named physical or combinatorial models. |

## Transfer standard

Every candidate implication will be labeled as one of:

- **Exact transfer:** all hypotheses match and the conclusion follows.
- **Closure transfer:** the source proves approximation, but its closure gives
  exact representation under the paper's definition.
- **Restricted-model result:** informative comparison only; it does not bound
  unrestricted localization complexity in the claimed direction.
- **Conditional transfer:** valid only after an explicit additional hypothesis.
- **Non-transfer:** a tempting implication that fails because information is
  lost or models are incomparable.

## Supplementary code

- [Balanced-block lift checker](quadratization/data/validate_block_lift.py):
  verifies Rosenberg penalties, latent counts, and monomial factorization on
  small instances; graph uniqueness is exhaustively enumerated when the
  feature count is at most ten.
- [RBM bound checker](rbm/data/check_bounds.py): checks the reported universal
  and dimension inequalities on representative ranges.
- [Eisenstein radial checker](flagship-routes/data/validate_eisenstein_radial.py):
  checks the all-`n` block embedding, exact quadratic feature threshold,
  Eisenstein coefficient conditions, bounded energy range, and base-`L`
  lookup encoding on small instances.
- [Block-layer selector checker](flagship-routes/data/validate_selector_block_layers.py):
  checks the primitive-line margins, projected zero set, unique witnesses, and
  degree-`2q` sign-definite certificate on small instances.
- [Full-support recognition checker](flagship-routes/data/validate_full_support_recognition_reduction.py):
  checks with exact arithmetic the energy, minimizing fibers, marginal
  factorization, and conditional-odds identities used by the fixed-budget
  recognition reduction.

## Known limitations

The balanced-block construction is mathematically checked, but its precise
novelty relative to general factor-graph arity reduction and marginal-extension
literatures remains only partially audited. The exponent and balanced
dictionary are classical; the exact distributional graph lift is the candidate
new synthesis.  The fixed-temperature radial theorem has a targeted source
audit but still warrants external expert novelty review, and its probabilities
are transcendental despite being explicit and uniformly well conditioned.  The
corpus distinguishes these uncertainties from correctness.

## Revision history

- **Author checkpoint (`513d79a`).** Initial source-by-source corpus and model
  dictionary.
- **Revision 1 (`ada4665`).** Corrected transfer directions and constants; added exact
  NAND synthesis, boundary-safe marginal ideals, zero-temperature transfer,
  and the filtered ground-state-extension invariant.
- **Revision 2.** Added selector facial-closure duality and LP certificates,
  the rank obstruction and random-layer thinning, tropical-statistics priority,
  effective cold intervals, and exact rational-table recognition.
- **Final review.** Compiled every citation through the master bibliography,
  separated the two Montúfar--Morton 2015 sources, reconciled the
  facial-cover and filtered-slice statements with the paper, and reran both
  supplementary checkers successfully.  Remaining questions in the status
  table are research problems, not unresolved corpus claims.
- **Revision 3.** Tested the three flagship routes; admitted the explicit
  fixed-temperature radial lower bound, retained the selector direct sum as a
  sharply delimited open problem, and added quasipolynomial dense-recognition
  algorithms with their ETH hardness barrier.
