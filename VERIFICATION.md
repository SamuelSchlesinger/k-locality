# Verification and evidence ledger

This file records what kind of evidence supports each major claim in
`main.tex`.  It deliberately distinguishes a manuscript proof from a Lean
proof, a finite computation, and a literature check.  None of those categories
silently substitutes for another.

Status reflected here: 2026-08-05.  The Lean toolchain is
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
| Definitions of marginal models, scoped marginal locality, and localization complexity | Lean checked in `KLocality/Core.lean`; manuscript definitions in Section 2 | The Lean `LC_k` API still requires an explicit universal-existence witness |
| Local verification and uniform ground-state locality | Lean checked in `KLocality/Core.lean` and `KLocality/GroundState.lean` | Covers the local-verification and nonnegative local-energy routes, not the full face--Gibbs equivalence |
| Face--Gibbs characterization | Manuscript proof; primary-source audit against finite exponential-family closure results | Not Lean formalized |
| Relative Gibbs reductions, composition, tensoring, and recovery of `n + L_k(D)` | Manuscript definitions and proofs | Not Lean formalized; this is a nonuniform projective weight reduction, not sample-preserving conversion or an efficient reduction between succinct inputs |
| Boundary-feasibility counterexample | Lean checked in `KLocality/InteriorFeasibilityCounterexample.lean` | Refutes only the support-intersection/interior-feasibility converse; it does not refute face--Gibbs geometry |
| Universal existence with at most `|supp(D)|` hidden bits | Manuscript proof | Not Lean formalized; universal existence is absent from the current `LC_k` API |
| Universal balanced block-feature lift | Manuscript proof; finite validation by `validate_block_lift.py` | The script checks small cubes, Rosenberg penalties, latent counts, graph uniqueness where feasible, and monomial factorization; the theorem is not Lean formalized |
| Marginal-ideal certificate, generic full-support lower bound, and worst-case `Theta_k(2^(n/k))` scale | Manuscript proofs; primary-source audit for toric parameterization and closure ingredients | No elimination implementation or Lean formalization of the general theorem |
| Effective rational hard tables and explicit certificate-degree bound | Manuscript proof | No end-to-end generated eliminant is checked for the asymptotic construction |
| Zero-temperature transfer | Manuscript proof using the closed finite selector-max image | Not Lean formalized; no finite script can establish the arbitrary-face limiting theorem |
| Exchangeable upper bound and explicit well-conditioned lower-bound family | Manuscript proof; exact finite validation by `validate_eisenstein_radial.py`; targeted primary-source audit | The script checks the encoding and algebraic preconditions on a finite range; Lindemann--Weierstrass and the marginal-ideal implication remain manuscript mathematics |
| Direct existential-real encoding | Manuscript proof | No standalone decision-procedure implementation |
| Quasipolynomial dense-table recognition | Manuscript proof from face enumeration plus a standard existential-real decision bound | No end-to-end recognizer implementation; complexity accounting is not Lean formalized |
| Few-variable full-support recognition | Manuscript proof; exact identities checked by `validate_full_support_recognition_reduction.py` | The script checks energy, minimizer, marginal-factorization, and conditional-odds identities, not the real-algebraic running-time theorem |
| Quadratic NAND recognizer synthesis with hardwired constants and exact gate-bit accounting | Lean checked through `KLocality/NANDCircuitWithConstantsLocalization.lean` | The generator half, NAND universality/existence, and transport from permissive raw `cslib` DAGs remain open in Lean |
| Generic fan-in generator and flat-recognizer bounds in `CircuitConnections.lean` | Lean derivations from `GeneratorToLocalizationBridge` and `FlatRecognizerToLocalizationBridge` | The bridge builders are explicit hypotheses, not constructed Lean proofs |
| Manuscript NAND generator and unambiguous-verifier variants | Manuscript proof | Not Lean formalized |
| Localization-to-circuit converse and natural-proofs proposition | Manuscript proofs; primary-source audit for exact-threshold integerization and Razborov--Rudich | Not Lean formalized |
| Parity localization and sign-definite-degree lower bound | Manuscript proof; source-level check of the Boros--Crama--Rodríguez-Heck formulas | The corrected odd case is proved directly in the manuscript and is not attributed to their formula (27) |
| Selector facial-closure duality and block-layer examples | Manuscript proofs; finite validation by `validate_selector_block_layers.py` | The unrestricted block-layer direct-sum conjecture remains open |
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
