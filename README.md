# Localization Complexity

Research manuscript and partial Lean formalization of **Localization Complexity
of Hidden-Variable Gibbs Models**, by Samuel Schlesinger and Joshua Grochow.

For a probability law `D` on `n` bits, `LC_k(D)` is the fewest hidden bits
needed to make `D` the marginal of a `k`-local maximum-entropy law. Equivalently,
the lifted law has a degree-at-most-`k` Gibbs potential on an exposed support
face. The paper studies `k >= 2`, where every distribution has a finite lift.

The model allows arbitrary real coefficients, interactions between hidden
bits, and boundary joint laws, including for full-support visible laws. Only
hidden coordinates are charged. These conventions matter when comparing the
results with restricted Boltzmann machines, finite-precision models, or
approximate representations.

## Start here

- [Manuscript](main.tex): definitions, principal theorems, proofs, and bibliography.
  Build the PDF with `make paper`.
- [Paper-to-Lean manifest](FORMALIZATION.md): every named theorem, lemma,
  proposition, corollary, and conjecture, with its exact formalization boundary.
- [Verification ledger](VERIFICATION.md): evidence, commands, and validation scope.
- [Lean library guide](docs/library.md): entry points and module groups.
- [Research notes and experiments](research/README.md): supplementary arguments,
  finite checks, exploratory searches, and historical material.

For a first reading, follow the manuscript's definitions, face--Gibbs theorem,
universal lift, and marginal-ideal certificate before the exchangeable and
recognition results. The support and circuit material provides a second route
through the paper.

## Results and proof status

All asymptotic statements below fix `k >= 2`. A manuscript proof and a Lean
proof are separate evidence; a successful build does not close the gaps.

| Result | Manuscript | Lean coverage |
|---|---|---|
| Face--Gibbs characterization, including boundary laws | Proved | Checked |
| Universal balanced lift: `LC_k(D) = O_k(2^(n/k))` | Proved | Checked, including the exact finite bound |
| Projective marginal variety, dimension bound, and integer certificates | Proved | Checked; rational identity membership is executable |
| Generic lower bound and worst-case `Theta_k(2^(n/k))` scale | Proved | Upper bound and algebraic ingredients checked; genericity remains |
| Exchangeable scale `Theta_k(n^(1/k))` and a bounded likelihood-ratio family | Proved | Open |
| Zero-temperature transfer and dense-table recognition algorithms | Proved | Open |
| Circuit traces, converse simulations, and support bounds | Proved | Partial; see the manifest for individual statements |
| Strict benefit from boundary lifts | Conjecture | Open in both |

The library also proves explicit full-support rational cubic lower bounds,
explained in [the companion note](notes/explicit-lower-bounds.tex). The
base-coded family has enormous rational entries; the bounded-precision
block-parity family is defined by exhaustive finite search. Neither supplies
an efficiently explicit circuit lower bound. The generic almost-everywhere
theorem and sharp cubic lower-bound scale remain unformalized.

## Reproduce

The Lean toolchain and transitive dependencies are pinned in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
Install Lean through `elan`; the first Lake build fetches the pinned packages.
The finite validators require Python 3.10 or newer and its standard library.
PDF builds require `latexmk`, `pdflatex`, and `biber`.

```sh
make check       # source/manifest checks, Lean build, axiom audit, finite validators
make paper       # output/pdf/main.pdf
make notes       # output/pdf/explicit-lower-bounds.pdf
make all         # all of the above
```

`make help` lists individual targets. Optional SageMath and Z3 discovery
programs are documented in [research/README.md](research/README.md); they are
separate from the default validation gate.

To use the library, write `import KLocality`, or import a focused module such
as `KLocality.BalancedUniversalLift`. There is no command-line application.

## Continuing the research

Use [FORMALIZATION.md](FORMALIZATION.md) to choose an unformalized result and
record the exact declaration and hypotheses when completing it. Keep
conjectures and assumed circuit bridges visible. The
[contribution guide](docs/contributing.md) describes the validation workflow.
Literature notes record earlier source checks; novelty and priority remain
subject to independent review.
