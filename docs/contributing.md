# Research workflow

Keep the [manuscript](../main.tex), [theorem manifest](../FORMALIZATION.md),
and [evidence ledger](../VERIFICATION.md) consistent at each coherent milestone.

## Mathematical changes

1. State the model, quantifiers, and resource being bounded. Include boundary
   lifts, hidden--hidden interactions, and arbitrary coefficients when claiming
   a result for the paper's `LC_k`.
2. Give each theorem, lemma, proposition, corollary, or conjecture a stable
   LaTeX label and one manifest row. Mark a row checked only after matching
   every clause and convention to the Lean statement.
3. Add formal developments as focused modules imported by `KLocality.lean`.
   Preserve explicit bridge hypotheses and distinguish supplied witnesses from
   proved existence. A finite experiment does not discharge a quantified claim.
4. Record a new experiment's command, parameters, seed, dependencies, and
   interpretation in `research/README.md` or its linked note. Identify sampled
   calculations and specify the finite range of exhaustive checks.
5. Run `make check`; run `make paper` or `make notes` for the corresponding
   prose changes and inspect the resulting PDF. `make all` runs the complete
   default gate. Optional discovery searches are listed separately.

The source checker verifies label coverage, declared statuses, local Markdown
link targets, library imports, and absence of proof placeholders. It cannot
verify the semantic correspondence between a paper theorem and a Lean theorem.
The axiom audit likewise does not validate a novelty claim or a manuscript proof.

## Dependencies and output

Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together when
deliberately updating dependencies. Ordinary reproduction uses the committed
lockfile; it does not require `lake update`.

Generated PDFs and TeX auxiliary files live under `output/pdf/`, which is
ignored. Research source, reproducible scripts, and exact certificates belong
in version control. A useful local check log can be captured with:

```sh
mkdir -p output
make all > output/validation.log 2>&1
```

When reporting results, give the revision, commands run, and any checks that
were unavailable. Historical notes in `research/archive/` preserve their
original context and do not define the current proof boundary.
