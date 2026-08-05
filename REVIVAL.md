# Revival memo: from local checks to ground-state extensions

> **Status note (July 2026, second checkpoint).** This memo records the first
> revival checkpoint.  The current paper has since added a universal
> balanced-block lift and matching generic lower bound, nonnegative
> nondeterministic degree with exact quadratic parity, an algebraic
> marginal-ideal certificate with explicit linear-algebra degree bounds, a
> zero-temperature transfer producing explicit full-support hard Gibbs rays, a
> sharp inverse-temperature-one exchangeable target theorem, exact dense-table recognition
> algorithms with an ETH barrier, a Razborov--Rudich natural-proofs barrier
> for the support program, an extended-formulations comparison (nonnegative
> rank, slack matrices, psd rank), and the interior-versus-closure conjecture
> that boundary lifts strictly help.  The source has also been restructured
> top-down: reading order equals source order, the contributions reference
> numbered theorems, an organization roadmap opens the paper, and the longest
> proofs are step-structured.  `main.tex` and the literature corpus under
> `research/literature-transfer/` are authoritative.

## Executive assessment

The project did not fail for the reason suggested by the current four-page draft.
The counterexample at commit `c2962b4` refutes one support lemma, not the localization
complexity program.  The original lemma tried to recover global support by intersecting
the positive supports of the individual local marginals.  That is too rigid: local
expectations can combine linearly to force a global zero even when every local marginal
entry is positive.

The correct replacement is the standard face geometry of a marginal polytope.  A
maximum-entropy distribution constrained by degree-at-most-`k` statistics has support
equal to the inverse image of a face of the `k`-marginal polytope.  Equivalently, its
support is the ground-state set of a nonnegative `k`-local pseudo-Boolean Hamiltonian.
This gives an unconditional, quantitatively weaker version of the abandoned converse:
the support of a distribution with a small `k`-localization has a small
nondeterministic Boolean circuit.

That result restores the intended complexity-theoretic spine of the paper.  The most
credible paper is no longer “local marginal supports behave like a CSP.”  It is:

> localization complexity is hidden-variable extension complexity for the closure of
> bounded-order exponential families; circuits give such extensions, and every such
> extension gives a nondeterministic recognizer through a low-degree exact threshold.

The underlying exponential-family face theorem is established mathematics, not a new
claim.  The potentially new contribution is its use to obtain the circuit converse and
to organize a distributional auxiliary-variable complexity measure between circuit
traces, hierarchical models, and pseudo-Boolean quadratization.

## What happened in the history

- `8aa75b5`: introduced the full program, including a support-intersection lemma and
  an overreaching circuit consequence.
- `1e88efd`: strengthened exposition but unfortunately doubled down on the false step:
  positivity of every local marginal cell was treated as sufficient for an interior
  feasible joint.
- `b2b6229`: responsibly reduced the paper to the sound local-verification upper bounds
  and began a Lean development.
- `9445ddb`: restored only a conditional converse under a maximal-support hypothesis.
- `c2962b4`: formalized a concrete pairwise counterexample and removed the converse.

The current state is mathematically conservative but still short of the original
ambition.  Its verification boundary is now:

1. Lean checks the entropy bound, the abstract local-verification theorem, and the
   counterexample.
2. Lean checks the exact quadratic NAND Hamiltonian, a typed acyclic sequential
   circuit semantics, trace existence and uniqueness, the uniform visible marginal,
   and `LC_2(U_S) <= C_NAND(S)`.  The paper's hardwired-input constants are
   substituted algebraically and add no latent coordinates.
3. NAND universality/existence, cslib-DAG transport, generators, and the older
   generic fan-in bridge hypotheses are not yet discharged.

The audit found that the Lean build was not reproducible because `lakefile.toml` pinned
cslib commit `8265e6c1...`, which is no longer present in the fetched repository history.
The revived branch replaces it with reachable commit `8961914...` from the same
Lean-toolchain era.  A clean dependency update and `lake build` now succeed.  The revived
Lean counterexample also checks the quadratic energy table and proves from the pairwise
constraints that the two positive-energy states have zero mass.

## The corrected structural theorem

For `y in {0,1}^N`, let

```text
chi_k(y) = (product_{i in A} y_i)_{A subseteq [N], |A| <= k}.
```

These monomial moments carry the same information as all marginals on at most `k`
variables.  Let `P_k(N) = conv{chi_k(y) : y in {0,1}^N}`.

For a distribution `Q` on `{0,1}^N`, the following are equivalent.

1. `Q` is `k`-local under the paper's definition.
2. `Q` maximizes entropy among distributions with the same full vector
   `E_Q[chi_k]`.
3. There are a face `F` of `P_k(N)` and a vector `theta` such that

   ```text
   supp(Q) = {y : chi_k(y) in F},
   Q(y) proportional to exp(theta . chi_k(y)) on supp(Q).
   ```

Since every polytope face is exposed, there is also a degree-at-most-`k` multilinear
polynomial `E` such that

```text
E(y) >= 0 on {0,1}^N,
supp(Q) = {y : E(y) = 0}.
```

The proof has four short ingredients.

- Adding all at-most-`k` marginals of `Q` cannot destroy its maximality.
- The target moment vector lies in the relative interior of a unique face of the
  marginal polytope.
- Entropy maximization gives positive mass to every state that can occur in any
  feasible distribution, so the optimizer's support is the inverse image of that face.
- Lagrange multipliers on the resulting support give the Gibbs form.  Conversely, the
  exposing energy forces every moment-matching competitor onto the same face, and a KL
  divergence argument proves maximum entropy.

## Why the counterexample supports the repair

For the pairwise marginals in `interior_feasibility_counterexample.tex`, set

```text
E(x,y,z) = x - xy - xz + yz = (x-y)(x-z).
```

On the Boolean cube, `E` is `1` exactly at `011` and `100`, and `0` at the other six
states.  The prescribed pairwise marginals give

```text
E[X] - E[XY] - E[XZ] + E[YZ]
  = 1/2 - 9/20 - 2/5 + 7/20
  = 0.
```

Thus every feasible joint has `E[E(X,Y,Z)] = 0`.  Nonnegativity forces it to put zero
mass at `011` and `100`.  No individual local cell is forbidden; a linear combination
of local statistics exposes the correct global support face.

## Corrected circuit converse

Suppose `D` on `n` visible bits has a `k`-localization `Q` with `ell` latent bits, and
write `N=n+ell` and

```text
d_k(N) = sum_{j=0}^k binom(N,j).
```

The support of `Q` is recognized by testing one exact linear equality in the
`d_k(N)` monomials of degree at most `k`.  Standard integer-weight bounds for exact
threshold functions give coefficients with `O(d_k(N) log d_k(N))` bits.  Computing the
monomials, adding the signed integer weights, and testing equality uses

```text
O(d_k(N)^2 log d_k(N))
```

fan-in-two Boolean gates.  A nondeterministic recognizer for `supp(D)` guesses the
`ell` latent bits and runs this test.  Therefore

```text
NSize(supp(D))
  <= ell + O(d_k(n+ell)^2 log d_k(n+ell)).
```

For fixed `k`, this implies the unconditional lower bound

```text
LC_k(D)
  >= Omega_k((NSize(supp(D)) / log NSize(supp(D)))^(1/(2k))) - n.
```

The old `1/k` exponent came from treating support as a conjunction of local checks.
The corrected standard-circuit simulation pays for exact-threshold weights and gives
`1/(2k)` (up to logarithms).  In a circuit model with exact-threshold gates, the stronger
exponent is recovered directly.

## Polynomial-method admission test

The first explicit lower-bound tool intrinsic to the revived measure comes from
nondeterministic polynomial degree.  If `Q` is a `k`-localization with `ell` latent
bits and `E(x,h)` is its nonnegative degree-`k` exposing energy, then

```text
P(x) = product_{h in {0,1}^ell} E(x,h)
```

vanishes exactly on `supp(D)` and has degree at most `k * 2^ell` after
multilinearization.  Therefore

```text
ndeg(complement(supp(D))) <= k * 2^L_k(D).
```

This yields a nearly tight explicit example.  For the uniform even-parity
distribution, nondeterministic-degree symmetrization gives the lower bound
`L_k >= log_2(n) - O(log k)`.  Conversely, one witness can encode a block of even
Hamming weights, and the nonnegative energy

```text
product_{r=0}^{floor(k/2)-1}
  (sum_i x_i - 2 * (floor(k/2) * J(h) + r))^2
```

has degree at most `k` and a unique zero-energy witness over every even-parity
string.  Hence `L_k(U_even) = log_2(n) + O_k(1)` for fixed `k`.

This passes a useful admission gate: the measure now has an explicit, nonconstant,
nearly tight lower bound not imported from Boolean circuit size.  It does not yet
give a new circuit lower bound.  Since nondeterministic degree is at most `n`, this
method alone cannot force more than logarithmically many latent bits.  A stronger
method must retain the shared low-degree parametrization of the witness slices rather
than multiplying all `2^ell` slices together.

The same lower bound gives a strict adjacent hierarchy.  For every `k >= 3`, let
`D_k` be uniform on all `(k+1)`-bit strings except the all-ones string.  Its support
complement is `AND_(k+1)`, which has nondeterministic degree `k+1`, so `L_k(D_k)`
cannot be zero.  A one-bit degree-`k` ground-state extension is obtained by splitting
the visible variables into blocks of sizes `2` and `k-1` and letting the latent bit
select which block product must vanish.  A degree-`(k-1)` Gibbs potential assigns
weight `1/2` to each of the two witnesses when both products vanish and weight `1`
to the unique witness otherwise, making the visible marginal uniform.  Thus

```text
L_k(D_k) = 1 and L_(k+1)(D_k) = 0.
```

This resolves the qualitative hierarchy question in the draft; the quantitative
question is now whether explicit adjacent gaps can grow with the input length.

## Novelty and positioning

The definition sits close to existing work and should say so explicitly.

- A `k`-local distribution is an element of the closure of the binary hierarchical
  exponential family of order `k`.  Support faces and boundary distributions are
  standard in algebraic statistics.
- Taking visible marginals after adding hidden variables is the subject of
  hidden-variable hierarchical models and Boltzmann-machine expressivity.
- For `k=2`, minimizing auxiliary variables has a strong analogy with quadratization of
  pseudo-Boolean functions.  Quadratization preserves an entire objective under
  minimization; localization complexity preserves both a ground-state support and Gibbs
  weights after marginalization.

Accordingly, the definition alone is unlikely to carry a paper.  The circuit trace
upper bounds plus the unconditional face/exact-threshold converse are the plausible new
core.  A strong next version should add at least one of:

- a growing explicit separation between adjacent levels of `LC_k`;
- tighter support-only bounds, especially in exact-threshold or threshold-circuit
  models;
- nontrivial lower bounds for structured families using modes, coding theory, or
  marginal-polytope faces;
- a precise comparison with quadratization/hidden-unit complexity.

## Immediate formalization gates

Current Lean progress goes beyond the original first gate: the quadratic
counterexample certificate is checked, and the repository now also contains a
general theorem sending nonnegative sums of bounded-scope energy terms to
uniform `k`-local ground-state laws.  The exact quadratic NAND polynomial,
summed constraint Hamiltonian, accepting-output penalty, and the resulting
two-locality of every nonempty finite accepting ground space are checked as
well.  Gate 5 is now complete for typed sequential NAND recognizers with the
paper's hardwired-input constants: Lean checks literal quadratic substitution,
the constraint translation, unique traces, the visible marginal, the 2-local
localization, and the corresponding minimum-size inequality.  Its remaining
extensions are generator circuits, a universality/existence construction, and
transport from the permissive cslib DAG representation.

1. Formalize the counterexample's quadratic exposing energy.  This is small and directly
   checks the conceptual repair.
2. Prove that an entropy maximizer over a finite affine slice has maximal feasible
   support.
3. Introduce the finite feature map and prove the face-support theorem.
4. Only then rebuild the nondeterministic converse; do not restore the deleted
   `LocalSupportSet` argument.
5. Replace the abstract circuit bridge assumptions with actual trace-witness builders.

The polyhedral step is substantially larger than the current Lean core.  The paper can
state it rigorously now, but it should not be described as Lean-checked until steps 2--3
are complete.
