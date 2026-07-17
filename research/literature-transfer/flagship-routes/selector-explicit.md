# Explicit selector obstructions

## Outcome

The unrestricted flagship ambition meets a real circuit barrier, but a useful
fragment can be solved exactly.  This note proves three statements.

1. For an explicit one-block support consisting of `2^r` separated central
   Hamming layers, both quadratic ground-state extension complexity and the
   localization complexity of its uniform law are exactly `r`.
2. For the `m`-fold block product of that support, the unrestricted complexity
   lies between `r` and `mr`, while the exact nonnegative witness-product
   invariant remains only `r`: it provably has no direct-sum power here.
3. If every fixed-witness slice respects the block symmetries, then the upper
   bound is sharp: exactly `mr` hidden bits are necessary.  The same theorem
   gives an exact block-symmetric zonotope obstruction.

Thus the precise unrestricted direct-sum statement is isolated as a concrete
open problem.  Proving it would give a linear lower bound when `r=1`, not a
superpolynomial general-circuit lower bound.  This is a plausible route to a
nontrivial explicit theorem without claiming a breakthrough that the circuit
transfer rules out.

## Where the general-circuit barrier begins

Write `GSE_2(S)` for the least number of hidden bits in a nonnegative quadratic
energy whose projected zero set is `S`.  The quadratic NAND synthesis theorem
in the manuscript gives

```text
GSE_2(S) <= w + s
```

for every NAND verifier with `w` witness bits and `s` gates.  For a deterministic
NAND recognizer of `S`, the uniform-support version also gives

```text
L_2(U_S) <= s.
```

Consequently:

- a superpolynomial unrestricted lower bound for a polynomial-time decidable
  explicit family would imply that this family has no polynomial-size Boolean
  circuits, and hence would separate `P` from `P/poly`;
- an exponential unrestricted lower bound for an explicit NP support would in
  particular give an exponential lower bound for nondeterministic circuits;
- a logarithmic or linear lower bound need not cross an unknown asymptotic
  circuit barrier, but it must still survive every unrestricted verifier
  construction.

The selector LP does not make this implication disappear.  It reformulates a
lower bound as a Farkas obstruction for *every* selector, and a NAND verifier
supplies one of the selectors that must be defeated.  The safe way to use a
symmetry hypothesis is therefore to state it as a restriction on the model,
not to silently symmetrize an arbitrary selector.

## The explicit block-layer family

Fix integers `r>=1` and `m>=1`, and put

```text
q = 2^r,                 b = 4q,
T_r = {q, q+2, ..., 3q-2} subset {0,...,b}.
```

Partition `n=mb` visible bits into blocks `B_1,...,B_m` of size `b`, and write
`W_j(x)=sum_{i in B_j} x_i`.  Define

```text
S_{m,r} = {x : W_j(x) in T_r for every j}.
```

This is an explicit, block-permutation-invariant support.  Membership is just
`m` Hamming-weight range-and-parity tests.  The choice of margins in `T_r` is
deliberate: two distinct target tuples determine a primitive lattice line that
can be extended by one step past both target points while remaining in the
weight box.

### Exact sign-definite degree

Let `ndeg_+(f)` be the least degree of a real multilinear polynomial that is
nonnegative on the cube and positive exactly where `f=1`, as in the
manuscript's nonnegative refinement of nondeterministic degree.  The underlying
nondeterministic degree was introduced by de Wolf [dewolf03][dewolf03].

**Proposition 1 (the witness product has no block direct sum).**  For all
`m,r>=1`,

```text
ndeg_+(complement(S_{m,r})) = 2q.
```

**Proof.**  For the upper bound, set

```text
g_j(x) = product_{t in T_r} (W_j(x)-t)^2,
P(x)   = sum_{j=1}^m g_j(x).
```

After multilinearization, `P` is nonnegative, has degree at most `2q`, and is
positive exactly when at least one block weight lies outside `T_r`.

For the lower bound, restrict all but one block to any fixed target-weight
string and average a putative certificate over permutations of the remaining
block.  The resulting symmetric multilinear polynomial has the form `R(W)`
with `deg R` no larger than the original degree.  It vanishes at all `q`
members of `T_r` and is positive at every other integer weight.

For each `t in T_r`, the open intervals `(t-1,t+1)` are pairwise disjoint and
`R(t-1),R(t+1)>0`.  If the root at `t` has even multiplicity, its multiplicity
is at least two.  If it has odd multiplicity, the sign change at `t`, together
with positivity at both neighboring integers, forces another real root in one
of `(t-1,t)` or `(t,t+1)`.  Each interval therefore contains roots of total
multiplicity at least two.  Hence `deg R>=2q`.  ∎

This calculation is important diagnostically: taking Cartesian products of
the support does not strengthen the witness-product bound at all.  Any
additive lower bound must retain shared-slice or selector information that
`ndeg_+` discards.

## An unrestricted exact theorem

**Theorem 2 (one block is exact).**  For every `r>=1`,

```text
GSE_2(S_{1,r}) = L_2(U_{S_{1,r}}) = r.
```

More generally, for all `m>=1`,

```text
r <= GSE_2(S_{m,r}) <= L_2(U_{S_{m,r}}) <= mr.
```

**Proof.**  Suppose an `ell`-bit quadratic ground-state extension exists and
form the product of all witness slices,

```text
Q(x) = product_{h in {0,1}^ell} E(x,h).
```

It is nonnegative, is positive exactly off `S_{m,r}`, and has degree at most
`2^(ell+1)` after multilinearization.  Proposition 1 gives

```text
2^(ell+1) >= 2q = 2^(r+1),
```

so `ell>=r`.

For the upper bound, use `r` hidden bits `h_{j,0},...,h_{j,r-1}` per block and
put

```text
t_j(h) = q + 2 sum_{a=0}^{r-1} 2^a h_{j,a},
E(x,h) = sum_{j=1}^m (W_j(x)-t_j(h))^2.
```

Boolean multilinearization makes this a jointly quadratic polynomial: the
visible square, visible-hidden cross term, and hidden square all have degree at
most two.  It is nonnegative and vanishes exactly when every block weight is
the target encoded by its own `r` hidden bits.  Every visible point in
`S_{m,r}` has a unique zero-energy witness.  Therefore the zero face has
uniform visible marginal `U_{S_{m,r}}`: explicitly, the joint laws proportional
to `exp(-beta E)` converge as `beta` tends to infinity to the uniform law on
the zero pairs.  This proves the upper bound on localization as well as
ground-state extension complexity.  When `m=1`, the two bounds coincide.  ∎

The family is close in spirit to symmetric pseudo-Boolean quadratization
[abcg16][abcg16], but the unique-witness statement is essential here because
the target is the *uniform distribution*, not only its support.

## Exact block-symmetric selector lower bound

Call a quadratic ground-state extension **block symmetric** if, for every
fixed hidden state `h`, the slice `E(.,h)` is invariant under independent
permutations within the visible blocks.  Let `GSE_2^blk(S)` denote the minimum
hidden count under this restriction.

Every such slice is a degree-at-most-two polynomial

```text
e_h(W_1,...,W_m)
```

on the integer box `{0,...,b}^m`.  The quadratic coefficients are common to
all slices, and the linear coefficients vary affinely with `h`, exactly as
required by the filtered Reed--Muller criterion.  The following lemma uses
only nonnegativity and is therefore stronger than a coefficient-rank test.

**Lemma 3 (one safe zero orbit per slice).**  Let `e` be a real polynomial of
total degree at most two that is nonnegative on `{0,...,4q}^m`.  If

```text
{z : e(z)=0} subset T_r^m,
```

then `e` vanishes at at most one point of `T_r^m`.

**Proof.**  Suppose `z` and `z'` are distinct zeros in `T_r^m`.  All their
coordinates are even.  Write

```text
z'-z = g v,
```

where `v` is a primitive integer vector and `g` is the gcd of the nonzero
coordinate differences.  Then `g>=2`.  Moreover every coordinate of `v` has
absolute value at most `q-1`; since all target coordinates lie between `q`
and `3q-2`, both `z-v` and `z'+v` remain in `{0,...,4q}^m`.

The univariate polynomial `rho(t)=e(z+tv)` is nonnegative at the integers
`-1,0,...,g,g+1` and vanishes at `0` and `g`.  Thus

```text
rho(t) = a t(t-g).
```

If `a>0`, then `rho(1)<0`; if `a<0`, then `rho(-1)<0`.  Hence `a=0` and the
whole line is a zero line.  Because `v` is primitive, at least one coordinate
of `v` is odd, so `z+v` is not in `T_r^m`.  This contradicts the assumed safe
zero set.  ∎

**Theorem 4 (exact block-symmetric selector obstruction).**  For all
`m,r>=1`,

```text
GSE_2^blk(S_{m,r}) = mr.
```

**Proof.**  A fixed hidden state can serve at most one of the `q^m` block-weight
orbits by Lemma 3.  Since every orbit must have a zero-energy witness,
`2^ell>=q^m`, and therefore `ell>=m log_2 q=mr`.  The energy in Theorem 2 is
block symmetric and attains equality.  ∎

In selector language, this says that fewer than `mr` bits cannot work whenever
the face exposing the selected graph is block invariant in the visible
coordinates: a successful selector must assign a distinct hidden state to
each of the `q^m` visible weight orbits.

This is also an exact zonotope statement.  Restrict the quadratic ground-state
zonotope model to the `m`-dimensional block-field subspace.  Each selected
Boolean generator image chooses a safe ground cell of one common quadratic
function of the block weights.  Lemma 3 says that such a cell meets at most one
target orbit, so an `ell`-generator affine cube supplies too few images unless
`ell>=mr`.  The binary field construction in Theorem 2 attains equality.

## What cannot be inferred by symmetry

Theorem 4 is **not** an unrestricted lower bound.  Given an arbitrary energy,
averaging a slice over the block-permutation group preserves nonnegativity, but
it preserves a zero at a target orbit only when that *same witness* vanishes on
the entire orbit.  An arbitrary selector may split one orbit among many hidden
states.  Symmetrizing the support therefore does not symmetrize its selector.

This pinpoints the missing step in the exact selector LP: one would need to
show that every low-bit coloring of all target strings forces some color class
to contain enough degree-two feature vectors to expose an entire target orbit,
or else directly aggregate the corresponding Farkas leakage certificates.  No
such statement is proved here.

## Two relaxations that are now sharply delimited

### Raw zonotope incidence forgets hidden-state activation

If the ground-state zonotope relaxation allows an arbitrary active subset of
hidden-cube points, then for every support `S subset {0,1}^n`,

```text
ZG_2(S) <= n.
```

Indeed, let `L(x)=sum_i 2^(i-1)x_i`, use the common visible quadratic
`L(x)^2`, and at hidden point `h` use field `-2L(h)L(x)`.  Up to an irrelevant
constant, the resulting objective is `(L(x)-L(h))^2` and has unique minimizer
`x=h`.  Declaring precisely the hidden points in `S` active selects `S`.  Thus an
oriented-matroid treatment of normal-cone incidence alone does not account for
the quadratic hidden-only term that must deactivate the other vertices in a
genuine extension.

### Ordinary coefficient rank is already falsified

The same singleton objectives all lie in
`span{1,L,multilinearize(L^2)}`.  Hence unfiltered coefficient rank is at most
three for an arbitrary support.  Any viable rank invariant must retain the
Boolean labels and their Reed--Muller degree, not only the span of slice
coefficients.

## Narrowed flagship conjecture

The surviving explicit question is the following.

**Conjecture (block-layer direct sum; open).**  For all `m,r>=1`,

```text
GSE_2(S_{m,r}) = mr.
```

What is known is now exact on three boundaries:

```text
unrestricted, m=1:          r
unrestricted, general m:   between r and mr
block-symmetric, general m: mr
ndeg_+ lower bound:         r, independent of m.
```

For `r=1`, the conjecture asks for `m` hidden bits on `n=8m` visible bits.  A
proof would give a linear explicit lower bound, not a superpolynomial circuit
lower bound.  It is therefore ambitious enough to mature the selector theory
while remaining below the `P` versus `P/poly` barrier.  A counterexample with
`ell<m` would be equally informative: it would exhibit a concrete
symmetry-breaking selector and show that block-product direct sum is the wrong
flagship target.

The next computational test should target `(m,r)=(2,1)`: decide whether one
hidden bit can project a quadratic face onto the two-block support.  This is a
finite selector-LP question, but the support has many points, so the search
should exploit block orbits and stabilizers rather than enumerate all
`2^(ell|S|)` selectors.

## Validation artifact

[`data/validate_selector_block_layers.py`](data/validate_selector_block_layers.py)
checks, for several small powers of two, all combinatorial hypotheses used by
Lemma 3, the exact zero set and unique-witness property of the construction,
and the degree-`2q` sign-definite certificate.  It is supplementary evidence;
the proofs above do not rely on floating-point optimization.

## Local References

[abcg16]: ../sources.md#abcg16
[dewolf03]: ../sources.md#dewolf03
