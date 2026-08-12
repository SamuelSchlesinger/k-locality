# The block-parity cubic fiber

This note isolates a structured submatrix of the profile matrix `M_L`.  The
formalization now closes it by finite counting and canonical exhaustive
search: for `q>=64` and `L=q^2`, it produces a signed trade and a separating
test.  That closure is deliberately weaker than the usual complexity-theoretic
meaning of explicit—the selected objects have no known efficient or
low-description construction.  The structural purpose of this note is to
explain the exact Fourier description that may support such a stronger result.

## 1. A doubly exponential cubic-moment fiber

Let

```text
A = {0,1}^q,
Z = {0,1}^4,
N = |A| = 2^q.
```

Use visible states `(r,a,z)`, where `r` is one reserved marker bit.  All states
below have `r=0`, so none is the all-ones filler from the uniform cubic
construction.

For every Boolean function `s : A -> {0,1}`, define

```text
C_s = {(0,a,z) : parity(z) = s(a)}.
```

There are `2^N` such candidates, each of size `8N`.

**Proposition 1.** All `C_s` have the same visible moments of degree at most
three.

**Proof.** Fix `a` and a monomial scope.  Its part in the four `z`
coordinates has size at most three.  After fixing those coordinates to one,
at least one `z` coordinate remains free, and that last coordinate determines
the required parity.  Hence the number of extensions is the same for even and
odd parity.  Multiplication by the fixed value of the `a`-part does not change
the conclusion.  Summing over `a` proves the claim.  The marker coordinate is
always false.  QED.

Thus the `2^N` columns indexed by `s` lie in a single visible block of `M_L`.
This is a concrete, highly structured replacement for the arbitrary large
fiber used by the pigeonhole proof.

## 2. Exact Boolean-test kernel

Use another block-parity function `t` as the Boolean test.  Within the block
indexed by `a`, the selected parity halves agree in all eight points if
`s(a)=t(a)` and are disjoint otherwise.  Therefore

```text
|C_s intersect C_t| = 8 * |{a : s(a)=t(a)}|
```

and

```text
K(t,s) = 2^|C_t intersect C_s|
       = 256^(N - distance(s,t)).
```

Consequently the restricted `K` is the `N`-fold tensor power of

```text
K_1 = [[256, 1],
       [1, 256]].
```

This is the binary Hamming association scheme.  In the Walsh basis
`chi_U(s)=(-1)^|U intersect s|`, its eigenvalue is

```text
lambda_U = 257^(N-|U|) * 255^|U|.
```

Every eigenvalue is nonzero.  In particular, restriction to this fiber loses
none of the interpolation power of the full binary-subset transform.

## 3. One-hidden-bit Fourier decomposition of `M_1`

For one hidden bit, factor the common visible cubic monomial and write `b_x`
for the visible quadratic toric monomial multiplying the hidden-one state.
The column indexed by `s` becomes

```text
P_s = product_a E_(a,s(a)),

E_(a,e) = product_{z : parity(z)=e} (1+b_(a,z)).
```

Let `Phi` be the linear map sending the basis vector indexed by `s` to `P_s`.
An integer vector is a one-hidden marginal trade on this fiber exactly when it
lies in `ker(Phi)`.

The Walsh transform of `Phi` factorizes exactly.  For `U subseteq A`,

```text
Phi(chi_U)
  = product_{a notin U} (E_(a,0)+E_(a,1))
    * product_{a in U} (E_(a,0)-E_(a,1)),
```

up to the common normalization convention for the Walsh transform.  This is
an exact decomposition of the structured column map into Fourier-indexed
products.  The remaining algebraic question is to find a relation among these
products and then control its pairing with one prescribed row of the Hamming
kernel.

## 4. Genuine symmetry versus apparent symmetry

The literal fixed-filler matrix `M_L` has the following evident automorphisms.

- `S_n` permutes visible coordinates.  It fixes the all-ones filler, permutes
  candidates, and permutes visible/mixed profile coordinates.
- `S_L` permutes hidden coordinates and corresponding profile coordinates.
- Complementing a hidden coordinate induces an invertible integral change of
  profile coordinates: a count containing the flipped coordinate becomes the
  lower-scope count minus the old count.  Together with `S_L`, this gives the
  hidden hyperoctahedral action on profile rows.

Visible bit flips preserve the global cubic marginal model but move the chosen
filler.  They are therefore projective symmetries after the common filler
factor is removed, not literal column automorphisms of the fixed presentation.

Within the block-parity fiber, the literal stabilizer contains `S_q x S_4`:
it permutes the prefix coordinates and the four parity coordinates.  The much
larger symmetric group on the `N` blocks is **not** a symmetry of `M_L`.
Assuming it would incorrectly turn the Fourier-level decomposition into a
complete Hamming-scheme decomposition.

## 5. What this accomplishes and what remains

The original problem

```text
find T and b with M_L b = 0 but k_T b != 0
```

has, on this fiber, become

```text
find a relation among the Fourier products Phi(chi_U),
then find a prescribed t whose nonzero Walsh weights do not annihilate it.
```

The test kernel is completely diagonalized.  A coarse count of complete
cubic joint profiles now proves that, for `L=q^2` and `q>=64`, two distinct
subsets of columns collide.  The Lean construction chooses the first such
pair, takes the difference of their indicators, and then chooses the first
test detected by the invertible agreement tensor.  This resolves the literal
finite witness problem, but only by repackaging the counting proof as an
astronomical exhaustive search.

The next useful target is therefore to identify a representation type of the
`S_q`-equivariant span of the products above which is absent from `im(Phi)` and
is hit by a uniformly efficient, low-description truth table `t_q`.

## 6. Executable checks

`analyze_block_parity_fiber.py` checks the common cubic profile, the exact
intersection formula, and the complete Walsh spectrum over the integers.  It
can also estimate the rank of the corresponding full toric marginal columns
over a finite field for small instances.

```text
sage -python research/analyze_block_parity_fiber.py --prefix-bits 2
sage -python research/analyze_block_parity_fiber.py --prefix-bits 3 --samples 280
```

The finite-field rank is discovery evidence only.  The integer profile and
kernel identities are exhaustive finite checks for the requested small `q`.

## 7. A useful degree filtration

For one hidden bit, give every quadratic toric monomial `b_(a,z)` degree one.
Then

```text
E_(a,0) + E_(a,1) = 2 + terms of positive degree,
E_(a,0) - E_(a,1) = g_a + terms of degree at least two,

g_a = sum_z (-1)^parity(z) b_(a,z).
```

It follows that the least homogeneous degree of `Phi(chi_U)` is `|U|`, and
its degree-`|U|` part is

```text
2^(N-|U|) * product_(a in U) g_a.
```

Consequently, in any relation among the Fourier products, the terms having
minimum `|U|` must already give a relation among the products of the much
simpler functions `g_a`.  This is a genuine triangular reduction; it does
not by itself produce the required relation.

Conditioned on a prefix `a`, a quadratic toric monomial has the form

```text
b_(a,z) = c_a * d_z * product_(r=1)^4 u_r(a)^z_r,
```

where `c_a` is a quadratic toric monomial in `a`, each `u_r(a)` is a product
toric monomial in `a`, and `d_z` contains only suffix parameters.  Hence

```text
g_a = c_a * sum_z (-1)^parity(z) d_z product_r u_r(a)^z_r.
```

After removing `c_a`, the tensor `(g_a)_a` has CP rank at most 16.  Ordinary
flattening minors therefore become a plausible source of equations.  The
important catch is that `c_a` contains arbitrary pair interactions among the
prefix bits.  Entrywise multiplication by this quadratic toric tensor can
make those flattenings full rank.  Any successful minor construction must
cancel the complete quadratic prefix profile, not merely the unary profile.

## 8. Why one-hot block labels do not solve the symmetry problem

There is a tempting way to make the apparent `S_N` block symmetry literal:
encode block `a` by the one-hot prefix state `e_a`.  Coordinate permutations
then realize every permutation of the blocks.  Unfortunately this also gives
the cubic joint model private mixed parameters for every block.

Already with one hidden bit one may specialize the quadratic toric factor to

```text
b_(a,z) = u_a * product_(r=1)^4 v_(a,r)^z_r,
```

using the scopes `{a,h}` and `{a,z_r,h}`.  The variables belonging to
different `a` are disjoint.  For a fixed block, the two polynomials

```text
E_(a,e) = product_(parity(z)=e) (1+b_(a,z))
```

are linearly independent: they have the same constant term, while the
coefficient of `u_a` in their difference is

```text
product_r (1-v_(a,r)),
```

up to sign, and is nonzero.  Tensoring these independent pairs over all
blocks makes every product column `product_a E_(a,s(a))` independent.  The
same specialization embeds into every positive hidden-bit budget by killing
the extra hidden states.

Thus the one-hot version has the desired full `S_N` symmetry but has no
column relation at all.  The binary-prefix version shares parameters strongly
enough that relations eventually exist, but its literal symmetry shrinks to
`S_q`.  This symmetry-versus-private-parameters tradeoff is a real structural
barrier, not an artifact of the small computations.

## 9. Formal status

`KLocality/BlockParityFiber.lean` checks the eight-point parity classes and
their common cubic moments.  `KLocality/BinaryAgreementTransform.lean` checks
the agreement tensor's integer inverse, Walsh spectrum, and generic product
factorization.  `KLocality/BlockParityMatrix.lean` and
`KLocality/BlockParityCounting.lean` define the complete profile matrix and
prove the `q^2`-hidden collision for `q>=64`.
`KLocality/BlockParityCanonicalTrade.lean` and
`KLocality/BlockParityAgreementWitness.lean` define the first collision,
the nonzero vector `b_q`, and the first detecting test `t_q`.
`KLocality/BlockParityCertificate.lean` compiles the result into the
boundary-safe certificate API and proves `LC_3(D_q)>q^2` for a full-support
two-level rational law on `q+5` visible variables.  The remaining open claim
is efficient explicitness, not finite existence or effective enumerability.
