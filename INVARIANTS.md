# Invariants that retain the shared witness polynomial

## The first repair: retain the sign

If a support `S` has an `ell`-bit degree-`k` ground-state extension

```text
S = { x : exists h, E(x,h) = 0 },
E >= 0,  deg(E) <= k,
```

then multiplying the `2^ell` slices `E_h(x) = E(x,h)` gives a **nonnegative**
polynomial of degree at most `k * 2^ell` that vanishes exactly on `S`.  This
suggests the sign-definite refinement

```text
ndeg_+(f) = min { deg(p) : p >= 0 and p(x) > 0 iff f(x)=1 }.
```

Every localization therefore satisfies

```text
ndeg_+(complement(S)) <= k * 2^ell.
```

This strictly improves ordinary nondeterministic degree on parity.  If `p` is
nonnegative and positive exactly on one parity class, its full-monomial
coefficient is the alternating sum of its values.  All nonzero summands have
the same sign, so that coefficient cannot vanish and `ndeg_+(PARITY_n)=n`.
Together with Boros--Crama--Rodríguez-Heck's even-`n` construction and the
paper's corrected odd-`n` Hamming-weight square, this gives the exact identity

```text
L_2(U_even,n) = ceil(log_2 n) - 1,  n >= 2.
```

Sign is only the first piece of lost information: `ndeg_+(f) <= n`, so it can
still prove at most logarithmic latent lower bounds.  The product also forgets
the key fact that all slices come from one jointly low-degree polynomial.

## Why even nonnegative nondeterministic degree stops too early

Write

```text
E(x,h) = sum_{A,B, |A|+|B|<=k} c_(A,B) x_A h_B.
```

For each visible degree `a`, the degree-`a` coefficient vector of `E_h` is a
polynomial function of `h` of degree at most `k-a`.  In particular:

- all slices have the same degree-`k` homogeneous part;
- their degree-`(k-1)` parts vary affinely with `h`;
- their degree-`(k-2)` parts vary quadratically with `h`;
- in general, every `(k-a+1)`-fold discrete difference of the degree-`a`
  coefficient map vanishes.

This filtered dependence is the information an improved invariant should keep.

## The exact invariant: filtered facial covers

Call a nonempty set `F` **k-facial** if it is the zero set on the Boolean cube
of a nonnegative degree-at-most-`k` multilinear polynomial.  The facial cover
number `fc_k(S)` is the fewest such sets whose union is `S`.  Every ground-state
extension with `ell` hidden bits supplies at most `2^ell` slices, so

```text
L_k(D) >= GSE_k(supp(D)) >= ceil(log_2 fc_k(supp(D))).
```

This cover is deliberately coarse.  The exact slice criterion says that
`GSE_k(S) <= ell` precisely when there are nonnegative polynomials

```text
p_h(x) = sum_A c_A(h) x_A,  h in {0,1}^ell,
S = union_h {x : p_h(x)=0},
```

whose coefficient tables obey

```text
c_A in RM_R(ell, k-|A|).
```

Thus the degree-`k` coefficients are constant across slices, the
degree-`(k-1)` coefficients are affine in the witness, and so on.  This is not
merely a rank condition: the Boolean-cube labeling and every level of the real
Reed--Muller filtration are retained.

## A first relaxation: common-leading-form cover number

Call a polynomial `p` **safe for `S`** if it has degree at most `k`, is
nonnegative on the Boolean cube, and its zero set is contained in `S`.  Define
`CLF_k(S)` to be the minimum size of a family of safe polynomials whose zero
sets cover `S` and whose degree-`k` homogeneous parts are all identical.

Every `ell`-bit ground-state extension supplies at most `2^ell` such slices.
Therefore

```text
L_k(D) >= GSE_k(supp(D)) >= ceil(log_2 CLF_k(supp(D))).
```

Here `GSE_k(S)` is the support-only ground-state extension complexity.  The
common-leading-form condition is a genuine remnant of the shared witness
polynomial; an arbitrary cover by unrelated degree-`k` zero sets need not have
it.

For `k=2`, this support program meets the circuit barrier exactly.  The
quadratic NAND penalty gives

```text
L_2(U_S) <= C_NAND(S),
GSE_2(S) <= NAND verifier size,
```

where an arbitrary verifier preserves only the projected support; uniform
visible weights require constant accepting-witness multiplicity.  Thus a
strong explicit quadratic support lower bound is automatically a deterministic
or nondeterministic circuit lower bound in the corresponding formulation.

There is a hierarchy of stronger relaxations.  After fixing a Boolean-cube
labeling `p_h` of the cover, require the degree-`a` coefficient map to have
Boolean polynomial degree at most `k-a`.  Requiring this for every `a` is
equivalent to asking that the slices assemble into one total-degree-`k`
polynomial.  Requiring it only for the top one or two layers may be much easier
to lower-bound.

## The quadratic case: ground-state zonotope dimension

For `k=2`, every exposing energy has the form

```text
E(x,h) = q_A(x) + (b + W h) . x + c(h),
```

where `q_A` is a fixed quadratic form in the visible variables and `c` is
quadratic in the hidden variables.  Thus the hidden bits do not change the
visible pair interactions.  They move only the external field, through the
vertices

```text
b + W h,  h in {0,1}^ell,
```

of an `ell`-generator zonotope.

For every active witness (a slice whose minimum is zero),

```text
Z(E_h) = argmin_x [q_A(x) + (b + W h) . x].
```

Define `ZG_2(S)` to be the minimum `ell` for which there are `A`, `b`, `W`, and
an active subset `H_0` of the witness cube such that

```text
S = union_{h in H_0} argmin_x [q_A(x) + (b + W h) . x].
```

We deliberately omit the additional requirement that the minimum-value
function be representable by the quadratic `c(h)`.  This makes `ZG_2` a
relaxation and therefore a valid lower bound:

```text
L_2(D) >= GSE_2(supp(D)) >= ZG_2(supp(D)).
```

Geometrically, fixing `A` gives a regular subdivision of the Boolean cube.
Changing the external field selects cells through the normal fan, while the
witnesses are restricted to the vertices of one low-generator zonotope in
field space.  A coarser invariant drops the zonotope condition and asks for the
minimum number of cells of a single quadratic regular subdivision that safely
cover `S`; its base-two logarithm is the quadratic instance of `CLF_k`.

This formulation explains both current examples:

- In the parity construction, the fixed interaction is the square of Hamming
  weight and the zonotope lies on the all-ones field direction.  Its vertices
  select blocks of even Hamming layers.
- In the adjacent-hierarchy construction, the one hidden bit selects between
  two lower-degree block products; this is the first nontrivial filtered
  coefficient variation at locality `k`.

## Shared structure gives an exponential Shannon bound

The shared polynomial already proves much more for a random support than the
witness-product degree can see.

Let `F(n,k,L)` be the collection of supports with ground-state extension
complexity at most `L`.  Put

```text
N = n + L,
d_k(N) = sum_{j=0}^k binom(N,j).
```

Then

```text
|F(n,k,L)| <= (L+1) * 2^(O_k(N^(k+1))).
```

To see this, fix a latent count `ell <= L`.  The zero set of a nonnegative
degree-`k` energy is the vertex set of a face of the order-`k` marginal
polytope.  A face is determined by an affine basis of at most
`d_k(n+ell)` vertices.  There are therefore at most

```text
sum_{i=0}^d binom(2^(n+ell), i) <= 2^(O_k((n+ell)^(k+1)))
```

faces.  Projecting their vertex sets to the visible coordinates cannot
increase the count, and summing over `ell` gives the claim.

Since `d_k(N) = O_k(N^k)`, for every fixed `k` there is a constant `c_k > 0`
such that a uniformly random nonempty support `S` satisfies

```text
GSE_k(S) > c_k * 2^(n/(k+1)),
L_k(U_S) > c_k * 2^(n/(k+1))
```

with probability `1 - 2^(-Omega(2^n))`.  Thus almost every flat distribution
has exponentially large localization complexity.  The nondeterministic-degree
bound can never show this because nondeterministic degree is at most `n`.

This is an existence theorem, not an explicit lower bound.  Its role is to
show that the filtered support invariant is exponentially nontrivial even
though explicit instances meet the NAND-circuit barrier.

## Concrete next tests

1. **Quadratic small-instance census.**  Enumerate the cells of quadratic
   regular subdivisions for small `n`, compute the common-Hessian cover number
   of each support, and look for structured maximizers rather than random ones.
2. **Zonotope obstruction.**  Lower-bound the number of generators required for
   a zonotope whose selected vertices meet prescribed normal cones.  Oriented
   matroid and sign-rank relaxations are plausible tools.
3. **Explicit hitting families.**  Construct a simple support whose complement
   hits every large degree-`k` ground set with a fixed leading form.  This would
   force a large `CLF_k` cover number.
4. **Filtered coefficient ranks.**  Define ranks of the discrete-difference
   tensors of the degree-`a` slice coefficients.  These interpolate between
   common-leading-form cover number and the full witness parametrization.
5. **Circuit relevance gate.**  Treat the NAND synthesis as a barrier, not an
   afterthought: a quadratic flat-support lower bound also lower-bounds its
   recognizer.  For a genuinely distributional separation from circuit
   complexity, use full-support weights; for a support lower bound, state the
   resulting circuit consequence explicitly.

The key strategic distinction is now clear: nondeterministic degree measures
the product of the witness slices, while the proposed invariants measure how
those slices can coexist inside one filtered low-degree family.

## A boundary-safe algebraic certificate

The marginal ideal now gives an exact lower-bound certificate for probability
tables, including lifts whose joint law lies on a support face. For fixed
`n,k,ell`, parameterize an unnormalized positive order-`k` joint table by

```text
q(x,h) = product_A t_A^(product_{i in A}(x,h)_i),  1 <= |A| <= k,
```

sum over `h`, and take the projective Zariski closure `V_(n,k,ell)` of the
visible vectors. Then

```text
L_k(D) <= ell  =>  [D] in V_(n,k,ell).
```

The implication survives boundary lifts because every extended hierarchical
table is a limit of positive Gibbs tables. The homogeneous ideal of `V` is
computable by eliminating the `t_A`; any `F` in that ideal with `F(D) != 0`
certifies `L_k(D)>ell`. If `d_k(n+ell)<2^n`, dimension guarantees a nonzero
such `F`. This is the certificate form of the paper's generic dimension
argument.

Raw tensor ranks cannot replace this quotient. A pairwise Gibbs table
`exp(sum_i lambda_i u_i v_i)` has zero latent bits but full balanced-flattening
rank, and the zero mask of `sum_i(u_i-v_i)^2` is an identity matrix. Any useful
quadratic rank must first quotient the visible pairwise Gibbs gauge and then
take orbit closure.

## Zero-temperature degree-reduction invariant

For real-valued `f`, let `aux_k(f)` be the fewest hidden bits in a representation

```text
f(x) = min_h g(x,h),  deg(g) <= k.
```

For the full-support Gibbs ray `D_(f,t)(x) proportional to t^f(x)`, the paper
now proves

```text
liminf_(t -> 0) L_k(D_(f,t)) >= aux_k(f).
```

Finitely many support faces let a subsequence of small localizations share one
fixed face. Scaled log-sum-exp converges to the fiberwise maximum, and the
tropical image of the degree-`k` restriction space under that maximum is a
closed finite union of polyhedral cones, so the limit is attained by one
degree-`k` polynomial on the face; a large multiple of the exposing energy then
converts the face-constrained minimum into an ordinary degree-`k` reduction.
No curve selection or Puiseux expansion is needed. This is the first
weight-sensitive lower-bound transfer that works on full support.

Two calibrations are now available:

- noisy parity gives an explicit `Omega(log n)` full-support quadratic lower
  bound at sufficiently low temperature;
- the superincreasing energy `f(x^(i))=B^i`, with
  `B>1+d_k(n+ell)^(d_k(n+ell)/2)`, escapes every degree-`k` witness-evaluation
  subspace by an augmented-minor and Cauchy-root argument. Choosing `ell` just
  below the dimension threshold gives explicit, though extremely
  ill-conditioned, Gibbs rays with optimal `Theta_k(2^(n/k))` complexity.

## Full support: interaction dimension rather than ground sets

When `D` has full support, every support invariant is zero.  With no latent
variables, however, `D` is `k`-local exactly when the multilinear expansion of
`log D` has degree at most `k`.  Hidden variables express higher-order log
interactions through marginalization.

The generic obstruction is parameter dimension.  On `N` total bits, all
`k`-local distributions form a finite union over support faces of analytic
families with at most `d_k(N)-1` effective parameters.  Their visible marginals
cannot fill the `2^n-1` dimensional interior probability simplex unless

```text
d_k(N) >= 2^n.
```

Thus almost every full-support distribution has

```text
L_k(D) >= Omega_k(2^(n/k)) - n.
```

For positive quadratic lifts there is a more concrete relaxation.  Factoring
out the visible quadratic potential writes the marginal tensor as a mixture of
at most `2^ell` positive product tensors.  This suggests minimizing nonnegative
tensor rank after arbitrary pairwise Gibbs rescaling.  Boundary lifts can evade
that particular relaxation, so a useful explicit invariant must either control
all support faces or prove that boundary lifts do not help for the chosen
distribution family.
