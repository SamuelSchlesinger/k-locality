# Hierarchical and marginal models

[Back to the research map](../index.md)

## Executive conclusion

The statistical-model literature contains three results that transfer cleanly
to localization complexity.

1. The closure of a finite exponential family is stratified by faces of its
   marginal polytope, and each stratum is the trace exponential family on the
   corresponding facial support.  For the binary order-`k` feature map this is
   exactly the paper's face--Gibbs characterization of `k`-local distributions
   [rka11][rka11] [mp10][mp10].
2. Neighborliness of binary hierarchical marginal polytopes implies a useful
   zero-hidden-bit theorem now incorporated in the draft: every distribution
   supported on at most `2^k - 1` Boolean strings is already `k`-local
   [kahle10][kahle10].
3. Published softplus covering theorems imply explicit upper bounds on
   `L_2`, including

   ```text
   L_2(D) <= sum_{j=3}^n D(n,j) <= 2^(n-1) - n
   ```

   for every distribution on `n` bits, where `D(n,j)` is a standard covering
   number.  The source states approximation by positive pairwise models; in a
   finite state space, compactness upgrades this to exact representation by a
   boundary `2`-local lift [montufarrauh17][montufarrauh17].

These are primarily upper-bound and structural transfers.  The dimension
literature supplies the standard method behind the draft's generic
full-support lower bound, but lower bounds proved for restricted Boltzmann
machines do **not** lower-bound unrestricted localization complexity.  Nor do
generic full-support lower bounds imply Boolean support-circuit lower bounds:
the support circuit is constant one.

For circuit-level implications, see the sibling [circuit transfer
audit](../circuits/index.md).

## Model dictionary

### Binary hierarchical models

Let `Delta` be a simplicial complex on `N` binary variables.  A hierarchical
model uses log-potentials that are arbitrary functions on scopes in `Delta`.
On the Boolean cube, its row space is equivalently spanned by the monomials

```text
y_A = product_{i in A} y_i,    A in Delta.
```

Thus the complete order-`k` complex

```text
Delta_k = {A subseteq [N] : |A| <= k}
```

has feature rank

```text
d_k(N) = sum_{j=0}^k binom(N,j),
```

and positive-model dimension `d_k(N)-1`.  This agrees exactly with the
paper's degree-at-most-`k` feature convention.  For a general binary complex,
the rank is `|Delta|` (including the constant feature).

The terminology differs at the boundary:

- Statistical papers commonly reserve *hierarchical model* for the strictly
  positive exponential family.
- The paper's `k`-local distributions include zeros.  They are exactly the
  topological closure, or *extended* order-`k` hierarchical model.

This closure distinction is essential.  Approximation by positive Gibbs
distributions is not an approximation notion in localization complexity; its
limit is itself an admissible exact `k`-local distribution.

### Hidden variables and cost

Localization complexity counts **binary hidden coordinates**, not free
parameters and not abstract hidden variables.

- Montufar and Rauh's principal representation theorems use binary hidden
  units, so their number `h` transfers literally to `h` hidden bits
  [montufarrauh17][montufarrauh17].
- A hidden variable with `q` categories does not cost one bit.  A
  locality-preserving conversion uses `q-1` Boolean indicators, with the
  all-zero word as the baseline category and the quadratic face penalty
  `sum_{a<b} h_a h_b` enforcing at most one active indicator.  An interaction
  involving `r` categorical variables then expands into Boolean monomials of
  degree at most `r`, while the at-most-one penalty is quadratic. Hence the
  encoded Boolean locality is at most `max(r,2)`, and the safe cost is
  `sum_i(q_i-1)` bits.
- A binary encoding using `ceil(log_2 q)` bits saves coordinates but does not
  preserve interaction rank: an arbitrary function of one categorical state
  can have Boolean degree `ceil(log_2 q)`, and excluding unused codewords can
  require additional high-order terms.

### Pairwise models are not all the same

The following inclusions must not be blurred:

```text
RBM
  subseteq pairwise model with visible-visible interactions
  subseteq unrestricted pairwise model on all visible and hidden bits.
```

An RBM has visible and hidden biases and visible--hidden edges, but no
visible--visible or hidden--hidden interactions.  Either of the first two
models gives a valid quadratic localization upper bound, because it is a
submodel of the third.  A lower bound for either restricted subclass does not
give a lower bound for unrestricted `L_2`.

## Exact closure and support results

### Facial supports and trace families

For a finite state space `X`, a positive reference measure `q`, and a feature
matrix `A` whose row span contains the constants, Rauh, Kahle, and Ay prove:

- **Theorem 4:** a distribution `p` lies in the closure of `E_{q,A}` exactly
  when

  ```text
  p^(u+) q^(u-) = p^(u-) q^(u+)    for every u in ker(A).
  ```

- **Proposition 8:** a set `F subseteq X` is facial for the convex support if
  and only if some distribution in the closure has support exactly `F`.
- **Theorem 18:** facial supports are characterized by signed circuits
  `(M,N)` of `A`: `M subseteq F` iff `N subseteq F` for every signed circuit
  [rka11][rka11].

Malago and Pistone give the complementary explicit trace statement.  Their
Theorem 1 says that a defective-support limit has exposed support and belongs
to the trace of the original exponential family on that support; Theorem 2
says every trace distribution on an exposed support is such a limit
[mp10][mp10].  Csiszar and Matus, Theorem 2, prove a more general variation-
closure theorem using accessible faces; for a full finite exponential family,
all polytope faces are accessible, so it specializes to the same finite
face-stratification [cm05][cm05].

**Classification: Exact transfer.**  Take `A=chi_k`, `q=1`.  A facial set is
the zero set of an exposing linear functional on the feature vectors, hence
the zero set of a nonnegative degree-at-most-`k` pseudo-Boolean polynomial.
The trace-family statement says that the logarithm of the probability mass is
another degree-at-most-`k` polynomial on that zero set.  This is precisely the
face--Gibbs theorem, including both its support and weight clauses.

The signed-circuit criterion is an exact test for `L_k(D)=0`, but by itself it
does not quantify how many hidden bits are needed after projection.  Treating
it as an `L_k` lower bound would be a **non-transfer** until one develops an
oriented-matroid extension invariant that respects the Boolean product
structure of the witness space.

### Neighborliness gives a sparse-support theorem

Let `g` be the smallest cardinality of a non-face of a simplicial complex
`Delta`.  Kahle's Theorem 14 states that its marginal polytope is
`(2^(g-1)-1)`-neighborly; equivalently, **every** probability distribution
`p` with

```text
|supp(p)| < 2^(g-1)
```

belongs to the extended hierarchical model [kahle10][kahle10].  The published
erratum corrects only claims in the later multiinformation remark, not
Theorem 14 [kahle12][kahle12].

For the complete order-`k` complex with `k<N`, the smallest non-face has size
`k+1`.  Therefore

```text
|supp(D)| <= 2^k - 1    implies    L_k(D) = 0.
```

**Classification: Exact transfer.**  This is stronger than saying that some
distribution with that support is `k`-local: the theorem includes every choice
of positive weights on the support.

There is an exact circuit corollary: every such support is the zero set of one
nonnegative degree-`k` polynomial, so it has a deterministic exact-threshold-
of-monomials representation.  With ordinary Boolean gates, however, this does
not beat the elementary DNF bound for an arbitrary sparse set.  It is a clean
representation theorem, not presently a new circuit upper bound.

## Hierarchical models as pairwise marginals

Montufar and Rauh identify a hidden binary unit with a softplus term

```text
log(1 + exp(c + w dot x))
```

in the visible free energy.  Their covering results control several
multilinear coefficients with one such unit [montufarrauh17][montufarrauh17].

### Exact source statements

- **Theorem 8:** if the interactions of a binary hierarchical complex `S` of
  size at least two can be covered, in reverse-inclusion order, by `h` star
  tuples or eligible edge pairs, then every distribution in `E_S` can be
  approximated arbitrarily well by an RBM with `h` binary hidden units.
- Let `D(v,j)` be the minimum number of star tuples covering all `j`-subsets.
  **Lemma 9** identifies

  ```text
  D(v,j) = C(v, v-j+1, v-j),
  ```

  a classical covering number, and includes the simple bound
  `D(v,j) <= binom(v-1,j-1)`.
- **Theorem 11:** every distribution in the binary `k`-interaction model is
  approximable by an RBM with

  ```text
  U(v,k) = sum_{j=2}^k D(v,j)
  ```

  hidden binary units.
- **Corollary 14:** after allowing direct visible pair interactions, the count
  improves to

  ```text
  B(v,k) = sum_{j=3}^k D(v,j).
  ```

  In particular, `B(v,v) <= 2^(v-1)-v` by the simple covering bound
  [montufarrauh17][montufarrauh17].

### Why approximation becomes an exact localization

Suppose `D` lies in the closure of the source hierarchical model.  Choose
positive `D_t -> D`, and for each `t` choose a positive pairwise joint model
`Q_t` whose visible marginal is within `1/t` of `D_t`.  The joint probability
simplex is compact, so a subsequence converges to `Q`.  Its visible marginal
is exactly `D`, and `Q` belongs to the closure of the pairwise exponential
family.  Hence `Q` is exactly `2`-local under the paper's definition.

Consequently:

```text
D in closure(E_S) and S has an h-cover     => L_2(D) <= h,
D in closure(E_k)                          => L_2(D) <= B(n,k),
arbitrary D on n visible bits              => L_2(D) <= B(n,n).
```

This is the sharpest direct bound imported from the audited restricted
pairwise/hierarchical literature. It is superseded for unrestricted
localization by the corpus's [balanced block-feature
lift](../quadratization/index.md#balanced-k-block-lift), which gives
`L_2(D)=O(2^(n/2))`.

For sparse distributions, the paper's existing `L_2(D)<=|supp(D)|` can be
better, so the universal statement should be recorded as the minimum of the
two bounds.

**Classification: Closure transfer.**  The sources prove density in a visible
marginal model, not finite-parameter equality.  The compactness argument is
what turns that statement into an exact localization theorem.  No conversion
of hidden-unit count is needed because the source units are binary.

### Circuit consequence

Combining an `h`-bit quadratic lift with the paper's support compilation gives

```text
NSize(supp D) <= h + O((n+h)^4 log(n+h)).
```

A deterministic circuit can enumerate all witnesses, at an additional
`2^h` factor.  For `D` already in an order-`k` hierarchical closure, its facial
support also has a direct deterministic exact-threshold circuit using the
order-`k` features; that route may be smaller than witness enumeration.

These are **exact transfers**, but the universal numerical bounds are not
competitive with truth-table/DNF circuits.  Their likely value is for a
structured interaction complex whose star cover `h` is much smaller than its
raw number of high-order interactions.

## Dimension results and their limits

### The transferable dimension argument

For a marginal model with joint sufficient-statistics matrix `F`, Montufar
and Morton's Definition 2 and Proposition 4 give

```text
dim(M_F) <= rank(F)-1,
```

with a tropical Jacobian rank as a lower bound
[montufarmorton17][montufarmorton17]. Their
Proposition 10 gives the familiar dimension of a categorical hierarchical
model; in the binary complete order-`k` case it is `d_k(N)-1`.

Combine this with the finite facial decomposition above.  Every boundary
stratum has at most the same dimension, and there are finitely many faces.
For `N=n+ell` total binary variables, visible marginals of all `k`-local joint
distributions therefore occupy a measure-zero subset of the visible simplex
whenever

```text
d_k(n+ell) < 2^n.
```

This is exactly the method behind the draft's generic full-support lower
bound `L_k(D)=Omega_k(2^(n/k))-n`.

**Classification: Exact transfer of method.**  Proposition 4 is stated for
the positive marginal model; the extension across all boundary supports uses
the finite face stratification.  The resulting localization theorem is a
short corollary of those ingredients, not a consequence of RBM dimension
alone.

### Algebraic marginal certificates

The dimension argument has an exact algebraic form. Let `V_(n,k,ell)` be the
projective Zariski closure of the visible marginal map from the order-`k` toric
model on `n+ell` bits. Toric graphical-model closures and their boundary
supports are standard [geiger06][geiger06]. Then

```text
L_k(D) <= ell  =>  [D] in V_(n,k,ell),
```

including boundary lifts. The homogeneous ideal is the elimination kernel of

```text
p_x -> s * sum_h product_A t_A^(product_{i in A}(x,h)_i),  1<=|A|<=k.
```

Thus any eliminant `F` with `F(D)!=0` certifies `L_k(D)>ell`. When
`d_k(n+ell)<2^n`, dimension guarantees a nonzero integer eliminant. This is an
**exact transfer of algebraic method** and upgrades the measure-zero statement
to a checkable, if potentially enormous, certificate.

The certificate is effective along a full-support Gibbs ray.  If `F` is
homogeneous of degree `Delta`, enumerate the cube as `x_0,...,x_(2^n-1)` and
set

```text
f(x_i)=(Delta+1)^i.
```

Distinct monomials of `F` acquire distinct powers after the substitution
`p_(x_i)=t^f(x_i)`.  Factoring the least power of `t` leaves an integer
polynomial with nonzero constant term, and an elementary coefficient bound
computes a rational `tau>0` on which it cannot vanish.  Hence

```text
L_k(D_(f,t))>ell for every real 0<t<tau.
```

This strengthens “generic” to an effective exact certificate and an effective
cold interval.  It applies to this eliminant-defined ray, not automatically to
every separate zero-temperature construction.

### Tropical marginalization: source result and new boundary step

Pachter and Sturmfels identify tropicalization of statistical-model
polynomials with replacing sums by minima or maxima in inference
[pachtersturmfels04][pachtersturmfels04].  Cueto, Morton, and Sturmfels develop
the tropical RBM parameterization and its relation to inference functions
[cuetomortonsturmfels10][cuetomortonsturmfels10].  Montufar and Morton's
dimension work supplies the corresponding tropical Jacobian method for
Kronecker-product marginal models [montufarmorton17][montufarmorton17].

These sources justify the positive-stratum `sum -> min` operation.  They do
not by themselves prove the paper's lower-bound transfer across arbitrary
boundary localizations.  The new step is to choose a semialgebraic family of
lifts, stabilize one exposed support face, take valuations on that face, and
then add a sufficiently large multiple of its exposing energy to remove the
face-constrained minimum.  This yields the exact inequality

```text
liminf_(t->0) L_k(D_(f,t)) >= aux_k(f).
```

**Classification: Established tropical operation plus a new boundary-safe
transfer.**  It should not be described as a direct corollary of tropical
statistics.

### Exact recognition for rational tables

For a densely listed rational table (all `2^n` entries, zeros included), the
face--Gibbs normal form can be
encoded by polynomial constraints: one nonnegative degree-`k` energy exposes
the joint support, complementarity makes the support exact, and positive
monomial parameters encode Gibbs weights on that face.  Expanding the
`2^(n+ell)` lifted states gives an existential-real formula of size
`poly(||D||_bit+2^(n+ell)d_k(n+ell))`.  Thus, for fixed `k,c` and `ell<=cn`,
recognition lies in `exists-R`.

At `ell=0`, faciality is a rational LP and the Gibbs condition is a finite set
of rational power-product equalities.  Those equalities are decidable in
polynomial time by gcd refinement [etessami14][etessami14], so exact
zero-latent recognition is in deterministic `P`, uniformly in `k<=n`.
Neither statement applies without qualification to sampled, approximate,
algebraic, sparsely encoded, or succinctly represented distributions.

### Mixture and secant-rank relaxation

Conditioning a `k`-local joint law on a positive-mass hidden assignment leaves
a `k`-local visible law. Hence, if `hmr_k(D)` is the minimum number of closed
order-`k` hierarchical components in a mixture for `D`,

```text
hmr_k(D) <= 2^L_k(D),
L_k(D) >= ceil(log_2 hmr_k(D)).
```

The algebraic border rank with respect to the order-`k` toric variety is a
further relaxation and supplies secant-ideal certificates. Its generic bound
is only `L_k(D)>=n-O_k(log n)`, much weaker than the full marginal-model
dimension theorem: independent mixture components forget the filtered
dependence of all witness slices on one shared hidden polynomial. Raw tensor
flattenings are already maximal for some zero-latent pairwise Gibbs models, so
they cannot be used without quotienting the visible Gibbs gauge.

### Facial covers and coherent hidden slices

For a support `S`, the paper now isolates the exact support-only extension
measure `GSE_k(S)`. Fixing a hidden assignment in a nonnegative degree-`k`
energy produces a `k`-facial visible zero set, so

```text
GSE_k(S) >= ceil(log_2 fc_k(S)),
```

where `fc_k(S)` is the minimum number of `k`-facial sets covering `S`. More
importantly, the slices are not arbitrary faces: if
`E(x,h)=sum_A c_A(h)x_A`, then

```text
c_A in RM_R(ell,k-|A|).
```

This filtered real Reed--Muller dependence is necessary and sufficient for the
slices to assemble into one total-degree-`k` energy. It supplies the missing
extension invariant that signed circuits and independent secant components do
not retain. A direct face count gives
`GSE_k(S)=Omega_k(2^(n/(k+1)))` for almost every support, but produces no
explicit family.

### Results confined to Kronecker and RBM architectures

Montufar and Morton's Theorem 24 gives Hamming-ball conditions under which a
Kronecker-product hierarchical marginal model has its expected tropical
dimension.  Corollary 26 proves that a binary RBM with `n` visible and `m`
hidden units has dimension

```text
min(2^n - 1, (n+1)(m+1) - 1).
```

[montufarmorton17][montufarmorton17]

**Classification: Restricted-model result.**  For RBMs this yields the
parameter-count obstruction `m = Omega(2^n/n)` to full dimensionality.  It
does not imply `L_2(D)=Omega(2^n/n)`: an unrestricted quadratic lift has
roughly `(n+ell)^2/2` parameters and permits visible--visible and
hidden--hidden interactions.  Its generic hidden-bit obstruction is only on
the `2^(n/2)` scale.

The general Kronecker theorem also does not automatically preserve a total
interaction rank.  If its visible factor uses scopes of size at most `a` and
its hidden factor scopes of size at most `b`, a tensor-product feature may
involve `a+b` total variables.  A localization transfer is therefore
**conditional** on translating the factor row spaces into a stated total
Boolean locality bound and then converting categorical hidden states to
bits.

Two further non-transfers are important:

- Full dimension does not mean the closure is the whole simplex, so expected
  dimension cannot be used as a localization upper bound.
- A lower bound for a subclass such as an RBM, mixture model, or
  conditionally independent hidden model cannot lower-bound `L_k` unless one
  first proves that every optimal `k`-local lift can be normalized into that
  subclass without adding hidden bits.

## Transfer ledger

| Candidate | Classification | Localization consequence | Circuit consequence |
|---|---|---|---|
| Finite closure equals union of facial trace families | Exact transfer | Face--Gibbs characterization | One deterministic exact-threshold support test; existential test after projection |
| Signed-circuit description of facial supports | Exact for `L_k=0`; non-transfer for hidden-bit lower bounds | Combinatorial zero-latent test | No membership-circuit lower bound by itself |
| Kahle neighborliness theorem | Exact transfer | `|supp D|<=2^k-1 => L_k(D)=0` | Exact-threshold representation, but no evident improvement over DNF |
| Soft-plus/star-cover representation | Closure transfer | Explicit `L_2` upper bounds | Structured nondeterministic upper-bound schema |
| General marginal-model dimension bound | Exact transfer of method | Generic full-support lower bound | Non-transfer to support-circuit lower bounds |
| Marginal-ideal eliminant plus base-coded Gibbs ray | Exact effective certificate | Computable rational cold interval with `L_k>ell` | None for support circuits |
| Tropical marginalization | Established operation plus new boundary-safe transfer | `liminf L_k(D_(f,t)) >= aux_k(f)` | Only through a separately established support or optimization consequence |
| Exact rational-table recognition | Exact algorithmic characterization | Linear hidden budgets in `exists-R`; zero hidden bits in `P` | No hardness consequence |
| Filtered facial-cover criterion | New exact support invariant built from facial strata | Characterizes `GSE_k(S)<=ell`; exponential almost-all-supports bound | Shannon-style existence only; explicit quadratic bounds imply circuit lower bounds |
| Expected dimension of binary RBMs | Restricted-model result | RBM lower bound only | No lower bound for unrestricted localization or circuits |
| Categorical hidden-variable theorem | Conditional transfer | Costs `sum(q_i-1)` bits at locality at most `max(r,2)` under indicator encoding | Depends on the encoded locality and witness cost |
| Full-dimensional marginal model | Non-transfer to universality | Does not imply finite `L_k` upper bound at that hidden count | No circuit conclusion |

## Audit boundaries

The theorem numbers and formulas above were checked against the primary paper
PDFs.  Three claims are intentionally narrower than a full novelty statement:

- The compactness step from approximation to exact localization is an
  elementary corollary supplied here; it is not labeled as a theorem in
  Montufar--Rauh.
- `B(n,n)` is the strongest universal quadratic bound imported directly from
  the audited restricted pairwise literature; the derived balanced-block lift
  is asymptotically much stronger for unrestricted localization.
- The `q-1` indicator conversion for categorical variables is an elementary
  model translation, not a theorem attributed to the cited papers.  Any use
  of a logarithmic binary encoding requires a new locality calculation.

## Integration status

| Item | Draft status |
|---|---|
| Attribute face/trace geometry to the exponential-family literature | Incorporated |
| Add Kahle's `2^k-1` sparse-support theorem | Incorporated |
| State the Montufar--Rauh closure transfer and restricted architecture | Incorporated |
| Extend parameter dimension uniformly across boundary faces | Incorporated |
| Separate RBM/Kronecker lower bounds from unrestricted localization | Incorporated |
| Produce a concrete superlogarithmic full-support lower bound | Incorporated via the effective eliminant ray and explicit superincreasing ray; a natural moderately conditioned family remains open |
| Analyze exact rational tables | Basic recognition incorporated: linear budgets in `exists-R`, zero latent bits in `P`; hardness for positive budgets remains open |
| Analyze general sparse interaction graphs and succinct weight descriptions | Open |

[cm05]: ../sources.md#cm05
[geiger06]: ../sources.md#geiger06
[kahle10]: ../sources.md#kahle10
[kahle12]: ../sources.md#kahle12
[montufarmorton17]: ../sources.md#montufarmorton17
[mp10]: ../sources.md#mp10
[montufarrauh17]: ../sources.md#montufarrauh17
[rka11]: ../sources.md#rka11
[pachtersturmfels04]: ../sources.md#pachtersturmfels04
[cuetomortonsturmfels10]: ../sources.md#cuetomortonsturmfels10
[etessami14]: ../sources.md#etessami14
