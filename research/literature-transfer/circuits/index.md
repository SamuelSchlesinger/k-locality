# Circuit transfers

[Back to the research map](../index.md)

This note separates two directions that are easy to conflate:

1. compiling a localization into a circuit for its visible support; and
2. converting a localization lower bound into a circuit lower bound.

The first applies to every distribution. The second applies to support circuits
only when the distribution whose localization is lower-bounded is the uniform
law on that support.

## Notation and gate conventions

`L_k` denotes the paper's `mathcal L_k`. `C_r(S)` is the minimum ordinary
Boolean circuit size for recognizing `S` with fan-in at most `r`; `NSize(S)`
is nondeterministic circuit size, including witness bits in the resource
accounting; `C_NAND(S)` is the minimum number of gates in a NAND-basis
recognizer; `G_r(D)` is exact generator size; and `GSE_2(S)` is the minimum
number of hidden bits in a nonnegative quadratic energy whose projected zero
set is `S`. Input gates are free and the output gate is counted. Exact-threshold
gates are mentioned only when the text explicitly changes the gate basis.

## Quadratic circuit-to-ground-state transfer

The circuit upper bound is already quadratic; it need not pay one unit of
locality for a gate and its two inputs.  The relevant observation is standard
in the Ising *ground-state synthesis* literature [guperales12][guperales12].

**Theorem (NAND trace lift).** Let `C` be an `s`-gate NAND circuit.

1. If `C` recognizes `S`, then `L_2(U_S) <= s`.
2. If `C` is an exact generator driven by `m` uniform seed bits, its output law
   `D` satisfies `L_2(D) <= m+s`.
3. If `C(x,w)` is a verifier with `w` witness bits, then
   `GSE_2(S) <= w+s` for `S={x: exists w, C(x,w)=1}`.  If every `x in S` has
   the same number of accepting witnesses--in particular, if the verifier is
   unambiguous--then also `L_2(U_S) <= w+s`.

**Proof.** For one NAND gate with inputs `a,b` and output `c`, use

```text
H_NAND(a,b,c) = 3-2a-2b-3c+ab+2ac+2bc.
```

On the Boolean cube this is zero precisely on
`001,011,101,110`, the graph `c=NAND(a,b)`, and takes the positive values
`3,1,1,1` on `000,010,100,111`.  Sum one copy for every gate.  For a
recognizer, add the unary penalty `1-output`.  The resulting quadratic energy
is nonnegative and has zero set exactly the accepting circuit traces.  A
deterministic circuit has one trace over each input, so uniform measure on the
ground states projects bijectively to `U_S`.  For a generator, every seed has
one trace, so uniform ground-state measure pushes forward to the generated
law.  For a verifier, every accepting pair `(x,w)` has one trace; consequently
the visible ground-state multiplicity over `x` is exactly its number of
accepting witnesses.  Projection always gives the asserted ground-state
extension, while the uniform law follows exactly in the constant-multiplicity
case.  The face--Gibbs characterization turns each uniform ground-state law
into a quadratic localization.

Gu and Perales formulate the surrounding synthesis problem, give general
constraints on ground sets of `m`-body Hamiltonians, and construct Ising
encodings of Boolean circuits [guperales12][guperales12].  The displayed NAND
penalty makes the resource count and the probability-multiplicity issue
transparent in the conventions of this corpus.

## Exact support normal form

Suppose `D` on `{0,1}^n` has an `ell`-bit `k`-localization. The face--Gibbs
characterization supplies a nonnegative multilinear polynomial

```text
E(x,h),  deg(E) <= k,
```

whose zero set is the support of the lifted distribution. Therefore

```text
1_{supp(D)}(x) = OR_{h in {0,1}^ell} [E(x,h) = 0].
```

For a fixed witness `h`, the predicate `[E(x,h)=0]` is one exact-threshold
predicate of the at-most-`k` visible monomials. This is more specific than an
arbitrary nondeterministic circuit: all witness slices come from a single
jointly degree-`k` polynomial.

## Nondeterministic compilation

Guess `h`, compute all order-at-most-`k` monomials of `(x,h)`, and test the
single weighted equality `E(x,h)=0`. Replacing the real exposing weights by
bounded integer weights and compiling the addition gives a fan-in-two Boolean
circuit of size polynomial in

```text
d_k(n+ell) = sum_{j=0}^k binom(n+ell,j).
```

The integer-weight replacement follows from general exact-threshold weight
bounds [babai21][babai21]. This is an **exact transfer** and is the paper's
current localization-to-nondeterministic-circuit theorem.

Inverting the estimate gives the fixed-`k` consequence

```text
L_k(D) >= Omega_k(
  (NSize(supp(D))/log(2+NSize(supp(D))))^(1/(2k))
) - n.
```

This is unconditional but concerns only the visible support.

## Deterministic compilation by witness expansion

The same normal form gives a complementary deterministic simulation. Restrict
`E` separately at every `h`. Each slice is an exact-threshold predicate of the
`d_k(n)` visible monomials. Compile each slice and OR the results. Thus

```text
C_2(supp(D))
  <= 2^ell * O(k d_k(n) + d_k(n)^2 log d_k(n)).
```

Here `C_2` denotes ordinary fan-in-two Boolean circuit size. For fixed `k`,

```text
L_k(D) >= log_2(1+C_2(supp(D))) - O_k(log(n+2)).
```

This is an **exact transfer**. It complements the nondeterministic bound:

- nondeterminism avoids the `2^ell` expansion but its verifier size depends
  polynomially on `n+ell`;
- deterministic simulation pays `2^ell`, while each fixed-witness test depends
  only on the visible feature dimension `d_k(n)`.

With exact-threshold gates treated as primitives, the visible monomials can be
shared and the normal form has `d_k(n)` monomial gates, `2^ell` exact-threshold
gates, and one OR tree.

## Nonnegative nondeterministic degree

For a Boolean function `f`, let `ndeg_+(f)` be the minimum degree of a
multilinear polynomial that is nonnegative everywhere and positive exactly on
`f^(-1)(1)`. If `S=supp(D)` is proper, take an optimal facial cover
`S=F_1 union ... union F_r` and nonnegative degree-`k` polynomials `p_i` whose
zero sets are the `F_i`. Multiplying them gives

```text
P(x) = product_{i=1}^r p_i(x).
```

The product is positive exactly on the complement of `S` and has degree at
most `k fc_k(S)`. Since every `ell`-bit localization gives a facial cover with
at most `2^ell` members,

```text
ndeg(complement(S))
  <= ndeg_+(complement(S))
  <= k fc_k(S)
  <= k 2^L_k(D).
```

The direct product of all witness slices is the corresponding special case.
This is an **exact transfer**. It retains the sign that ordinary
nondeterministic degree discards. In particular, the top multilinear
coefficient proves `ndeg_+(PARITY_n)=n`, yielding the sharp lower half of the
paper's quadratic parity theorem. It still forgets the fact that all slices
come from one jointly degree-`k` polynomial, and since `ndeg_+(f)<=n`, it can
prove at most logarithmic latent lower bounds [dewolf03][dewolf03].

## Filtered facial-cover normal form

The exact support-only quantity keeps the information lost by the product.
Define `GSE_k(S)` as the least `ell` for which a nonnegative degree-`k` energy
`E(x,h)` has projected zero set `S`. Writing

```text
E(x,h) = sum_A c_A(h) x_A
```

gives the exact criterion

```text
GSE_k(S) <= ell
iff
there are nonnegative slices p_h with zero-set union S and
c_A in RM_R(ell,k-|A|) for every A.
```

The coarser facial-cover number `fc_k(S)` drops this shared Reed--Muller
dependence and yields `GSE_k(S) >= ceil(log_2 fc_k(S))`. Singleton faces give
`fc_k(S)<=|S|`, so this relaxation alone can prove at most `n` latent bits.
Counting faces of the order-`k` marginal polytope proves that a uniformly
random nonempty support satisfies

```text
GSE_k(S) = Omega_k(2^(n/(k+1)))
```

with probability `1-2^(-Omega_k(2^n))`. This is a Shannon existence bound,
not an explicit circuit lower bound. At `k=2`, the NAND trace theorem explains
the obstacle: an explicit lower bound on `GSE_2(S)` also lower-bounds the size
of every NAND verifier for `S`, while a lower bound on `L_2(U_S)` lower-bounds
deterministic NAND recognizers.

The same invariant has a selector dual.  For a selector
`sigma:S->{0,1}^ell`, let `Gamma_sigma` be its graph and let `fcl_k` denote
the inverse image of the smallest order-`k` marginal-polytope face containing
a set.  Then

```text
GSE_k(S)<=ell
iff
there is a selector sigma with proj_X fcl_k(Gamma_sigma)=S.
```

Equivalently, a lifted point lies in this facial closure exactly when some law
with the same degree-at-most-`k` moments as the uniform selector graph gives
that point positive mass.  For each fixed selector this is a rational primal--
dual LP: the primal finds an exposing energy, while Farkas multipliers certify
moment leakage outside `S`.  A lower bound still requires one obstruction for
every selector; there are `2^(ell|S|)` of them.

This quantifier is not removed by ordinary coefficient rank.  If
`L(x)=sum_i 2^(i-1)x_i`, the singleton-exposing quadratics

```text
p_a(x)=(L(x)-L(a))^2
```

all lie in the three-dimensional span of `1,L,multilinearize(L^2)`, for an
arbitrary support `S`.  Any rank invariant that forgets the witness labeling
is therefore bounded by three even when `GSE_k(S)` is large.  The filtered
Reed--Muller dependence is the information that must be retained.

The counting argument remains nontrivial on a structured ambient set.  If
`A_n` is the middle Hamming layer, then a uniformly random half-subset
`S subset A_n` has

```text
GSE_k(S) > Omega_k(2^(n/(k+1)) n^(-1/(2(k+1))))
```

with high probability, whereas the unthinned layer itself has zero latent
complexity because it is exposed by a squared Hamming-weight energy.  This is
still nonexplicit, but it shows that the lower-bound phenomenon is not merely
caused by choosing arbitrary points throughout the whole cube.

## Reverse trace transfer for verifiers

The NAND trace theorem strengthens the elementary fan-in-`(k-1)` local-trace
argument: an ordinary fan-in-two verifier already has a *quadratic* ground
lift. If every accepted input has the same number of accepting witnesses, the
uniform law on all accepting witness traces has visible marginal `U_S`, giving

```text
L_2(U_S) <= w+s.
```

This distributional statement is a **conditional transfer**. With arbitrary
witness multiplicities the same construction biases the visible marginal by
the number of accepting witnesses, so it does not localize `U_S`--although it
still gives the unconditional support statement `GSE_2(S)<=w+s`.
Unambiguous verification is the important special case.

## When localization lower bounds imply circuit lower bounds

The quadratic NAND trace construction gives

```text
L_2(U_S) <= C_NAND(S),
```

and hence the same upper bound for every `L_k`, `k>=2`. Consequently, any lower
bound proved for the quadratic localization complexity of the *uniform*
distribution on an explicit support `S` immediately lower-bounds an ordinary
bounded-fan-in deterministic recognizer for `S`. This is an **exact transfer**.
It also explains sharply why strong explicit flat-distribution lower bounds
may run into ordinary circuit-lower-bound barriers. For nondeterministic
circuits the analogous implication requires constant witness multiplicity;
without it, the unconditional object is `GSE_2(S)`, not `L_2(U_S)`.

For a nonuniform `D`, a lower bound on `L_k(D)` does not by itself lower-bound
a recognizer for `supp(D)`: the recognizer trace constructs the uniform law on
the support, not the specified weights. Full-support distributions make this
failure decisive, since their support recognizer is the constant-one circuit.

A localization lower bound does lower-bound the paper's exact generator
complexity `G_{k-1}(D)`. For generic real-valued probability tables this can be
vacuous, because no finite circuit driven by unbiased random bits generates
non-dyadic probabilities exactly. A meaningful distributional transfer would
need an approximate-generator model or an explicit finite description of the
random source.

## Transfer ledger

| Source statement | Localization consequence | Circuit consequence | Status |
|---|---|---|---|
| Exact marginal representation by an `ell`-hidden-bit order-`k` model | `L_k(D) <= ell` | Nondeterministic support circuit of polynomial size in `n+ell`; deterministic support circuit of size `2^ell poly_k(n)` | **Exact transfer** |
| Nonnegative facial-cover product | `ndeg <= ndeg_+ <= k fc_k(supp D) <= k 2^L_k(D)` | Algebraic support lower bound, logarithmic at best | **Exact transfer** |
| Filtered slices and selector facial closure | Exact criterion for `GSE_k(S)<=ell`; rational LP/Farkas certificates per selector; random supports and random middle-layer thinnings are exponentially hard | Nonexplicit circuit existence bound; explicit quadratic bounds meet the NAND barrier | **Exact support invariant** |
| Approximation by a fixed-size binary hierarchical model | Same bound after compactness and closure | Same as above | **Closure transfer** |
| Deterministic NAND recognizer with `s` gates | `L_2(U_S) <= s` | Uniform accepted traces project bijectively to `S` | **Exact transfer** |
| Exact NAND generator with `m` seed bits and `s` gates | `L_2(D) <= m+s` | Uniform traces push forward to the generated law | **Exact transfer** |
| Arbitrary nondeterministic NAND verifier | `GSE_2(S) <= witness bits + trace gates`; its flat ground law is witness-count weighted | Support lift, but not generally a localization of `U_S` | **Exact support transfer; non-transfer for uniform weights** |
| Constant-multiplicity nondeterministic verifier | `L_2(U_S) <= witness bits + trace gates` | Reverse trace construction; unambiguous verification is the main case | **Conditional transfer** |
| Lower bound for unrestricted `L_2(U_S)` | None needed | `C_NAND(S)` is at least the same lower bound | **Exact transfer** |
| Lower bound for unrestricted `L_k(D)` with nonuniform `D` | The stated localization bound | Generator lower bound; no support-recognizer lower bound in general | **Conditional transfer** |
| Hidden-unit lower bound for RBMs | Lower bound only for the RBM subclass | Threshold-code/RBM consequences only; no general support-circuit lower bound | **Restricted-model result** |
| Parameter dimension lower bound for full-support tables | Generic lower bound on `L_k` when dimension counts the full unrestricted model | None for support circuits, which are constant one | **Non-transfer** to support circuits |
| Quadratic reformulation of one chosen objective | Ground-state extension for that chosen objective, if the reformulation preserves its full minimizer projection | Circuit consequence only for that ground set | **Conditional transfer** |

## Research opportunities

1. Exploit the exact filtered criterion on an explicit support: rule out every
   nonnegative slice cover whose coefficient tables lie in
   `RM_R(ell,k-|A|)`, or aggregate the selector LP duals without forgetting
   their Boolean witness labels.
2. Import lower bounds only from statistical models that contain all
   order-`k` interaction graphs allowed here, or state the architectural
   restriction explicitly.
3. Formulate approximate localization and approximate generator complexity
   together; this is the natural setting for KL-divergence bounds from the RBM
   literature.
4. Seek weight-sensitive circuit models for full-support distributions. Boolean
   support circuits intentionally discard the information responsible for the
   generic localization lower bound.

[babai21]: ../sources.md#babai21
[dewolf03]: ../sources.md#dewolf03
[guperales12]: ../sources.md#guperales12
