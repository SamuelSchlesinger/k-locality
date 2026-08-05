# Natural full-support families

## Verdict

This route clears the flagship admission rule with a manuscript-ready result.
There is an elementary Hamming-radial (equivalently, finitely exchangeable)
family

```text
D_n(x) proportional to exp(-2^(|x|/r_n)),
r_n = 2^floor(log_2(n+1)),                              (1)
```

whose point-probability ratio is less than `e^3`, yet, for every fixed
`k>=2`,

```text
L_k(D_n) = Theta_k(n^(1/k)).                            (2)
```

In particular, `L_2(D_n)=Theta(sqrt(n))`.  The target law is evaluated at the
fixed visible inverse temperature one: there is no ineffective cold threshold
and no dimension-dependent condition number.  This terminology does not
restrict the competing localizations to interior finite-parameter lifts; the
lower bound is against the full closure, including boundary joint laws.  The
energy is a smooth function of Hamming weight taking values in `[1,4)`, rather
than a superincreasing encoding.

The lower bound combines four exact facts:

1. `X^(r_n)-2` is Eisenstein, so its positive root has algebraic degree `r_n`;
2. a quadratically exposed block-constant copy of the smaller cube turns
   Hamming weight into the binary integer `0,...,r_n-1`;
3. Lindemann--Weierstrass makes the corresponding Gibbs weights algebraically
   independent; and
4. the manuscript's marginal ideal excludes every hidden budget below the
   feature-dimension threshold.

The block substitution is related to the symmetrization reduction of
Anthony--Boros--Crama--Gruber [abcg16][abcg16], but the explicit Eisenstein
specialization, the facial conditioning step, and the finite-temperature
localization conclusion are not results found in that source.

## Parameters and the encoded diagonal copy

Fix `n>=1` and put

```text
m = floor(log_2(n+1)),
r = 2^m,
alpha = 2^(1/r).
```

Then

```text
r <= n+1 < 2r.                                          (3)
```

Define the radial energy and its Gibbs law by

```text
f_n(x) = alpha^|x| = 2^(|x|/r),
D_n(x) = exp(-f_n(x)) / sum_z exp(-f_n(z)).              (4)
```

Use `r-1` of the `n` visible coordinates in blocks

```text
B_0,...,B_(m-1),       |B_j|=2^j,
```

Their total size is

```text
sum_j |B_j| = 2^m-1 = r-1 <= n,
```

so let `F` be the set of the remaining `n-r+1` coordinates.  Define
`psi : {0,1}^m -> {0,1}^n` by repeating `u_j` throughout `B_j` and setting
all coordinates in `F` to zero.  Its image `C` is a quadratically exposed
diagonal copy of the `m`-cube: it is the zero set of the nonnegative quadratic
energy

```text
E_C(x)
 = sum_(i in F) x_i
   + sum_(j=0)^(m-1) sum_(i in B_j - {b_j})
       (x_i-x_(b_j))^2,                                 (5)
```

where `b_j` is an anchor in `B_j`.  Moreover,

```text
|psi(u)| = sum_(j=0)^(m-1) 2^j u_j =: val(u).           (6)
```

Thus restricting (4) to `C` produces the `m`-bit table with unnormalized
weights

```text
w(u)=exp(-alpha^val(u)),
```

which, as `u` ranges over the cube, are
`exp(-1),exp(-alpha),...,exp(-alpha^(r-1))`.

## Algebraic core

### Lemma 1 (Eisenstein power basis)

The polynomial `X^r-2` is irreducible over `Q`, and

```text
1, alpha, ..., alpha^(r-1)                              (7)
```

are linearly independent over `Q`.

#### Proof

Every non-leading coefficient of `X^r-2` is divisible by `2`, while its
constant coefficient is not divisible by `4`.  Eisenstein's criterion at `2`
therefore makes the polynomial irreducible.  It is the minimal polynomial of
its positive real root `alpha`, so the powers in (7) form the standard power
basis of `Q(alpha)`.

### Lemma 2 (algebraically independent Gibbs weights)

The `r` numbers

```text
exp(-1), exp(-alpha), ..., exp(-alpha^(r-1))             (8)
```

are algebraically independent over `Q`.

#### Proof

The negatives of the numbers in (7) are algebraic and rationally linearly
independent.  Lindemann--Weierstrass therefore gives the claim
[popescu24][popescu24].
Explicitly, if a nonzero rational polynomial vanished on (8), expanding it
into monomials would give a nontrivial algebraic linear combination of
exponentials of distinct algebraic numbers of the form

```text
-sum_(j=0)^(r-1) a_j alpha^j,
```

where distinct exponent vectors give distinct sums by Lemma 1.  This
contradicts the linear-form version of Lindemann--Weierstrass.

## Fixed-temperature lower bound

Put

```text
d_k(s) = sum_(i=0)^k binom(s,i),
q_(m,k) = min { ell>=0 : d_k(m+ell) >= 2^m }.           (9)
```

### Lemma 3 (facial restriction does not cost hidden bits)

Let `P` be a distribution on `{0,1}^n`, and let `C` be the zero set of a
nonnegative degree-at-most-`k` polynomial.  If `P(C)>0` and `P` has an
`ell`-bit `k`-localization, then `P(.|C)` has an `ell`-bit `k`-localization.
If `psi:{0,1}^m -> C` is a bijection obtained by duplicating coordinates and
fixing coordinates to constants, the pullback of `P(.|C)` also has an
`ell`-bit `k`-localization.

#### Proof

Let `Q(x,h)` be a localization of `P`.  By the face--Gibbs theorem, its
support is the zero set of a nonnegative degree-at-most-`k` energy `E_Q`, and
its log-density on that support is the restriction of a degree-at-most-`k`
potential `theta_Q`.

Conditioning on `x in C` replaces the support by its intersection with
`C x {0,1}^ell`.  If `E_C` exposes `C`, then `E_Q+E_C` exposes this
intersection, while `theta_Q` remains its Gibbs potential.  It is nonempty
because `P(C)>0`.  Hence the conditional joint law is still `k`-local.

Substituting `x=psi(u)` in the exposing energy and potential does not increase
multilinear degree.  The pulled-back joint law on `(u,h)` is therefore
`k`-local and has the asserted visible marginal.

### Theorem 4 (well-conditioned radial lower bound)

For the distribution in (4),

```text
L_k(D_n) >= q_(m,k).                                    (10)
```

For every fixed `k`, this is `Omega_k(n^(1/k))`.  At `k=2`,

```text
q_(m,2)
 = max(0,
       ceil((sqrt(2^(m+3)-7)-1)/2)-m)
 = Theta(sqrt(n)).                                      (11)
```

#### Proof

Condition `D_n` on the quadratic face `C` in (5) and pull it back along
`psi`.  By (6), the resulting distribution `A_m` on `{0,1}^m` has the `r`
unnormalized coordinates in (8).

Fix `ell<q_(m,k)`.  Then `d_k(m+ell)<r`.  The manuscript's marginal-ideal
theorem supplies a nonzero homogeneous polynomial

```text
H in Z[p_u : u in {0,1}^m]
```

that vanishes on every visible marginal of an `ell`-hidden-bit order-`k`
model, including boundary-supported joint models.  Lemma 2 gives
`H((w(u))_u) != 0`.  If `Delta=deg(H)` and `Z=sum_u w(u)`, homogeneity gives

```text
H(A_m) = Z^(-Delta) H(w) != 0.
```

Thus `L_k(A_m)>ell`.  Lemma 3 then implies `L_k(D_n)>ell`.  This holds for
every `ell<q_(m,k)`, proving (10).

For fixed `k`, `d_k(s)=s^k/k!+O_k(s^(k-1))`; also (3) gives
`r>(n+1)/2`, while `m=O(log n)`.  Therefore
`q_(m,k)=Theta_k(n^(1/k))`.  Formula (11) follows by solving
`1+s(s+1)/2>=2^m` for `s=m+ell`.

Finally, (3) gives `n/r<2`, and hence

```text
1 <= f_n(x) <= alpha^n = 2^(n/r) < 4.
```

Consequently

```text
max_x D_n(x) / min_x D_n(x) < exp(4-1) = e^3.           (12)
```

This is stronger than a bounded energy range: it directly bounds the ratio of
the largest and smallest point probabilities by a universal constant.  In
particular, every point mass is within the same universal factor of uniform:

```text
e^(-3) 2^(-n) < D_n(x) < e^3 2^(-n).                   (12a)
```

## Matching upper bound for every radial law

The lower bound has the exact radial, or exchangeable, scale.  The `k=2`
construction below is the quotient--remainder one-hot encoding of
Boros--Crama--Rodríguez-Heck [bcrh20][bcrh20]; the `k`-digit form is a direct
extension.

### Theorem 5 (radial lookup lift)

Let `P` be any Hamming-radial law on `{0,1}^n`, including one that vanishes on
some Hamming layers.  Write

```text
p_s = P(x) when |x|=s.
```

For `k>=2`, put `L=ceil((n+1)^(1/k))`.  Then

```text
L_k(P) <= kL.                                            (13)
```

#### Proof

Introduce hidden bits `y_(j,a)` for `0<=j<k` and `0<=a<L`.  The nonnegative
quadratic graph energy

```text
E(x,y)
 = sum_(j=0)^(k-1) (1-sum_(a=0)^(L-1)y_(j,a))^2
   + (|x|-sum_(j=0)^(k-1)L^j sum_(a=0)^(L-1)a y_(j,a))^2
                                                               (14)
```

vanishes exactly when each group is one-hot and the selected digits give the
base-`L` expansion of `|x|`.  The witness is unique because
`0<=|x|<=n<L^k`.

For a digit tuple `a=(a_0,...,a_(k-1))`, put

```text
w(a) = sum_(j=0)^(k-1) L^j a_j.
```

The nonnegative degree-at-most-`k` support penalty

```text
R(y)
 = sum_(a : w(a)<=n and p_(w(a))=0)
     product_(j=0)^(k-1)y_(j,a_j)                       (15a)
```

removes exactly the unique witnesses above the zero-probability Hamming
layers.  Thus `E+R` exposes the lifted support of `P`.  On that support use
the degree-at-most-`k` potential

```text
theta(y)
 = sum_(a : w(a)<=n and p_(w(a))>0)
     log(p_(w(a))) product_(j=0)^(k-1)y_(j,a_j).        (15b)
```

At every point of the exposed support, exactly one summand in (15b) survives
and equals `log P(x)`.  The face--Gibbs theorem therefore gives a `k`-local
joint law supported on this unique-witness graph whose visible marginal is
exactly `P`.  It uses `kL` hidden bits.  For a full-support law the penalty
`R` is simply zero.

Combining Theorems 4 and 5 proves (2).  In fact,

```text
max { L_k(P) : P Hamming-radial on n bits }
  = Theta_k(n^(1/k)),                                   (16)
```

and (4) is one explicit, uniformly well-conditioned full-support witness.
Thus the same `Theta_k(n^(1/k))` worst-case scale holds even if the maximum in
(16) is restricted to full-support exchangeable binary laws.

## Auxiliary-variable proof without transcendence

The same algebraic-degree idea gives a useful independent check.  It proves a
strong degree-reduction lower bound before any Gibbs model is considered.

### Proposition 6 (Eisenstein auxiliary lower bound)

For the real-valued objective `f_n` in (4),

```text
aux_k(f_n) >= q_(m,k).                                  (17)
```

#### Proof

Suppose `f_n(x)=min_h g(x,h)` with `ell` auxiliary bits and `deg(g)<=k`.
Restrict `x` to `psi(u)`.  For each `u`, choose one minimizing witness
`sigma(u)`.  Writing the restricted polynomial in its degree-at-most-`k`
monomial features gives

```text
(1,alpha,...,alpha^(r-1))^T = A_sigma c,                (18)
```

where `A_sigma` is the `r`-by-`d_k(m+ell)` zero--one feature matrix with row
`chi_k(u,sigma(u))`.

If `d_k(m+ell)<r`, this rational matrix has a nonzero rational vector in its
left kernel.  Equation (18) would then give a nontrivial rational linear
relation among the power basis (7), impossible by Lemma 1.  Hence every
degree-`k` reduction has `ell>=q_(m,k)`.

This proof checks the direction of every reduction: restriction and coordinate
identification preserve a degree upper bound, and selecting minimizers turns a
minimum representation into a rational feature subspace.  No symmetry of the
putative reduction is assumed.

## Zero-temperature transfer for arbitrary real objectives

An earlier manuscript version stated its zero-temperature theorem only for
integer-valued objectives because its proof used semialgebraic dependence on
the temperature parameter.  Integrality is unnecessary: the closed-image
argument below yields the stronger statement now used in the manuscript.

### Theorem 7 (real zero-temperature transfer)

For every real-valued `f:{0,1}^n -> R` and every `k>=2`, define

```text
D_(f,t)(x) = t^f(x) / sum_z t^f(z),       0<t<1.
```

Then

```text
liminf_(t down to 0) L_k(D_(f,t)) >= aux_k(f).          (19)
```

#### Closed minimum-image lemma

Let `T subseteq {0,1}^n x {0,1}^ell` meet every visible fiber, and let `V` be
any linear subspace of `R^T`.  The map

```text
Phi: V -> R^({0,1}^n),
Phi(v)(x) = min_(h:(x,h) in T) v(x,h)                   (20)
```

has closed image.

To prove this, for every selector `sigma(x) in T_x`, let

```text
C_sigma = {v in V : v(x,sigma(x)) <= v(x,h)
                     for every x and h in T_x}.
```

This is a closed polyhedral cone.  On it, `Phi` is the linear coordinate map
`L_sigma(v)=(v(x,sigma(x)))_x`.  A linear image of a polyhedral cone is
polyhedral by the projection theorem for polyhedra (equivalently,
Fourier--Motzkin elimination), hence closed.  There are finitely many
selectors, and

```text
Phi(V) = union_sigma L_sigma(C_sigma),
```

a finite union of closed sets.

#### Proof of Theorem 7

Subtract `min f` from `f`; this does not change `D_(f,t)` or `aux_k(f)`, so
assume `min f=0`.  If (19) failed, the integer-valued complexities would give
an `ell<aux_k(f)` and a sequence `t_j down to 0` such that every
`D_(f,t_j)` has a localization using at most `ell` bits.  Pad localizations
with fewer bits by deterministic-zero bits, and denote the resulting
exactly-`ell`-bit localizations by `Q_j`.

Only finitely many supports exist on the fixed lifted cube, so pass to a
subsequence for which

```text
supp(Q_j)=T
```

is constant.  Full visible support implies that every fiber `T_x` is nonempty.
Let `s_j=-log(t_j)` and define, on `T`,

```text
v_j(x,h) = -log Q_j(x,h) / s_j.                         (21)
```

The face--Gibbs theorem says that `log Q_j|T` is the restriction of a
degree-at-most-`k` polynomial.  Hence every `v_j` lies in the fixed linear
space `V_T` of degree-at-most-`k` functions restricted to `T`.

For every visible `x`,

```text
-1/s_j log sum_(h in T_x) exp(-s_j v_j(x,h))
 = -1/s_j log D_(f,t_j)(x)
 = f(x) + log Z_j/s_j,                                  (22)
```

where `Z_j=sum_z exp(-s_j f(z))`.  Since `min f=0`,
`1<=Z_j<=2^n`, so the right side tends to `f(x)`.  For a fiber of size at
most `2^ell`, soft minimum and minimum differ by at most
`ell log(2)/s_j`.  Therefore

```text
Phi(v_j) -> f.                                          (23)
```

The closed minimum-image lemma gives `v in V_T` with

```text
f(x)=min_(h in T_x)v(x,h).                              (24)
```

Choose a degree-at-most-`k` polynomial `g` whose restriction to `T` is `v`.
Because `T` is the support face of a `k`-local law, a nonnegative
degree-at-most-`k` energy `E` has zero set exactly `T`.  Choose

```text
M > max({0} union
        {(f(x)-g(x,h))/E(x,h) : (x,h) notin T}).        (25)
```

Then (24) and (25) give

```text
f(x)=min_h {g(x,h)+M E(x,h)},
```

a degree-at-most-`k` reduction using `ell` auxiliaries.  This contradicts
`ell<aux_k(f)` and proves (19).

The sign check in (22) is essential: `t_j=e^(-s_j)`, so
`t_j^f=e^(-s_j f)` and the tropical operation is a minimum.  No compactness of
the coefficient vectors is required; closedness of the piecewise-linear image
replaces coefficient convergence.  No semialgebraic choice or Puiseux
expansion is needed.

Proposition 6 and Theorem 7 already give
`L_k(D_(f_n,t))>=q_(m,k)` for all sufficiently small `t`.  Theorem 4 is
strictly stronger for this family: Lindemann--Weierstrass proves the bound at
the fixed temperature `t=e^(-1)`, namely `exp(-f_n)`, and gives the constant
ratio (12).

## Novelty and literature check

- The binary block identification follows the reduction pattern in Lemma 5.1
  of [abcg16][abcg16].  That paper uses it for an existential symmetric
  quadratization lower bound; it does not give this explicit Eisenstein family
  or a localization theorem.
- The `k=2` radial upper bound is the exact-support/Gibbs interpretation of the
  quotient--remainder construction in Theorem 6 of [bcrh20][bcrh20].  The
  `k`-digit lookup lift is the evident higher-locality extension and should be
  labeled as such.
- The fixed-temperature lower bound depends on the manuscript's boundary-safe
  marginal-ideal theorem.  Standard positive restricted-Boltzmann dimension
  counts would not cover localizations supported on arbitrary lifted faces.
- Targeted searches for combinations of Lindemann--Weierstrass, marginal
  varieties, graphical models, Hamming-radial laws, and algebraically
  independent probability tables found no matching construction.  This is
  encouraging, but it is not a substitute for an expert novelty review before
  submission.

## Remaining limitations

The probabilities in (4) are transcendental, although the law is uniformly
computable: its normalizer is the `n+1`-term radial sum

```text
sum_(s=0)^n binom(n,s) exp(-2^(s/r)).
```

A rational, comparably conditioned family with the same transparent lower
bound remains open.  Also open is a comparable result for a named physical or
combinatorial model such as noisy parity, a fixed-degree polynomial of Hamming
weight, a standard code ensemble, or an Ising model on a natural graph.

These are worthwhile refinements, but they do not weaken the theorem above:
(4) is an explicit, simple, Hamming-radial, full-support family with an exact
localization scale and universal probability conditioning.

## Reproducible check

The standard-library script
[`data/validate_eisenstein_radial.py`](data/validate_eisenstein_radial.py)
checks the all-`n` block embedding, the exact `k=2` threshold, Eisenstein's
coefficient conditions, the energy range, and the base-`L` lookup encoding on
small instances.  It is a sanity check, not a replacement for the proofs.

## Admission decision

**Admit.**  Theorems 4 and 5 give a complete, manuscript-ready
`Theta_k(n^(1/k))` result for an explicit well-conditioned radial family.
Proposition 6 supplies an independent algebraic-degree check, and Theorem 7
strengthens the manuscript's zero-temperature machinery.  This is materially
stronger than a computationally narrowed conjecture or a barrier reduction.

## Local References

[abcg16]: ../sources.md#abcg16
[bcrh20]: ../sources.md#bcrh20
[popescu24]: ../sources.md#popescu24
