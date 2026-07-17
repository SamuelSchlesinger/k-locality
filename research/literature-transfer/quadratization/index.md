# Quadratization and local Gibbs lifts

[Back to the research map](../index.md)

The useful connection is narrower than the shared use of auxiliary bits might
suggest.  An exact quadratization always gives a quadratic extension of a
*ground-state support*.  It does not normally give a finite-temperature Gibbs
marginal.  A stronger construction hidden in the universal-feature proof of
Anthony--Boros--Crama--Gruber does give an exact distributional lift; its
balanced `k`-block generalization appears to settle the worst-case exponent of
`L_k`.

## Three different quantities

For a pseudo-Boolean function `f : {0,1}^n -> R`, let `q(f)` be the least `m`
for which a quadratic `g(x,h)` satisfies

```text
f(x) = min_h g(x,h)                 (quadratization).
```

For a support `S`, let `GSE_2(S)` be the least `m` for which a nonnegative
quadratic `E(x,h)` has

```text
S = {x : exists h, E(x,h)=0}        (ground-state extension).
```

Finally, `L_2(D)` also prescribes the relative probabilities: on the exposed
joint support there must be a quadratic Gibbs potential whose visible marginal
is exactly `D`.  Consequently, the safe comparison is

```text
objective quadratization  ->  ground-state support  ->  visible distribution,
```

where only the first arrow is automatic.

## Logic gates are quadratic ground-state constraints

There is also a circuit-to-quadratic route, traditionally called Ising
*ground-state synthesis* [guperales12][guperales12].  It is stronger than the
scope-counting trace argument because the graph of a two-input NAND gate is
already exposed by a quadratic polynomial.

**Theorem (quadratic NAND trace lift).** Let `C` be an `s`-gate NAND circuit.
If it recognizes `S`, then `L_2(U_S)<=s`.  If it is driven by `m` uniform seed
bits and generates `D`, then `L_2(D)<=m+s`.  A NAND verifier with `w` witness
bits always gives `GSE_2(S)<=w+s`; it gives `L_2(U_S)<=w+s` when accepting
witness multiplicity is constant, in particular when the verifier is
unambiguous.

**Proof.** The polynomial

```text
H_NAND(a,b,c)=3-2a-2b-3c+ab+2ac+2bc
```

is nonnegative on `{0,1}^3` and vanishes exactly when
`c=NAND(a,b)`: it is zero on `001,011,101,110` and has values `3,1,1,1`
on the other four assignments.  Summing this penalty over all gates, and
adding `1-output` for a recognizer, gives a nonnegative quadratic whose ground
states are precisely the valid accepting traces.  A deterministic trace is
unique for each input or seed, proving the recognizer and generator statements.
For a verifier, there is one ground trace per accepting `(x,w)`, so projection
always realizes the support but the flat ground-state law weights `x` in
proportion to its number of accepting witnesses.  Constant multiplicity is
exactly what makes the visible law uniform.

Gu and Perales study the general synthesis question, characterize constraints
on unlifted `m`-body ground sets, and encode Boolean circuits into two-body Ising
ground states [guperales12][guperales12].  Hadfield surveys and systematizes
representations of Boolean and real functions as Hamiltonians, including
degree reduction and Boolean-gate constructions [hadfield21][hadfield21].
In localization language, the theorem
above has an important barrier consequence: a strong lower bound for
`L_2(U_S)` is automatically a deterministic circuit lower bound, whereas an
arbitrary nondeterministic verifier only upper-bounds the support quantity
`GSE_2(S)` unless witness counts are controlled.  See the
[circuit-transfer note](../circuits/index.md) for the full implication ledger.

## What an exact quadratization transfers

Let `alpha = min_x f(x)` and let `g` be an `m`-variable quadratization of `f`.
Then

```text
E(x,h) = g(x,h) - alpha
```

is nonnegative on the whole lifted cube: every `g(x,h)` is at least
`min_h g(x,h)=f(x)`, which is at least `alpha`.  Moreover,

```text
exists h, E(x,h)=0  iff  x is in argmin(f).
```

Thus

```text
GSE_2(argmin f) <= q(f).
```

This is an **exact transfer** for upper bounds.  Anthony et al.'s general
upper bound (Theorem 5) therefore gives every ground set an extension with at
most

```text
2^ceil(n/2) + 2^floor(n/2) - 2
```

auxiliary bits [abcg17][abcg17].  Their Theorem 6 similarly gives
`O_d(n^(d/2))` auxiliaries for the ground set of a degree-at-most-`d`
objective.

The corresponding fixed-ground-support lower-bound transfer is false. A ground-state extension
of `S=argmin(f)` need only preserve the zeros of `f-alpha`; it need not preserve
the positive objective gaps.  This failure is decisive in the generic case:
Theorem 1 of [abcg17][abcg17] shows that almost every `f` needs
`Omega(2^(n/2))` quadratization variables, while almost every `f` also has a
unique minimizer.  A singleton is exposed by a linear energy with no auxiliary
bits.  Hence these generic objective lower bounds are a **non-transfer** to
`GSE_2` and to localization complexity.  The same warning applies to the
`Omega_d(n^(d/2))` bounded-degree lower bound in their Theorem 2.

## Why minimization does not preserve Gibbs weights

The tempting identity

```text
exp(-min_h g(x,h)) = sum_h exp(-g(x,h))
```

is false.  The left side keeps only a minimum value; the right side depends on
all excitation energies and their multiplicities.  Sending inverse temperature
to infinity recovers global ground states, not an exact finite-temperature
marginal with prescribed visible weights.

There is a **conditional transfer** to a flat distribution when every visible
ground state has the same number of minimizing witnesses.  In particular, a
unique minimizing witness over each `x in argmin(f)` makes the uniform law on
the joint ground states marginalize to `U_argmin(f)`.  More generally, an exact
distributional transfer requires a quadratic potential `p` on the joint ground
space such that

```text
rho(x) = (1/Z) sum_{h:E(x,h)=0} exp(p(x,h)).
```

Ordinary quadratization theorems assert neither condition.

## Zero temperature restores the lower-bound direction

For an integer-valued objective `f`, define `aux_k(f)` as the least `ell` for
which

```text
f(x)=min_h g(x,h),  deg(g)<=k.
```

Consider the full-support Gibbs ray

```text
D_(f,t)(x)=t^f(x)/sum_z t^f(z),  0<t<1.
```

The paper's zero-temperature theorem proves

```text
liminf_(t->0) L_k(D_(f,t)) >= aux_k(f).
```

The key point is boundary-safe. If arbitrarily cold members had an `ell`-bit
localization, semialgebraic curve selection chooses a family of joint lifts
with fixed facial support. Puiseux valuations of their positive coordinates
come from algebraic Puiseux expansions [basu06][basu06]. The selected joint
potentials then force the valuation vector to be a degree-`k` polynomial on
that face, and marginalization becomes minimum over the hidden fiber. A large
multiple of the face-exposing energy converts that constrained minimum into an
ordinary degree-`k` reduction with `ell` bits. This contradicts
`aux_k(f)>ell`.

Thus objective lower bounds still do not lower-bound the localization of the
flat ground-state law, but they **do** lower-bound sufficiently cold
full-support Gibbs laws. BCRH's parity bound gives a concrete noisy-parity ray
with `L_2=Omega(log n)`, while the finite-union quadratization bound yields
integer energies whose cold rays require `Omega(2^(n/2))` hidden bits
[abcg17][abcg17] [bcrh20][bcrh20].

There are two different notions of “sufficiently cold” in the paper.  The
zero-temperature theorem gives an existential cold tail for any fixed
objective with `aux_k(f)>ell`.  Separately, a homogeneous marginal-ideal
eliminant and a base-coded integer energy produce a computable rational
threshold `tau` such that `L_k(D_(f,t))>ell` for every real `0<t<tau`.
The latter is effective but the energy is elimination-defined; it does not
make the threshold effective for the closed-form superincreasing ray.

## Universal monomial features give an exact distributional transfer

The proof of Theorem 4 of [abcg17][abcg17] is stronger than its minimization
statement.  For a pairwise-cover family `H`, it introduces the Boolean
features

```text
y_A = product_{i in A} x_i,          A in H,
```

and represents each visible monomial by a product of two such features.  The
feature map is independent of `f`.  Theorem 5 takes `H` to be all nonempty
subsets lying within either side of a balanced bipartition, giving the exact
size displayed above.

The graph of this feature map is quadratically exposed.  Recursively split a
non-singleton `A` into smaller sets and impose `z=uv` with Rosenberg's
nonnegative penalty

```text
R(u,v,z) = uv - 2uz - 2vz + 3z.
```

This identity originates with Rosenberg and is recorded in Boros and Hammer's
survey [rosenberg75][rosenberg75] [boroshammer02][boroshammer02].

On Boolean inputs, `R>=0`, with equality exactly when `z=uv`.  The sum of the
recursive penalties is therefore a quadratic `P_graph>=0` whose zero set is
the graph `h=phi(x)`, with one lifted point over every `x`.

Now let `D` have support `S` and mass function `rho`.

1. Represent `b(x)=1[x notin S]` by a quadratic `q_b(x,h)` on the feature
   graph.
2. Choose `M` large enough that
   `E=M P_graph+q_b` is positive off the graph.  On the graph it equals `b`,
   so its zero set is exactly `{(x,phi(x)):x in S}`.
3. Extend `a(x)=log rho(x)` arbitrarily off `S` and represent it by a quadratic
   `q_a(x,h)` on the graph.

The joint distribution supported on `(x,phi(x))` with mass `rho(x)` has
quadratic exposing energy `E` and quadratic log-potential `q_a`.  By the
face--Gibbs characterization it is 2-local, and its visible marginal is exactly
`D`.  Therefore

```text
L_2(D) <= 2^ceil(n/2) + 2^floor(n/2) - 2.             (1)
```

This is an **exact transfer**, derived from the universal-feature construction,
not from the invalid minimum-to-log-sum-exp step.  Combining (1) with the
paper's generic full-support lower bound makes the worst-case order
`Theta(2^(n/2))` up to constants.

The displayed bound retains Theorem 5's auxiliary variables for singleton
features.  Identifying those features directly with the original `x_i` removes
`n` redundant bits; this sharpened count is the `k=2` case of (2) below.

For a full-support distribution whose multilinear `log rho` has degree at
most fixed `d`, the smaller pairwise cover in Theorem 6 of
[abcg17][abcg17] gives the exact order-reduction upper bound

```text
L_2(D) = O_d(n^(d/2)).
```

## Balanced `k`-block lift

The preceding graph argument generalizes beyond the published quadratic
pairwise cover.  This subsection is **our derivation**, not a theorem attributed
to the quadratization papers; its novelty relative to hierarchical-model and
factor-graph literature has not yet been audited.

Partition `[n]` into `k` blocks `V_1,...,V_k` whose sizes differ by at most one.
The resulting dictionary of within-block subsets is the classical balanced
`k`-generator of the Boolean lattice [ellis09][ellis09]. Its combinatorial
origin should be distinguished from the graph-certificate and Gibbs-lift
steps below.
Within every block introduce a feature `y_A` for each subset `A` of size at
least two, and expose all identities `y_A=product_{i in A}x_i` recursively with
the quadratic Rosenberg penalties above.  The number of latent bits is

```text
ell = sum_j (2^|V_j| - |V_j| - 1)
    <= k (2^ceil(n/k) - 1)
    = O_k(2^(n/k)).
```

For every visible monomial `x_S`, write

```text
x_S = product_{j=1}^k y_{S intersect V_j}
```

on the graph, interpreting an empty factor as `1`, a singleton factor as the
original visible bit, and a larger factor as its feature bit.  This is a
polynomial of degree at most `k` in the lifted variables.  Consequently every
pseudo-Boolean table has an order-at-most-`k` representation on this one fixed
feature graph.

Repeating the support-indicator and log-weight construction verbatim gives

```text
L_k(D) <= sum_j (2^|V_j| - |V_j| - 1) = O_k(2^(n/k))   (2)
```

for **every** distribution `D` and every `k>=2`.  The support-zero case is not
being smuggled through a logarithm: `q_b + M P_graph` exposes precisely the
graph points over `S`, while `q_logrho` controls weights only on that exposed
set.  Equation (2) matches the exponent in the paper's generic full-support
`Omega_k(2^(n/k))-n` lower bound. The proof has survived an independent
mathematical audit; the exact distributional synthesis still requires novelty
comparison beyond the sources audited here. It identifies the worst-case scale
of localization complexity for every fixed `k`.

The elementary graph and factorization claims are exhaustively checked for
small instances by
[the validation script](data/validate_block_lift.py).

## Structured results: what survives

Boros--Crama--Rodríguez-Heck substantially sharpen the older symmetric bounds
[bcrh20][bcrh20].  Several of their constructions encode the relevant Hamming
weight with a unique minimizing witness, so they transfer to flat
localizations, not merely to support extensions.  All logarithms in the table
are base two.

| Published result | Localization consequence | Label |
|---|---|---|
| Theorem 6: every symmetric objective has a quadratization with `2 ceil(sqrt(n+1))` auxiliaries | Every flat law on a union of Hamming layers has `L_2 <= 2 ceil(sqrt(n+1))`; the proof's one-hot encoding gives a unique minimizer | **Exact transfer** |
| Theorem 9 and Corollary 1: the positive monomial needs and suffices with `ceil(log_2 n)-1` auxiliaries | For `S={0,1}^n minus {1^n}`, `GSE_2(S)=L_2(U_S)=ceil(log_2 n)-1` for `n>=2` | **Exact transfer** |
| Theorem 5 and the valid part of Theorem 11: parity needs `ceil(log_2 n)-1` auxiliaries; formula (26) attains it for even `n` | For either parity class `S`, `GSE_2(S)=L_2(U_S)=ceil(log_2 n)-1`; for odd `n`, use the corrected square encoding described below rather than printed formula (27) | **Exact transfer after correcting the odd case** |
| Theorems 4 and 7: exact-`t` has lower bound `max(ceil(log t),ceil(log(n-t)))-1` and an upper bound one larger | The unique-witness upper bound transfers to `U_{|x| != t}`; the paper's witness-product argument independently gives the support lower bound | **Exact transfer** after restating the proof for zeros |
| Theorem 1: some symmetric objectives require `Omega(sqrt(n))` auxiliaries | No lower bound for a ground support or `L_2`; the objective gaps may carry all the hardness | **Non-transfer** |

The earlier `y`-linear lower bounds--including the `Omega(sqrt(n))` parity
bound in Theorem 5.6 of [abcg16][abcg16] and the general bound in Theorem 3 of
[abcg17][abcg17]--are **restricted-model results**.  Quadratic localization
allows hidden--hidden interactions.  Indeed, the later unrestricted parity
construction uses only `ceil(log_2 n)-1` auxiliary bits, so a `y`-linear lower
bound cannot lower-bound unrestricted `L_2`.

There is a source-level correction in the odd-parity upper bound.  With the
notation of [bcrh20][bcrh20], printed formula (27) fails for odd `n` at
`x=1^n`: its square has inner value at least two for every encoded witness, so
it cannot attain the required zero.  The lower bound in Theorem 5 and the
even-`n` formula (26) are unaffected.  For odd `n`, if `pi_n` denotes the
odd-parity indicator, put

```text
J(h)=sum_{j=0}^{ell-1} 2^j h_j,
ell=ceil(log_2((n+1)/2)),
g(x,h)=(|x|-2J(h))^2.
```

Every even weight in `{0,2,...,n-1}` has one zero witness, and every odd weight
has minimum one.  Hence this is a valid quadratization of the odd-parity
indicator, with a unique zero witness over every ground input (odd inputs can
have two minimizing witnesses), using
`ell=ceil(log_2 n)-1` bits.  Complementing one visible bit exchanges the two
parity classes.  This is the odd construction used in the current paper; it
should not be attributed to formula (27).

## Circuit consequences

Ground-state synthesis also runs in the reverse direction. A deterministic
NAND recognizer with `s` gates gives `L_2(U_S)<=s`, and an arbitrary
nondeterministic NAND verifier gives `GSE_2(S)<=w+s`; uniform weights require
constant accepting-witness multiplicity. Every transferred ground-state
extension can in turn be fed into the paper's exact
localization-to-nondeterministic-circuit compilation. These implications are
logically valid, but the generic quadratization bounds above do not produce new
circuit bounds:

- quadratization lower bounds usually concern objective values, not the
  minimizer support;
- the explicit positive-monomial and parity supports already have elementary
  deterministic circuits;
- the universal feature lift counts latent bits but may use a dense order-`k`
  potential with `Theta(2^n)` coefficients, so it does not yield a
  `2^(n/k)`-size circuit for an arbitrary truth table;
- full-support distributional bounds have no support-circuit consequence,
  since the recognizer is constant one.

Thus circuit statements are presently a **conditional transfer** through the
separate support-compilation theorem, not an implication of quadratization
complexity itself.  Reversing the `y`-linear parity proof would also be invalid:
that proof imports a known hyperplane-slicing bound from threshold-circuit
work; it does not establish a new circuit lower bound.

## Transfer ledger

| Candidate statement | Status |
|---|---|
| An `m`-auxiliary quadratization upper-bounds `GSE_2(argmin f)` | **Exact transfer** |
| A quadratization with equal ground-witness multiplicity realizes the flat law on `argmin f` | **Conditional transfer** |
| Pairwise-cover monomial features realize every `D` with the bound (1) | **Exact transfer** |
| The balanced `k`-block feature graph realizes every `D` with the bound (2) | **Exact transfer**, new derivation; novelty open |
| A lower bound on `q(f)` lower-bounds `GSE_2(argmin f)` or `L_2` | **Non-transfer** |
| A degree-reduction lower bound for `f` lower-bounds `L_k(D_(f,t))` for sufficiently small `t` | **Exact asymptotic transfer** |
| A `y`-linear quadratization lower bound lower-bounds unrestricted localization | **Restricted-model result** |
| An approximation or penalty-limit quadratization gives an exact localization | **Non-transfer** without a closure argument matching the paper's model |
| An `s`-gate NAND recognizer for `S` gives `L_2(U_S)<=s` | **Exact transfer** via a bijective ground-state trace |
| An arbitrary NAND verifier gives `L_2(U_S)<=w+s` | **Non-transfer** without constant witness multiplicity; `GSE_2(S)<=w+s` is unconditional |

[abcg16]: ../sources.md#abcg16
[abcg17]: ../sources.md#abcg17
[bcrh20]: ../sources.md#bcrh20
[boroshammer02]: ../sources.md#boroshammer02
[rosenberg75]: ../sources.md#rosenberg75
[ellis09]: ../sources.md#ellis09
[basu06]: ../sources.md#basu06
[guperales12]: ../sources.md#guperales12
[hadfield21]: ../sources.md#hadfield21
