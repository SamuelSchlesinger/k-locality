# Restricted Boltzmann machines

[Back to the research map](../index.md) ·
[Circuit transfers](../circuits/index.md) ·
[Hierarchical models](../hierarchical-models/index.md)

Restricted Boltzmann machines (RBMs) are the cleanest strict subclass of
quadratic localizations. Consequently, their representation theorems give
valid upper bounds on localization complexity, while their lower bounds
usually do not. This note makes that asymmetry precise.

## Model match

The binary RBM with `n` visible and `m` hidden bits has joint law

```text
Q(x,h) proportional to exp(b*x + c*h + h*W*x).
```

Only singleton and visible--hidden pair interactions occur. Every
finite-parameter RBM joint law is therefore 2-local. The same remains true on
the boundary: if visible RBM marginals converge to `D`, compactness of the
joint probability simplex gives a convergent subsequence of joint laws; its
limit is in the closure of the bipartite pairwise exponential family and has
visible marginal `D`. The face--Gibbs characterization used in the paper then
makes that limiting joint law 2-local.

Hence

```text
D in closure(RBM(n,m))  ==>  L_2(D) <= m.
```

This is an **exact transfer** when the source gives membership in the closed
RBM model, and a **closure transfer** when the source only proves arbitrary
approximation.

The converse fails. An unrestricted quadratic localization may also contain
visible--visible and hidden--hidden interactions. Thus `RBM(n,m)` is a
submodel of the `m`-hidden-bit quadratic marginal model, not an equivalent
parameterization.

## Universality: the constants and the closure issue

There are three distinct bounds that are often conflated.

### The original support-size construction

Le Roux and Bengio's Theorem 2.4 in the accessible author manuscript says
that a distribution with `s` positive-probability visible states can be
approximated arbitrarily well in KL divergence using `s+1` hidden units
[lerouxbengio08][lerouxbengio08]. In particular it gives `2^n+1`, not
`2^(n-1)-1`, for a completely arbitrary target.

Despite the section heading's use of “represent,” the theorem statement is an
approximation theorem. It yields

```text
L_2(D) <= |supp(D)| + 1
```

only as a **closure transfer**. No finite-parameter exact representation is
asserted, even when `D` has full support.

### Pairing neighboring cube vertices

Montúfar and Ay's Theorem 1 replaces individual support points by edges of the
Boolean cube. Let `kappa(S)` be the minimum number of pairs of Hamming-adjacent
vertices whose union contains `S`. Their theorem approximates every
distribution supported on `S` using `kappa(S)-1` hidden units
[montufaray11][montufaray11]. A perfect matching covers the full cube, giving
Corollary 2:

```text
L_2(D) <= 2^(n-1) - 1.
```

Both statements are **closure transfers**. The numerical constant
`2^(n-1)-1` is therefore the 2011 bound, not the best currently audited bound.

### Star-cover improvement

Montúfar and Rauh's Theorem 11 shows that every distribution in the binary
`k`-interaction model is approximable by an RBM with

```text
U(v,k) = sum_{j=2}^k D(v,j)
```

hidden bits, where `D(v,j)` is a star-tuple covering number. For `k=v`,
Corollary 12 applies to every distribution and retains the older
`2^(v-1)-1` estimate while also giving the sufficient bound

```text
ceil( 2(1+log(v-1))/(v+1) * (2^v-v-2) + 1 ).
```

Thus `U(v,v)=O(2^v log(v)/v)`, a genuine asymptotic improvement
[montufarrauh17][montufarrauh17]. Under localization complexity this is the
**closure transfer**

```text
L_2(D) <= U(n,n) = O(2^n log(n)/n).
```

Corollary 14 of the same paper treats pairwise models that already allow
visible--visible interactions. That result is closer to unrestricted
quadratic localization and improves the hidden-bit count to

```text
B(v,k)=sum_{j=3}^k D(v,j)=U(v,k)-D(v,2).
```

It is architecturally weaker as an RBM theorem because it permits direct
visible interactions, but it is the sharper localization transfer. See the
[hierarchical-model audit](../hierarchical-models/index.md).

### Exactness after taking closure

KL approximation is enough here. Convergence in KL implies convergence in
total variation, and the compact-joint subsequence argument above supplies a
limiting 2-local joint distribution with exactly the desired visible
marginal. This does **not** turn the source statement into finite-weight RBM
realizability; it uses the fact that localization complexity includes boundary
faces exactly.

Montúfar and Morton's Definition 2.2 instead defines `RBM(n,m)` itself as the
closure of the positive-parameter model
[montufarmorton15mixtures][montufarmorton15mixtures].
Statements made with that convention already include zero probabilities, but
“exact” still means exact membership in the closed model, not necessarily
finite natural parameters.

## Dimension and generic hidden-unit lower bounds

Montúfar and Morton's Corollary 26 proves for all nonnegative `n,m` that

```text
dim RBM(n,m) = min(2^n - 1, (n+1)(m+1) - 1).
```

This closes the exceptional cases left by the earlier tropical analysis
[montufarmorton17][montufarmorton17]. Parameter counting therefore forces any
universal RBM, and almost every individual target distribution, to have

```text
m >= ceil(2^n/(n+1)) - 1.
```

The word “universal” matters: attaining full dimension is necessary but does
not say that the model fills the simplex.

For localization this is a **restricted-model result**. It does not imply the
same lower bound on `L_2`, because an `m`-bit unrestricted quadratic lift has
all pair interactions among `n+m` variables, not just `(n+1)(m+1)-1` RBM
parameters. Indeed the paper's all-face dimension argument gives only a
generic `L_2` lower bound on the scale `2^(n/2)`, whereas the RBM parameter
obstruction is on the scale `2^n/n`.

The arithmetic translation of Corollary 26 is checked by
[`data/check_bounds.py`](data/check_bounds.py).

## Strong modes, supports, and linear-threshold codes

A strong mode of `p` is a string `x` satisfying

```text
p(x) > sum_{y: Hamming(x,y)=1} p(y).
```

Conditioning an RBM on its hidden state expresses its visible law as a
restricted mixture of at most `2^m` product distributions. Montúfar and
Morton's Theorem 3.7 says that each strong mode of a mixture of product
distributions must be the mode of a separate component. Consequently an
`m`-hidden-bit RBM has at most `2^m` strong modes
[montufarmorton15mixtures][montufarmorton15mixtures]. This gives the valid RBM lower bound

```text
m >= ceil(log_2(number of strong modes)).
```

It is a **restricted-model result**, not a localization lower bound.

Theorem 1.6 and Theorem 3.16 of the same paper sharpen the combinatorics. For
a code `C` of minimum Hamming distance at least two:

- if an RBM distribution has strong modes `C`, an `m`-zonoset must meet every
  `C`-orthant;
- equivalently at the inference level, `C` must be contained in the image of
  `n` linear threshold functions on `m` bits, an `(n,m)` linear-threshold code;
- support exactly equal to `C` implies the strong-mode and perfect-
  reconstruction properties;
- the reverse implication from a threshold code to exact support needs the
  equal-`l_1`-norm condition stated in Theorem 3.16. It is not an unconditional
  characterization of RBM supports.

That last qualification prevents a common overstatement: the paper does not
say that every RBM support is exactly an LTC image, nor that every LTC image is
an RBM support.

### Parity is an explicit non-transfer witness

Let `C` be one parity class. It has `2^(n-1)` words and minimum distance two,
so an RBM supported on `C` needs at least `n-1` hidden bits from mode counting.
For odd `n>1`, Proposition 3.19 and Corollary 3.21 rule out `m=n-1`, so at
least `n` RBM hidden bits are required
[montufarmorton15mixtures][montufarmorton15mixtures].

By contrast, the paper's parity-localization proposition gives

```text
L_2(uniform parity) = Theta(log n).
```

This is a concrete **non-transfer**, not merely a logical warning: zonoset,
strong-mode, and LTC lower bounds for RBMs can be asymptotically false for
unrestricted quadratic localizations.

## RBM networks and threshold-circuit lower bounds

Marginalizing the hidden bits of a positive RBM gives the log-density

```text
b*x + sum_j log(1 + exp(w_j*x + c_j)).
```

Martens, Chattopadhyay, Pitassi, and Zemel call this a softplus RBM network.
Their Theorem 7 approximates every symmetric real function on the Boolean cube
with `n^2+1` softplus units, giving a corresponding (historical) **closure
transfer** for distributions whose log-density depends only on Hamming weight
[martens13][martens13].

Gu, Huang, and Yang subsequently reduce this symmetric-distribution RBM size
to `2n+1`. They also prove a polynomial-size, polynomial-weight equivalence
between margin representation by RBM networks and by depth-two threshold
circuits [gu19][gu19]. The `2n+1` approximation is again a **closure transfer**;
the margin equivalence concerns log-density computation, not Boolean support
recognition.

Martens et al.'s Theorem 10 is a qualified explicit lower bound. If such a network
represents inner product mod 2 with margin `delta`, and its weights are
upper-bounded in value by `C`, it needs

```text
m >= delta * 2^(n/4) / (2 max(log 2, nC + log 2)).
```

In particular, polynomial `C` and `1/delta` give
`m >= 2^((1/4-o(1))n)`. Negative parameters may be arbitrarily large in
magnitude; the hypothesis is an upper bound, not an absolute-value bound.
[martens13][martens13]

This is both a **restricted-model result** and a **non-transfer** to
localization complexity: `L_2` imposes no weight bound, permits intra-layer
quadratic interactions, and does not ask its visible log-density to implement
a Boolean function with margin. It also gives no support-circuit lower bound;
the associated finite-log-density distributions have full support.

## Circuit consequences that do survive

Boundary RBMs have a sharper support normal form than general quadratic
localizations. A joint support face is exposed by

```text
E(x,h) = a + b*x + c*h + sum_{i,j} w_ij x_i h_j >= 0,
supp(Q) = { (x,h) : E(x,h)=0 }.
```

Therefore

```text
x in supp(D)  iff  exists h in {0,1}^m : E(x,h)=0.
```

Writing `r=1+n+m+nm`, the exact-threshold compilation in the paper yields:

- a nondeterministic fan-in-two support circuit with `m` witness bits and
  `O(r^2 log r)` gates; and
- after enumerating witnesses, a deterministic circuit of size
  `O(2^m n^2 log n)`, since each fixed-`h` slice is affine in `x`.

These are **exact transfers** from closed RBM representation to support
circuits, and refine the general bounds in the [circuit audit](../circuits/index.md)
by using the bipartite sparsity.

The LTC statement alone is weaker. If one additionally knows
`C=image(F)` for `n` threshold functions on `m` inputs, then membership in `C`
has the nondeterministic verifier `exists h: F(h)=x`; this is a **conditional
transfer**. The published necessity result usually gives only
`C subseteq image(F)`, which is insufficient for membership testing and hence
is a **non-transfer** by itself.

Strong-mode lower bounds also do not become Boolean circuit lower bounds.
Strong modes depend on probability ratios, and a full-support distribution may
have a complicated mode pattern while its support circuit is the constant-one
circuit.

## Transfer ledger

| Primary result | Localization consequence | Circuit consequence | Classification |
|---|---|---|---|
| Fixed-size RBM represents `D` in the closed model | `L_2(D)<=m` | Sparse nondeterministic and `2^m`-expanded deterministic support circuits | **Exact transfer** |
| Fixed-size RBM approximates `D` arbitrarily well | Same after compactness and closure | Same after passing to a limiting joint law | **Closure transfer** |
| Montúfar--Ay `2^(n-1)-1` universality | Universal upper bound on `L_2` | Only exponential generic circuit upper bounds | **Closure transfer** |
| Montúfar--Rauh `U(n,n)=O(2^n log n/n)` universality | Improved universal upper bound on `L_2` | No new circuit upper bound versus elementary constructions | **Closure transfer** |
| Expected dimension of `RBM(n,m)` | No lower bound on unrestricted `L_2` | None | **Restricted-model result** |
| Strong-mode, zonoset, or LTC obstruction | No lower bound on unrestricted `L_2`; parity explicitly separates them | None for ordinary support circuits | **Restricted-model result / non-transfer** |
| Weight-and-margin RBM-network lower bound for inner product | No unconditional localization lower bound | A statement about shallow threshold/softplus representation, not support recognition | **Restricted-model result / non-transfer** |
| `C` is exactly an LTC image | No localization conclusion by itself | Nondeterministic threshold verifier for membership in `C` | **Conditional transfer** |

## Research use

The RBM literature contributes three useful ingredients without being mistaken
for the full localization model:

1. its approximation theorems immediately improve `L_2` upper bounds;
2. its mode, code, and zonotope invariants are candidates to generalize from
   bipartite energies to arbitrary quadratic ground-state projections; and
3. its free-energy/threshold-circuit dictionary suggests weight-sensitive
   refinements for full-support distributions.

The second item is the real lower-bound opportunity. A useful invariant must
survive visible--visible and hidden--hidden interactions; the published RBM
invariants, as stated, do not.

[gu19]: ../sources.md#gu19
[lerouxbengio08]: ../sources.md#lerouxbengio08
[martens13]: ../sources.md#martens13
[montufaray11]: ../sources.md#montufaray11
[montufarmorton15mixtures]: ../sources.md#montufarmorton15mixtures
[montufarmorton17]: ../sources.md#montufarmorton17
[montufarrauh17]: ../sources.md#montufarrauh17
