# Localization at fixed total-variation error

The current proofs are in the approximation section of [main.tex](../main.tex).
The four results are manuscript proofs with no Lean counterparts; their exact
boundary is recorded in [FORMALIZATION.md](../FORMALIZATION.md).

## Outcome

For fixed locality `k >= 2`, bias `0 < beta < 1`, and error
`0 < epsilon < beta/2`, the exchangeable law

`P_n,beta(x) = 2^(-n) (1 + beta (-1)^|x|)`

has approximate localization complexity

`LC_k,epsilon(P_n,beta) = (1/2) log2(n) + O_(k,beta,epsilon)(1).`

Both bounds include the full model: arbitrary interaction coefficients,
visible--visible and hidden--hidden interactions, and boundary joint laws.
The lower bound applies to every approximating visible law, including
asymmetric ones. The upper bound first uses a boundary joint law.
Using half the error allowance for the window and then a finite penalty
for its exposing energy gives a strictly positive quadratic joint law at
the same asymptotic hidden-bit cost.

The choice `beta = 1/2` has probability `3/2^(n+1)` at each even string
and `1/2^(n+1)` at each odd string. It is rational, has full support, and
has likelihood ratio three. At `epsilon = 1/16`, the finite lower bound is

`LC_k,1/16(P_n,1/2) >= (1/2) log2(n+1) - log2(2(k+1))`

for `n > k`. Uniform is at TV distance exactly `1/4`, explaining the
endpoint of the positive-error regime. This family is the existing noisy
parity law at the fixed parameter `t = 1/3`; no cold threshold is needed
for the new lower bound.

## Mechanism

Each hidden assignment supplies a nonnegative slice of the visible density.
Every positive superlevel set of that slice is a degree-k polynomial threshold
set. A sufficiently large multiple of the exposing energy removes points
outside its support without raising degree.

Clipping a slice at the target's largest density turns its correlation with a
balanced Boolean function into an integral of threshold correlations.
Summing over the hidden assignments then bounds the target bias by the
approximation error plus `2^ell` times threshold discrepancy. This step
does not assume conditional independence or an upper bound on a slice's peak.

For parity, threshold discrepancy is `O(k/sqrt(n))`. The upper bound
encodes only a central interval containing `O(sqrt(n))` Hamming weights.
Binary encoding uses `(1/2) log2(n) + O(1)` hidden bits; its lowest bit
supplies the even/odd weight ratio. Chebyshev's inequality controls the
discarded probability.

For completeness, the central-binomial estimate used in the paper has an
elementary induction. If `c_n = 2^(-n) binom(n,floor(n/2))`, then
`c_(2m+1) = c_(2m+2) = ((2m+1)/(2m+2)) c_(2m)`.
Starting with `c_0 = 1`, the inequality
`(2m+1)(2m+3) <= (2m+2)^2` proves `c_n^2 (n+1) <= 1`.

The older analytic exchangeable family behaves differently at fixed error:
its TV distance to uniform is at most `e^3 log(2)/sqrt(n)`.
The paper now proves this explicitly. Its exact algebraic lower bound does
not supply a fixed-error separation.

## Transfer to and from Boolean complexity

For balanced `f`, bias `0 < beta <= 1`, `delta > 0`, and
`0 <= epsilon < beta/2`, the paper's discrepancy lemma gives

`Delta_k(f) <= delta`

`=> LC_k,epsilon(D_f,beta) >= log2((beta-2*epsilon)/((1+beta)*delta)).`

The restriction fixes hidden bits and leaves all visible inputs free.
Clipping makes the resulting estimates additive. Counting `2^ell`
assignments explains the logarithmic conversion to hidden-bit complexity.

For the reverse transfer, an s-gate NAND circuit computing `(1+f)/2`
has a unique quadratic gate trace over each input. With `0 < beta < 1`,
weight its output bit o by the affine potential
`log(1-beta) + o*log((1+beta)/(1-beta))`. This gives an exact quadratic
lift of the biased law with s hidden gate wires. Thus its approximate
localization complexity lower-bounds that circuit size.

The current estimate discards the compatibility between slices inherited
from their shared joint energy and potential. Exploiting that compatibility,
positivity, or marginal geometry could strengthen the transfer. The current
parity result imports a classical Boolean lower bound.

## Source check and remaining questions

The parity threshold ingredient is classical:
[Aspnes, Beigel, Furst, and Rudich, Theorem 2.2](https://www.cs.yale.edu/homes/aspnes/papers/stoc91voting.pdf).
The manuscript gives its short dimension argument.
[The journal record](https://doi.org/10.1007/BF01215346) confirms the
bibliographic metadata. Section 5 of the same paper derives parity lower
bounds for AC0 with one majority gate from the polynomial method.
The theorem was checked on 2026-09-05 and the circuit connection on
2026-09-06; these were not comprehensive priority searches for the
localization transfer.

An explicit **superlogarithmic** lower bound at fixed TV error remains open
in this repository. So do the approximate worst-case and exchangeable scales,
coefficient-bounded variants, and Lean formalization of these results.

## Finite validation protocol

Run `python3 research/validate_robust_parity.py`, also included in
`make check-finite`. Python 3.10 or newer and its standard library suffice.
All calculations use exact integers and fractions; there is no random seed.

- Central-binomial and discrepancy-bound arithmetic: every
  `1 <= n <= 256`, `0 <= k < n`.
- Polynomial thresholds: every coefficient vector in `{-1,0,1}` for the
  complete multilinear feature basis, `1 <= n <= 3`, `0 <= k < n`.
  This includes ties but does not enumerate all real-coefficient thresholds.
- Clipped-mixture inequality: all nonzero 4-by-2 joint weight tables over
  `{0,1,4}`, all six balanced sign functions, and biases `1/4,1/2,1`.
  These use the actual slice discrepancy and make no locality assumption.
- Window construction: every `1 <= n <= 512`, biases `1/4,1/2,3/4`,
  and errors `beta/4,beta/8`. Check exact discarded mass, conditioning TV,
  interval coverage, binary reconstruction, and parity.
  For `n <= 12`, also exhaust every hidden code at each Hamming weight
  to check zero-energy witness uniqueness.

These finite checks catch arithmetic and construction errors. The manuscript
proofs supply the quantified conclusions.
