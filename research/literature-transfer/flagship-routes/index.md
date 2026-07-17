# Flagship theorem routes

The manuscript was proof-complete at its previous level, but a top-tier
complexity submission still needed one theorem whose significance was not
carried by generic dimension counting or an artificial superincreasing
encoding.  This dossier records the outcomes of the three routes identified by
the final hostile review.

## Admission rule

A route advances the paper only if it produces at least one of:

1. a complete theorem and proof that can enter the manuscript;
2. a reproducible computation that falsifies or materially narrows a proposed
   conjecture; or
3. a formal reduction showing that the desired statement would resolve a
   recognized open problem, together with the strongest unconditional fragment
   that survives the reduction.

## Parallel routes

- [Natural full-support families](natural-full-support.md): seek a moderately
  conditioned explicit family with a superlogarithmic localization lower bound.
- [Explicit selector obstructions](selector-explicit.md): turn the filtered
  witness-slice invariant into a lower bound for a structured support family.
- [Circuit consequences](circuit-consequences.md): seek a new upper/lower bound
  or completeness statement for a standard circuit or recognition model.

## Decision ledger

| Route | Candidate flagship theorem | Current status | Admission outcome |
|---|---|---|---|
| Natural full support | The explicit radial law `D_n(x) proportional to exp(-2^(|x|/r_n))` has `L_k(D_n)=Theta_k(n^(1/k))` for every fixed `k>=2`, while `max D_n/min D_n<e^3`. | Complete proof and finite sanity check; external expert novelty review remains advisable. | **Admit as the flagship theorem.** |
| Explicit selector | The separated block-layer support has exact one-block complexity `r` and exact block-symmetric `m`-block complexity `mr`. | Complete proofs for those two regimes; the unrestricted `m`-block direct sum remains open. | **Admit as a supporting theorem and barrier; reject as the present flagship.** |
| Circuit consequence | Dense exact recognition is quasipolynomial for fixed locality and a linear latent budget, with a sharper fixed-budget full-support algorithm and an ETH barrier to NP-hardness. | Complete proof and exact-arithmetic sanity check; the polynomial-time boundary remains open. | **Admit as a secondary algorithmic theorem; reject as the flagship.** |

## Assembly checklist

- Compare all candidate theorems using the same model conventions as the paper.
- Verify every quantitative claim with a worked proof or a script under
  `data/`.
- Compile any new primary sources into the corpus bibliography.
- Promote only claims that survive an adversarial mathematical review; the
  admission labels above assess the completed route phase, not external
  publication priority or novelty certification.
