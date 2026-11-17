<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignPredicate.randomizedValue_scaled_sign_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Randomized Acceptance

**Claim.** If each mean is $(1-\delta)x_i$ for a fixed sign vector $x$ and $\delta\in[0,1]$, then the indicator that the predicate accepts $x$, less $m\delta/2$, is at most its randomized value.

**Proof.** If the predicate accepts $x$, consider the probability that all independently sampled signs equal their respective coordinates of $x$. Each coordinate has probability $1-\delta/2$ of matching its specified sign (\texttt{FABL.signPMFOfMean_scaled_sign_apply_self_toReal}), so independence gives probability $(1-\delta/2)^m$. The elementary Bernoulli bound $(1-t)^m\ge 1-mt$ for $0\le t\le1$ yields $(1-\frac m2\delta)$. On this all-matching outcome the predicate accepts, and all other contributions to its indicator expectation are nonnegative; hence the randomized value is at least this probability lower bound. If the predicate rejects $x$, the left side is $-m\delta/2\le0$, while every randomized value is nonnegative by the interval bound (\texttt{FABL.SignPredicate.randomizedValue_mem_Icc}).

**Key facts.** `FABL.signPMFOfMean_scaled_sign_apply_self_toReal`, `FABL.SignPredicate.randomizedValue_mem_Icc`.
