<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NTIME.lean :: Complexity.NTIME_eq_empty_of_exists_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Zero Time Bound Forces Emptiness

**Claim.** If $T(n)=0$ for at least one input length $n$, then $\mathrm{NTIME}(T)=\varnothing$.

**Proof.** Choose $n$ with $T(n)=0$, and suppose a language $L$ were decided by a nondeterministic machine $N$ within $cT(m)$ steps. Apply the halting requirement to the input consisting of $n$ false bits. Its allowed time is $cT(n)=0$, so the empty choice sequence must already leave the initial configuration in the halting state. But the initial configuration has state $q_0$, hence state $\operatorname{some}(q_0)$, which cannot equal the halting state $\operatorname{none}$. This contradiction rules out every language from the class.
