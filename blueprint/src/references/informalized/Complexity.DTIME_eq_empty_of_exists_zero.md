<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/DTIME.lean :: Complexity.DTIME_eq_empty_of_exists_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Zero Time Bound Forces Emptiness

**Claim.** If $T(n)=0$ for some natural number $n$, then $\mathrm{DTIME}(T)$ is empty.

**Proof.** Choose $n$ with $T(n)=0$. If a language belonged to $\mathrm{DTIME}(T)$, some machine with time constant $c$ would decide it on every input in time $cT(|x|)$. Apply this requirement to the input consisting of $n$ copies of `false`, whose length is $n$. Its prescribed time is $cT(n)=0$. But `not_computesInTime_zero` says that no machine computes any input-output pair in zero steps. This contradiction rules out every language in the class, so the class equals the empty set.

**Key facts.** `Turing.FinTM.not_computesInTime_zero`.
