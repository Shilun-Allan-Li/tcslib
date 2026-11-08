<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.timeConstructible_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time Constructibility

**Claim.** The function $T(n)=2^n$ is time constructible: it dominates $n$, and a finite binary Turing machine outputs the little-endian binary representation of $2^{|x|}$ within a constant multiple of $2^{|x|}+1$ steps.

**Proof.** The inequality $n\le2^n$ is the standard exponential domination of the natural numbers. Use the machine that emits one false bit for each input bit and then appends a true bit. After $|x|$ steps, `twoPowTM_run` gives a configuration in the active state with input-head position $|x|+1$ and output consisting of $|x|$ false bits. At the next step the input head is at the right boundary, so the scanned input symbol is blank; the machine halts and appends the final true bit. The resulting output is $\mathrm{replicate}(|x|,\mathrm{false})$ followed by true, which is the little-endian representation of $2^{|x|}$ by `bits_two_pow`. Thus it computes the required output in $|x|+1$ steps. Since $|x|+1\le2^{|x|}+1$, the runtime is within the required bound with constant $1$; the computation-time monotonicity lemma permits this extension (`ComputesInTime.mono`).

**Key facts.** `Complexity.twoPowTM_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.bits_two_pow`, `Turing.FinTM.ComputesInTime.mono`.
