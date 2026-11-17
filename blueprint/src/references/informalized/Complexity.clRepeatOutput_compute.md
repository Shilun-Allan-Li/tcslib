<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeatOutput_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Bound for Repeated Iteration

**Claim.** Under the clean-call and iterate-length hypotheses, the repetition-output machine computes $f^{[N]}(s)$ from the packed repetition argument within the stated time bound.

**Proof.** Let $\mathrm{arg}$ be the packed encoding and let $W$ bound the lengths of the first $N+1$ iterates. Each tape word in the repetition argument has length at most $|\mathrm{arg}|$, since every field's word length is bounded by the total encoded field length (`Complexity.clFields_width`). For each $j<N$, apply the clean-call hypothesis to the argument $f^{[j]}(s)$. Its length is at most $W$, so its running time is at most $a(W+1)^d$. The repetition controller's bounded-completion result therefore reaches its completed state with word $f^{[N]}(s)$ in some time $b\le N(a(W+1)^d+2)+1$ (`Complexity.clRepeat_complete`). The encoded initial configuration is the controller's start configuration (`Complexity.clRepeat_initial`). The preparation machine then reaches the corresponding prepared configuration within a time $u\le 2|\mathrm{arg}|+4+(C.k+1)(3|\mathrm{arg}|+7)$ (`Complexity.clPrepared_run`); applying it to the controller's run gives the prepared configuration containing the completed word. At that point the prepared machine is in its designated return state, where it remains idle (`Complexity.clPrepared_idle`). The output-reading result now copies the word to the output in a further $b+u+|f^{[N]}(s)|+4$ steps, using the designated output tape and its known head position (`Complexity.clOutputAt_compute`). The length of the final iterate is at most $W$. Adding these bounds, and using that a computation that finishes by a given time also finishes at any larger time (`Turing.FinTM.ComputesInTime.mono`), yields the stated bound.

**Key facts.** `Complexity.clFields_width`, `Complexity.clRepeat_complete`, `Complexity.clRepeat_initial`, `Complexity.clPrepared_run`, `Complexity.clPrepared_idle`, `Complexity.clOutputAt_compute`, `Turing.FinTM.ComputesInTime.mono`.
