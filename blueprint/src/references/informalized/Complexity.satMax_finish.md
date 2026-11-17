<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMax_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of counter replay

**Claim.** From the streaming entry configuration with a unary counter of length $n$, arbitrary buffer, and empty output, the machine reaches the halted configuration after $n+1$ steps, with counter head at $n$ and output consisting of $n$ true bits.

**Proof.** The prefix lemma identifies the configuration after $n$ steps: the machine is still in the streaming entry state, the counter head is at $n$, the buffer and input positions are unchanged, and the output is $n$ true bits (Complexity.satMax_prefix). At this point the counter head reads blank, because the unary counter has true symbols only at positions strictly below $n$ (Complexity.satRedCounter_read). Thus the next transition takes the counter-exhaustion branch and halts. It leaves the input head fixed, does not alter either tape, and emits no further symbol, so the resulting configuration is exactly the asserted one. The run decomposition into the first $n$ steps and the final step is the standard successor-step identity (Turing.MultiTapeTM.runFrom_succ_eq_step'); a zero input-head movement leaves its position fixed (Turing.moveInputPos_zero).

**Key facts.** `Complexity.satMax_prefix`, `Complexity.satRedCounter_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
