<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_BPP_PTMWith_of_inBPPWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Characterization Implies Randomized Polynomial Time

**Claim.** If a polynomial-time Boolean verifier has the stated acceptance and rejection probability bounds using uniformly random bit strings of length $a(|x|+1)^k$, then a finite nondeterministic Turing machine decides the language with those bounds in polynomial time and halts on every choice string of the prescribed length.

**Proof.** Take a verifier and parameters witnessing the hypothesis. The efficient-verifier construction supplies a finite nondeterministic Turing machine, together with polynomial time-bound parameters, that halts on every choice string of the prescribed length. It also identifies the machine's output probabilities for the two Boolean outputs with the verifier's probabilities on uniformly random strings of the specified length (`Randomized.exists_FinNDTM_of_eff`). For each input, split into the cases that it belongs to the language or does not. In the first case, the verifier's acceptance bound transfers to the machine's probability of outputting the membership indicator; in the second, its rejection bound transfers likewise. Thus the constructed machine witnesses membership in the randomized polynomial-time class.

**Key facts.** `Randomized.exists_FinNDTM_of_eff`.
