<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_RP_PTMWith_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of One-Sided Randomized Time

**Claim.** For every probability function $p$ and language $L$, membership in the polynomial-time one-sided randomized class with acceptance threshold $p$ is equivalent to having a polynomial-time verifier with polynomially many random bits that meets the same acceptance threshold and always rejects nonmembers.

**Proof.** 1. Suppose $L$ is decided by a finite nondeterministic machine $N$ within time $c(|x|^e+1)$, with acceptance probability at least $p(|x|)$ on members and certain rejection on nonmembers. The choice-verifier construction (`Complexity.exists_choiceVerifier_mem_P`) gives a polynomial-time language whose membership, on a sufficiently long choice string, expresses that $N$ halts and outputs true. Let the verifier accept when the concatenation of input and random string belongs to this language; its efficiency follows from `Randomized.eff_append_mem`.

2. The verifier uses $2c(|x|+1)^e$ random bits. The choice-budget bound (`Turing.choiceBudget_le`) ensures this is at least the machine's running-time bound. The probability agreement theorem (`Randomized.randProb_choiceVerifier`) then identifies the verifier's acceptance probability with the machine's output probability, preserving the threshold $p(|x|)$. On a nonmember, every machine choice string of the running-time length rejects. The correspondence between the verifier language and machine outputs, together with `Randomized.append_mem_iff_outputWith_take` and `Randomized.indicator_eq_false_iff`, therefore shows that every verifier random string is rejected.

3. Conversely, suppose a polynomial-time verifier has the stated guarantees. Its efficiency yields a finite nondeterministic machine by `Randomized.exists_FinNDTM_of_eff`, with a polynomial running-time bound. The construction preserves the verifier's output distribution, so members retain acceptance probability at least $p(|x|)$. For a nonmember, the verifier rejects every random string; the machine's output on any choice string is the verifier's output on a corresponding random string, as guaranteed by the same construction. Hence the machine rejects on every branch, proving membership in the one-sided randomized time class.

**Key facts.** `Complexity.exists_choiceVerifier_mem_P`, `Randomized.eff_append_mem`, `Turing.choiceBudget_le`, `Randomized.randProb_choiceVerifier`, `Randomized.append_mem_iff_outputWith_take`, `Randomized.indicator_eq_false_iff`, `Randomized.exists_FinNDTM_of_eff`.
