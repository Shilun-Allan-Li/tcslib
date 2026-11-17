<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.ao_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Transition of the Advice Machine

**Claim.** One step from state $q$ with the head at position $i+1$ is the result of applying the machine's prescribed transition action to that configuration, using the input bit at position $i$.

**Proof.** The input-symbol lemma says that a configuration whose shifted head position is $i+1$, with $i$ inside the input, reads precisely the input bit at index $i$ (\texttt{Turing.inputSymbolInner}). The configuration has state $q$, so the machine’s step is obtained by applying its transition action to the symbols it reads. Substituting the identified input symbol gives the claimed equality.

**Key facts.** `Turing.inputSymbolInner`.
