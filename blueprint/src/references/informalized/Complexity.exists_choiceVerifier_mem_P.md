<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.exists_choiceVerifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Choice-Word Verifier

**Claim.** For a nondeterministic binary Turing machine and natural numbers $C,c$, there is a language in polynomial time that accepts the concatenation $xu$, for choice words of the specified length, exactly when the run on $x$ using $u$ halts with output $[1]$.

**Proof.** Take the language `choiceVerifier N C c`. Its polynomial-time membership is established by `cont_choiceVerifier_mem_P`. For any $x,u$ with $|u|=C(|x|+1)^c$, the verifier's defining membership property, `choiceVerifier_append`, says precisely that $xu$ belongs to this language if and only if the run of $N$ on input $x$ driven by $u$ halts with output $[1]$. These facts give the required language and equivalence.

**Key facts.** `Complexity.cont_choiceVerifier_mem_P`, `Complexity.choiceVerifier_append`.
