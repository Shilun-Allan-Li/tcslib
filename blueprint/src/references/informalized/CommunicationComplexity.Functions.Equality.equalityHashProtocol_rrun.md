<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean :: CommunicationComplexity.Functions.Equality.equalityHashProtocol_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality protocol output

**Claim.** The equality hashing protocol outputs true exactly when the hashes of the two inputs agree.

**Proof.** Unfolding the protocol execution, Alice sends $h(x)$, and Bob compares that value with $h(y)$. Thus the output is the decision of $h(y)=h(x)$. Equality is symmetric, so this Boolean decision is the same as the decision of $h(x)=h(y)$.
