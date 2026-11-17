<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of the transducer

**Claim.** For every state $q$ and finite bit string $w$, applying the transducer twice, each time starting in state $q$, returns $w$.

**Proof.** Induct on the input string, allowing the starting state to vary in the induction hypothesis. The empty string is fixed. For a string beginning with $b$ and followed by $w$, the leading-bit rule (`T_cons`) says the first application outputs the swapped bit and processes the suffix from the state reached after reading $b$. The transition state is the same whether the transition reads $b$ or its swapped value. Also, swapping twice in the original state returns $b$: the only nontrivial case is state $k_2(0)$, where swapping complements the bit twice; in all other states the bit is unchanged. Applying the leading-bit rule again, these two facts reduce the twice-transformed suffix to applying the transducer twice from the intervening state. The induction hypothesis returns the original suffix, and the first bit is $b$, proving the claim.

**Key facts.** `BoolCircuit.CktSatReduction.T_cons`.
