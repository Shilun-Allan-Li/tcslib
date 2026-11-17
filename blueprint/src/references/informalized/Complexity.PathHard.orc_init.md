<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.orc_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Oracle Component

**Claim.** For every finite nondeterministic Turing machine $N$, bit strings $x,\beta$, and natural numbers $v,s$, the third oracle component on the specified encoded input returns true exactly when the pairing of $x$ with the binary representations of $v$ and $s$ belongs to $N$'s initial-configuration language.

**Proof.** The third component is the indicator of the language consisting of inputs whose decoded payload belongs to the initial-configuration language. An indicator is the Boolean decision of membership (Complexity.LogProg.indicator_eq_decide). For the given nested pairing, dropping the outer index encoding recovers precisely $\operatorname{pairEncode}(x,\operatorname{pairEncode}(\operatorname{bits}(v),\operatorname{bits}(s)))$ (Complexity.dropIdx_pairEncode). Thus the membership decision is exactly the one stated.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Complexity.dropIdx_pairEncode`.
