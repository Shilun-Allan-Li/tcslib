<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.orc_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Oracle Component

**Claim.** For every finite nondeterministic Turing machine $N$, bit strings $x,\beta$, and natural numbers $u,v,s$, the fifth oracle component on the specified encoded input returns true exactly when there is a valid one-step transition from a configuration of code $u$ to one of code $v$, with both configurations in the radius-$s$ work-tape window.

**Proof.** The fifth component is the indicator of the language whose decoded payload belongs to the step language. Its value is therefore the decision of membership in that language (Complexity.LogProg.indicator_eq_decide). Dropping the outer index encoding from the given input yields the pairing of $x$ with the binary representations of $u,v,s$ in the order used by the step relation (Complexity.dropIdx_pairEncode). By the definition of that relation, membership asserts precisely the existence of the two in-window configurations, their respective codes, and a valid one-step transition between them.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Complexity.dropIdx_pairEncode`.
