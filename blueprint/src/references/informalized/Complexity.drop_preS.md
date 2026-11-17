<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_preS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preconditions for Drop Instructions

**Claim.** For every mode, input bit string, and configuration of the specified computation, the instruction-dependent conditions in the statement hold.

**Proof.** Split on whether the configuration has an active state. A halted configuration has no instruction preconditions to check. For an active state, inspect the instruction assigned by the machine. Most states impose no condition, and their cases are immediate. In a copy state with no pending increment, the two register indices being compared are distinct, as verified for each copy stage. In scan and second-bit states, pointer register $0$ differs from the layer's limit register. The remaining parameter-dependent states impose no additional obligations: examining their Boolean cases reduces the checks to these same instruction forms or to conditions that hold automatically. Thus every possible active instruction satisfies the required preconditions.
