<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.PathHard.implicitlyLogspaceComputable_red -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Computability of the Reduction

**Claim.** The reduction has polynomially bounded output length, and the languages deciding its indexed output bits and output positions are both decidable in logarithmic space.

**Proof.** Fix either Boolean query mode. The corresponding query language is decidable in logarithmic space by the program simulation theorem (`Complexity.LogProg.arm_decides_poly`): use the program beginning at its length-query state, the five deciders supplied by `As_mem`, and the halting behavior established by `query_halts`. That halting result uses a bound depending on the query input; the lemma `qBnd_le` bounds it by a fixed constant times a fixed power of the input length plus one, so every configuration also meets the polynomial register bound required by the simulation theorem. The two modes give, respectively, the indexed-bit language and the output-position language in the definition of implicit logspace computability. Finally, `length_red_le` supplies the required polynomial bound on the reduction's output length.

**Key facts.** `Complexity.LogProg.arm_decides_poly`, `Complexity.PathHard.As_mem`, `Complexity.PathHard.query_halts`, `Complexity.PathHard.qBnd_le`, `Complexity.PathHard.length_red_le`.
