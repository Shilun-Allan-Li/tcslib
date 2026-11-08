<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer-State Halting

**Claim.** Starting in the answer state for $b$, with any register vector bounded by $B$, the machine halts with answer $b$, and every earlier configuration satisfies its precondition and register bound.

**Proof.** In the answer state, the machine instruction is exactly to return $b$. The precondition and register bound hold at the initial configuration: the former follows from the machine's precondition lemma, and the latter is the assumed bound on the register vector. The one-step halting property for return instructions (`AHalt.ret`) now gives the result.

**Key facts.** `Complexity.comp_preS`, `Complexity.LogProg.AHalt.ret`.
