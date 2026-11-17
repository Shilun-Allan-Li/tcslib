<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting from an Answer State

**Claim.** From an answer state for $b$, with all nine register values at most $4|h|+4$ and no answer yet recorded, the computation halts with answer $b$, and every preceding configuration satisfies the invariant.

**Proof.** At the answer state the machine instruction is precisely the return instruction for $b$. The answer-state halting principle (`Complexity.LogProg.AHalt.ret`) therefore gives termination with that answer as soon as the invariant holds at the starting configuration. Its safety component follows from the register bound assumed here and the fact that every state satisfies the instruction preconditions (`Complexity.drop_preS`).

**Key facts.** `Complexity.LogProg.AHalt.ret`, `Complexity.drop_preS`.
