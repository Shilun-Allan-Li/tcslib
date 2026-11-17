<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.gb_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds Imply the Guard

**Claim.** If every entry of a state record is at most $B$, then for every program label the configuration with that label, those register values, and no answer yet satisfies the guard: its registers remain bounded by $B$ and its instruction meets the precondition.

**Proof.** The guard has two parts: the instruction precondition and the register bounds. For the configuration at any label, `preS_A` supplies the precondition. The record bound transfers to the register vector through `St.Bd.toV`, giving that every register value is at most $B$. Together these establish the guard.

**Key facts.** `Complexity.PathHard.preS_A`, `Complexity.PathHard.St.Bd.toV`.
