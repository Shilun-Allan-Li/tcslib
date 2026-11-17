<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.tact_idle_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect with Idle Original Tapes

**Claim.** When the action leaves every original work tape idle, applying it preserves those tapes and produces the stated successor state, moved input head, auxiliary-tape updates and movements, and appended optional output.

**Proof.** Apply the general action-effect result (`Complexity.Meyer.tact_apply`) with the original-tape instruction set equal to the idle instruction. The original-tape content function is therefore unchanged, and each original head position has zero movement. The auxiliary-tape content and head-position formulas from that result reduce, coordinate by coordinate, to the three updates and movements stated here. The state, input-head position, and output components are already the claimed successor state, moved position, and appended output.

**Key facts.** `Complexity.Meyer.tact_apply`.
