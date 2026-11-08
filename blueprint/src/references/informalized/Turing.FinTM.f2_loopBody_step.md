<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBody_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Loop-Body Machine

**Claim.** If the current base state is not the anchor with release false, then one augmented-machine step gives the lifted result of one base-machine step, resets release to false, and sets the extra-tape cell to true exactly when the base step halts, retaining its old contents otherwise.

**Proof.** Let $a$ be the base transition selected by the current state, input symbol, and work-tape symbols. The augmented configuration presents the same symbols on all original work tapes as the base configuration, so this is exactly the transition selected by the augmented machine's ordinary branch. The hypothesis excludes its special stopping branch, which is reserved for the anchor state with release false. On the original tapes and input head, the augmented transition makes precisely the same changes as $a$; it also appends the same output and enters the paired successor state with release component false. On the added tape, the transition writes true at the current head position (cell zero in the lifted configuration) if $a$ has no successor state, and otherwise makes no write, preserving the previous cell contents. These componentwise equalities establish the claimed lifted configuration.
