<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBody_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stopping at the Anchor State

**Claim.** When the base configuration is in the anchor state and release is false, one augmented-machine step halts the base computation, leaves release false, and sets cell zero of the extra tape to false.

**Proof.** At the anchor state with release false, the augmented transition takes its special stopping branch. This branch leaves every original tape unchanged, makes no output, and has no successor state; on the added tape it writes false without moving its head. The input head also stays fixed, since a zero movement leaves its position unchanged (`moveInputPos_zero`). The resulting configuration is therefore the lift of the same base configuration with its state replaced by none, release still false, and the extra-tape flag equal to false.

**Key facts.** `Turing.moveInputPos_zero`.
