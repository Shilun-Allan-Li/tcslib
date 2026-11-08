<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBodyImage_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Prefix Loop-Body Images

**Claim.** When $c.output=[]$, applying the loop-body image with empty prefix, direction $f$, and startup marker $s$ to the padded configuration built from $c,r,g,w,e$ gives the loop-call configuration built from the same data and marker.

**Proof.** If the direction bit is false, the loop-body image is defined directly as the loop-call configuration, so the two sides agree by unfolding their definitions. If the direction bit is true, the image is the forward loop configuration. The empty-output condition means that adding the empty prefix does not change the body’s output, and the forward loop representation of an empty output agrees with the loop-call representation (`emLoopCall_empty`).

**Key facts.** `Turing.FinTM.emLoopCall_empty`.
