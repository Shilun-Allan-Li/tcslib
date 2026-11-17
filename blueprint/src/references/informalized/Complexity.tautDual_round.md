<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Complete Transducer Round

**Claim.** For every binary string $x$, the dual transducer has a positive-length run of at most $4|x|+5$ steps that returns to its anchor configuration with output equal to the guarded dual output of $x$, and it does not visit the anchor state at any intermediate time.

**Proof.** First, the anchor transition releases the machine into the formula-scanning state at position $1$, without changing the input head’s position or the empty output. This follows by inspecting the transition and using that a zero head movement leaves the position fixed (`Turing.moveInputPos_zero`). Next, split according to whether the syntax scan of $x$ ends in the exact-end state. In that case, the valid-input run lemma (`Complexity.tautDual_valid`) gives a segment of length $4|x|+4$ from the released configuration back to the anchor with the polarity-flipping scan as output. Otherwise, the invalid-input run lemma (`Complexity.tautDual_invalid`) gives such a segment of length $2|x|+2$ with output `[false]`. These outputs are precisely the two branches of the guarded dual output. Prepending the release step gives a total length one larger, which is positive and at most $4|x|+5$. Every intermediate time after the initial release corresponds to a time strictly before the end of the chosen segment, so the segment’s anchor-avoidance property rules out an intermediate anchor visit. Finally, the segment endpoint is identified with the stated anchor configuration by equality of its state, position, and output; since there are no work tapes, these fields determine the whole configuration (`Turing.Cfg.ext_zero_tapes`). The decomposition of the run after its first step is the run-after-one-step law (`Turing.MultiTapeTM.runFrom_succ_eq_step`).

**Key facts.** `Complexity.tautDual_valid`, `Complexity.tautDual_invalid`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.Cfg.ext_zero_tapes`.
