<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Successor-Field Run

**Claim.** After a number of steps equal to the length of the optional-state encoding, the machine reaches the configuration specified by `succFieldCfg`: the tag transition has occurred, the unary encoding of `s` has been copied to the destination exactly when `s` is present and copying is enabled, and the machine is done with live flag recording whether `s` is present.

**Proof.** Apply the intermediate-time run description (`succFieldTM_trace`) at the encoding length, which is permitted with equality. At positive time, the description gives the post-tag configuration followed by a unary scan of length one less than the encoding length, and puts the control in the done phase when the scan reaches its final symbol. If `s` is absent, its optional-state encoding is the single false bit, so the tag transition itself reaches done with false live flag and the scanned unary word is empty. If `s` is present, the encoding consists of the leading tag bit followed by the unary state word; the remaining scan length is exactly the length of that unary word, and the done phase has true live flag. In both cases, the resulting copied prefix is the full unary word when copying is enabled, as required by the stated configuration.

**Key facts.** `Turing.StepBlock.succFieldTM_trace`.
