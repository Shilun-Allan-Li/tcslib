<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedFrame_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Correspondence for Framed Configurations

**Claim.** One step of the capture machine from a framed configuration equals the frame of the timed interpreter’s one-step successor.

**Proof.** Split according to whether the timed interpreter’s configuration is halted. If it is halted, its step leaves the configuration unchanged; the framed configuration is also halted, so its step likewise leaves it unchanged (`Turing.MultiTapeTM.step_of_halt`). Now suppose its state is active, say $q$. The framed state is then the corresponding active capture state. The framed read symbols agree with the interpreter’s read symbols by the reads lemma (`Turing.timedFrame_reads`), and the input symbol is unchanged because framing preserves the input-head position. Thus the capture transition uses exactly the action of the timed interpreter on the same state and readings. Applying that action to the frame produces the frame of the interpreter’s updated configuration, by the compatibility of framing with action application (`Turing.timedFrame_apply`). This is the desired equality.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.timedFrame_reads`, `Turing.timedFrame_apply`.
