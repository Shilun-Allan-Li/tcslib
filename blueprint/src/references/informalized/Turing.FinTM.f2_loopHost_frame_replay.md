<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_frame_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Payload Replay Reaches Halt

**Claim.** Starting in phase 13 with payload word $w$ at cell zero, payload head at zero, and empty output, the loop host halts after $|w|+1$ steps with output exactly $w$.

**Proof.** The proof first identifies the given framed configuration with the specialized replay configuration used by the replay simulation lemma. The tape and head components agree by splitting the tape indices into the host's control tape and the remaining tapes; the definitions of the frame and replay configuration then give equality of the configurations. Apply the payload replay simulation (`f2_loopHost_replay`): after $|w|+1$ steps, the control remains in phase 13, the payload head has advanced to the end of the word, the payload tape still stores the word, and the output is the initial output followed by $w$. Here the initial output is empty. The replay lemma also states that the final state is the phase-13 control state; the surrounding halted-state conclusion follows from the replay configuration's state component as used in the simulation result.

**Key facts.** `Turing.FinTM.f2_loopHost_replay`.

**Caveat.** The supplied replay lemma concludes with phase 13, whose state is not `none` according to the given host transition definition. The proof source derives the claimed halted-state conjunct by reflexivity after applying that lemma, but the provided definitions do not support this step.
