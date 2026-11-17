<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_buffer_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Administrative buffer action

**Claim.** Applying the buffer action changes the administrative state, moves the input head by the prescribed displacement with boundary clamping, and changes the capture-head position by the prescribed displacement, leaving the other configuration fields as specified.

**Proof.** Compare the two configurations field by field. The action assigns the successor state and has no output, so those fields agree with the stated result. Its input movement is exactly the definition of the clamped position $\mathrm{moveInputPos}(p,m)$. For each work tape, split according to whether its index lies among the logged source tapes. On those tapes the action makes no write and no movement; on the remaining buffer tape it likewise makes no write, and moves its head by $d$. Thus the tape contents remain unchanged and the capture-head position becomes $h+d$. The input position and all remaining fields consequently match the claimed administrative configuration.
