<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCall_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Call Frame Representation

**Claim.** Every loop-call configuration equals its frame representation, with the call state, the body configuration's input position, the designated flag, counter, and payload tapes and head positions, and empty output as specified.

**Proof.** Both configurations have the same state, input-head position, and output by their definitions. To compare their work tapes and head positions, consider a tape index. At index $\mathrm{body.k}$, the padded body configuration supplies the flag tape and head position zero. At index $\mathrm{body.k}+1$, the frame supplies the counter tape and its prescribed head position; at index $\mathrm{body.k}+1+(1+F.\mathrm{k})$, it supplies the payload tape and head position. Every other index is left as the corresponding base tape and head by the frame construction. These cases exhaust the work tapes, so the two configurations agree componentwise.
