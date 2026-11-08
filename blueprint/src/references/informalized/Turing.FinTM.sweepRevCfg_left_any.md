<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepRevCfg_left_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep with an Arbitrary Right Stack

**Claim.** Applying the action that writes $b$, moves the work head left, and enters state $q'$ to the backward-sweep configuration with right stack $r$ produces the configuration with state $q'$, the same input-head position and output, frontier $z-1$, left stack $b::l$, and right stack $r.tail$.

**Proof.** Split on the right stack. If $r=a::r'$, the claim is exactly the one-cell frontier step: writing at the frontier and shifting the zipper gives left stack $b::l$ and right stack $r'$ (`Turing.FinTM.sweepRevCfg_left`). If $r$ is empty, first replace it by the singleton blank stack $[none]$. This does not change the represented tape, since an empty right stack and one blank right cell define the same tape (`Turing.FinTM.sweepTape_nil`). The one-cell frontier step then applies with $a=none$; the new right stack is empty, which is the tail of the original empty stack. In both cases the desired configuration follows.

**Key facts.** `Turing.FinTM.sweepRevCfg_left`, `Turing.FinTM.sweepTape_nil`.
