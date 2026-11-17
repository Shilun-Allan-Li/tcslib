<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFrame_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload Tape in a Loop Frame

**Claim.** In the loop-frame configuration, the symbol scanned by the last work tape is the payload tape's content at the chosen payload-head position $ph$.

**Proof.** The last work-tape index is $B.k+1+(1+F.k)$, the index at which the frame assigns the payload tape. This index is distinct from the flag-tape index $B.k$, so the frame's tape-selection conditions identify its content as the payload tape. The frame also assigns its head position to $ph$. By the definition of the scanned symbol, the result is $\mathrm{payload}(ph)$.
