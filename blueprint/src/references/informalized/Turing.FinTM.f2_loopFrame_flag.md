<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFrame_flag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flag Tape in a Loop Frame

**Claim.** In the loop-frame configuration, the symbol scanned by work tape $B.k$ is the flag tape's content at position $0$.

**Proof.** The frame assigns the flag tape to index $B.k$ and places its head at position $0$. The scanned symbol is the content of that tape at its head position, hence it is $\mathrm{flag}(0)$.
