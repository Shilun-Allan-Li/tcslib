<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFrame_counter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Tape in a Loop Frame

**Claim.** In the loop-frame configuration, the symbol scanned on work tape $B.k+1$ is the counter tape's content at the counter-head position $ch$.

**Proof.** The frame assigns the counter tape to index $B.k+1$ and assigns that tape's head position to $ch$. By definition, the scanned symbol is the content of the selected tape at its head position. Substituting these assignments gives $\mathrm{counter}(ch)$.
