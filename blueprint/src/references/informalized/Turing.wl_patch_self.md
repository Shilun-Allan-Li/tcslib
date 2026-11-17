<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_patch_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Patch Self-Consistency

**Claim.** Under the recording hypothesis, patching the configuration with state $q$ and fields $f_s$ gives exactly the configuration obtained by changing only its state to $q$.

**Proof.** The state, input-head position, work-head positions, and output agree immediately by the definitions. It remains to check the work-tape contents. If a cell is outside the patch interval, the patch leaves it unchanged. If it is inside, it is on tape $0$ and its position has the form $d.\mathrm{workTapePos}(0)+r$, with $0\le r<\mathrm{length}(\mathrm{joinFields}(f_s))$. The recording hypothesis applies at offset $r$, so the old tape content there is precisely $\mathrm{fieldsTape}(f_s,r)$. This is the value written by the patch, since subtracting the head position recovers $r$. Thus every tape cell agrees, and the configurations are equal.
