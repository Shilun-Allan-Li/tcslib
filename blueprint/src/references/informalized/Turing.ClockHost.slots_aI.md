<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.slots_aI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment to the Second Tape Block

**Claim.** At the combined index corresponding to any index $i$ in the second block, the function assembled from $f$, $g$, and $y$ has value $g(i)$.

**Proof.** The assembled function is the concatenation of the first block $f$, the second block $g$, and the final singleton value $y$. The index $aI(i)$ places $i$ in that second block, so evaluating the concatenation there returns $g(i)$. This is precisely the second-block evaluation rule for `Fin.append`, after unfolding the definitions of the assembled function and index.
