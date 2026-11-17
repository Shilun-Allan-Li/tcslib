<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.laneCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the head of a lane tape

**Claim.** In the lane configuration with frontier $z$ and right list $r$, the designated tape's head reads the first entry of $r$, or blank if $r$ is empty.

**Proof.** The lane configuration places the sweep tape determined by $z,l,r$ on the designated work tape and places its head at $z$. The sweep tape reading lemma says that reading this tape at its frontier returns the head of the right list, with an empty or blank entry represented by blank (\(\texttt{Turing.FinTM.sweepTape_read}\)).

**Key facts.** `Turing.FinTM.sweepTape_read`.
