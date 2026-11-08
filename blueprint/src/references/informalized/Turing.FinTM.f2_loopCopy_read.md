<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCopy_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Next Copy Symbol

**Claim.** For any Boolean words $p$ and $r$, the tape $T(p,r)$ contains the first symbol of $r$ at cell $|p|$, with a blank there when $r$ is empty.

**Proof.** At cell $|p|$, the cutoff in the definition of $T(p,r)$ does not blank the cell. The buffer lookup for the concatenated word $p++r$ at position $|p|$ returns the head of $r$, or blank if $r$ is empty. This is exactly the buffer-read fact (\texttt{f2\_loopBuffer\_read}).

**Key facts.** `Turing.FinTM.f2_loopBuffer_read`.
