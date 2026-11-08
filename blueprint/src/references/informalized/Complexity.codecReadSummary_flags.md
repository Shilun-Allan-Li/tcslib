<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecReadSummary_flags -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of an output summary

**Claim.** For every output summary $o$, the flags indicating whether $o$ is the accepting summary or the dead summary recover $o$.

**Proof.** Check the three possible summaries. For the empty summary both flags are false, so the reader returns empty. For the accepting summary only the accepting flag is true, so it returns accept. For the dead summary the dead flag is true, so it returns dead.
