<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecSummaryWord_summary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary Word Decoding

**Claim.** For every output summary, applying the summary function to its encoded Boolean word recovers that summary.

**Proof.** Check the three possible summaries. The empty summary is encoded by the empty list, whose summary is empty. The accepting summary is encoded by $[\mathrm{true}]$, whose summary is accepting. The dead summary is encoded by $[\mathrm{false}]$, which is neither empty nor exactly $[\mathrm{true}]$, so its summary is dead.
