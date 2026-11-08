<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Randomized.halted_rounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rounds Until a Halted Run Satisfies a Property

**Claim.** Under the stated block-step conditions, every halted run of length $Rj$ from a ready initial configuration ends in a configuration satisfying $P$.

**Proof.** Proceed by induction on the number $j$ of blocks, allowing the initial configuration and choice word to vary. When $j=0$, the choice word has length zero and is empty, so the run leaves the initial configuration unchanged. That configuration is ready and hence nonhalted, contradicting the assumption that the final run is halted; thus the implication holds.

For the induction step, split the choice word into its first $R$ choices and the remaining choices. The first block has length $R$. By hypothesis, after this block either the machine is halted and satisfies $P$, or the resulting configuration is ready. In the first case, additional choices leave a halted configuration unchanged (Turing.NDTM.runWith_of_halt), so the final configuration satisfies $P$. In the second case, the remaining word has length $Rj$, as follows from the total length $R(j+1)$. The induction hypothesis applied to this ready configuration and the remaining word gives $P$ at the end of the full run; the identification of the full run with these two successive runs follows from concatenation of runs (Turing.NDTM.runWith_append).

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
