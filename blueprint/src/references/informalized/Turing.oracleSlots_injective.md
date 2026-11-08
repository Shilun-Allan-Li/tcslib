<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSlots_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct designated tape indices

**Claim.** When $c>0$, the four designated tape indices in the host tape set are pairwise distinct.

**Proof.** Assume two of the four indices are equal and compare their natural-number values. The four cases correspond to the two source-bank positions, the final host position, and the call-bank position for the first virtual bank tape. The source positions occupy distinct locations in the initial source block; the final position lies beyond both embedded blocks; and the call-bank position lies in the call block, where its first-tape coordinate is separated from the source block by that block's offset. The positivity of $c$ ensures the first virtual bank index exists and that these block boundaries are strictly ordered. Thus each possible equality of two different designated indices contradicts the resulting index inequalities, proving injectivity.
