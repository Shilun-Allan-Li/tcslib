<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockValue_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of parity block values

**Claim.** For the specified block assignment, every entry whose input index is at least $n$ equals $1$.

**Proof.** Fix an entry $j$ and suppose $n\le gr+j$. Then its index is not less than $n$, so the definition of the block assignment takes the padding branch, whose value is $1$.
