<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Configuration from a Relocated Copier

**Claim.** Placing the copier’s source and record tapes into the row machine’s slots for field $i$ and the record tape, while supplying the other counter tapes and heads as specified, gives exactly the row configuration at field $i$ and copier control $q$.

**Proof.** Compare the two configurations component by component. Their state and input position agree by the definitions of the placement and the row configuration, and both have empty physical output. For a counter slot other than $i$, the placement uses the supplied tape contents and gives its head position zero, matching the row configuration. At slot $i$, the placement uses the copier’s source tape, which is the buffer tape for $w(i)$, and its source head is at zero. At the record slot, it uses the copier’s record tape and head, which hold the buffer tape for the current record and have head position $|record|$. These are precisely the row machine’s tape contents and heads, so the configurations are equal.
