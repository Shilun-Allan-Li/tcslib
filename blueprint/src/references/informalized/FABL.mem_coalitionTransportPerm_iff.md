<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mem_coalitionTransportPerm_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coalition Transport Membership

**Claim.** For equal-cardinality subsets A and B and any index i, the image of i under the coalition transport permutation belongs to B exactly when i belongs to A.

**Proof.** If i belongs to A, the extended permutation agrees with the chosen equivalence between the subtypes defined by A and B. Its image therefore belongs to B. If i does not belong to A, the extension maps i outside B, so its image cannot belong to B. These two cases establish both directions.
