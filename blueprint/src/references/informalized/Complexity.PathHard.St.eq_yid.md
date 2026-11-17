<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.eq_yid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a state from three coordinates

**Claim.** If a vector agrees with a state record’s coordinate vector except possibly at the query-length, index, and decoding-and-comparison-scratch coordinates, then it is the coordinate vector of the record obtained by replacing those three coordinates with the vector’s entries there.

**Proof.** Compare entries at each coordinate. At the query-length, index, and scratch coordinates, the updated record uses exactly the entries of the given vector, so the entries agree. At each of the other twelve coordinates, the hypothesis says that the given vector agrees with the original coordinate vector. The coordinate evaluation facts (`toV_p`, `toV_x`, `toV_t`, `toV_c`, `toV_s`, `toV_e`, `toV_n`, `toV_m`, `toV_k`, `toV_q`, `toV_u`, and `toV_z`) identify these entries with unchanged coordinates of the updated record. Thus the vectors agree at every index and are equal.

**Key facts.** `Complexity.PathHard.St.toV_p`, `Complexity.PathHard.St.toV_x`, `Complexity.PathHard.St.toV_t`, `Complexity.PathHard.St.toV_c`, `Complexity.PathHard.St.toV_s`, `Complexity.PathHard.St.toV_e`, `Complexity.PathHard.St.toV_n`, `Complexity.PathHard.St.toV_m`, `Complexity.PathHard.St.toV_k`, `Complexity.PathHard.St.toV_q`, `Complexity.PathHard.St.toV_u`, `Complexity.PathHard.St.toV_z`.
