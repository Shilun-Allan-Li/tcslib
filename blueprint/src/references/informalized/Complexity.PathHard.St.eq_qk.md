<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.eq_qk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a state from two coordinates

**Claim.** If a vector agrees with a state record’s coordinate vector except possibly at the width-cap and width-check-pointer coordinates, then it is the coordinate vector of the record obtained by replacing those two coordinates with the vector’s entries there.

**Proof.** Compare the two vectors coordinate by coordinate. At the width-cap and width-check-pointer indices, the updated record has precisely the entries of the given vector, so equality holds there by definition. At every other index, the hypothesis identifies the given vector’s entry with the original coordinate vector’s entry. The coordinate evaluation facts for `toV` (`toV_p`, `toV_x`, `toV_t`, `toV_c`, `toV_s`, `toV_e`, `toV_n`, `toV_m`, `toV_i`, `toV_d`, `toV_u`, `toV_z`, and `toV_y`) identify those entries with the corresponding unchanged record coordinates. Thus the two vectors agree at every index, hence are equal.

**Key facts.** `Complexity.PathHard.St.toV_p`, `Complexity.PathHard.St.toV_x`, `Complexity.PathHard.St.toV_t`, `Complexity.PathHard.St.toV_c`, `Complexity.PathHard.St.toV_s`, `Complexity.PathHard.St.toV_e`, `Complexity.PathHard.St.toV_n`, `Complexity.PathHard.St.toV_m`, `Complexity.PathHard.St.toV_i`, `Complexity.PathHard.St.toV_d`, `Complexity.PathHard.St.toV_u`, `Complexity.PathHard.St.toV_z`, `Complexity.PathHard.St.toV_y`.
