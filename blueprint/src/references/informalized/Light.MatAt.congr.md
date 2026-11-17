<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.MatAt.congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on a Matrix Interval

**Claim.** If μ encodes the entries of A at the specified matrix indices and μ' agrees with μ throughout the interval from a to a+nk, then μ' encodes the same matrix entries there.

**Proof.** Fix i<n and j<k. The bound for a row-major index gives ik+j<nk (`Nat.mul_add_lt_mul`). Consequently a≤a+ik+j<a+nk, so the assumed interval agreement applies at this index. It identifies μ' there with μ, and the matrix-encoding hypothesis identifies μ with A at the corresponding entry. Hence μ' has the required value for every i and j.

**Key facts.** `Nat.mul_add_lt_mul`.
