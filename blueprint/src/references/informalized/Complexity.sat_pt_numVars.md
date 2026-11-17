<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Variable Count

**Claim.** The function sending each bit string $x$ to the unary string of length equal to the variable count of the decoded formula is polynomial-time computable.

**Proof.** First compute a canonical serialized form of the decoded formula in polynomial time (`Complexity.satStreamCanonical_poly`), using that this canonical form is exactly the serialization (`Complexity.satStreamCanonical_spec`). On that serialization, the maximum-finding machine outputs a unary word of length equal to the formula's variable count in at most four times the serialized length plus six steps (`Complexity.satMax_computes`). The serialization has length at most $|x|+1$, so this second computation fits a linear bound in the original input length. Compose the two machines on the image of the first computation (`Complexity.sat_comp_on_image`). Its combined time is bounded by $2C(|x|+1)^e+4(|x|+1)+8$; since $|x|+1\leq(|x|+1)^{e+1}$, this is at most $(2C+12)(|x|+1)^{e+1}$. Increasing the allotted time to that polynomial preserves the computed result (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Complexity.satStreamCanonical_poly`, `Complexity.satStreamCanonical_spec`, `Complexity.satMax_computes`, `Complexity.sat_comp_on_image`, `Turing.FinTM.ComputesInTime.mono`.
