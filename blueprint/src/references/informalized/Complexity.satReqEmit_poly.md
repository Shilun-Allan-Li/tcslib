<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReqEmit_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Emission

**Claim.** There exist a finite Turing machine $M$ over the Boolean alphabet and natural numbers $C,c$ such that, for every Boolean word $z$, $M$ halts after exactly $C(|z|+1)^c$ steps with output equal to the word-level emission function applied to $z$.

**Proof.** The emission function is defined by nested cases on simple fields of the request word. The fields needed for those tests and the literal portion are polynomial-time computable (`Complexity.satReq_fields_poly`). The phase test compares its field with a fixed word; tests of whether the unread prefix is empty or begins with false use the first bit of the remainder; further cases test whether the phase or polarity is empty. Each such equality test is polynomial-time computable (`Complexity.sat_pt_eq`), and the initial-bit test is polynomial-time computable by composition with taking the first bit (`Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_head`). In the final branch, the link decision and fragment are polynomial-time computable (`Complexity.satReqLink_poly`, `Complexity.satReqFragment_poly`). Combining these branches with the polynomial-time conditional construction (`Complexity.sat_pt_cond`) and constant-output machines (`Complexity.sat_pt_const`) proves that the entire piecewise emission function is polynomial-time computable.

**Key facts.** `Complexity.satReq_fields_poly`, `Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_head`, `Complexity.sat_pt_eq`, `Complexity.satReqLink_poly`, `Complexity.satReqFragment_poly`, `Complexity.sat_pt_cond`, `Complexity.sat_pt_const`.
