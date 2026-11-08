<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReqFragment_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tail-Link Fragment

**Claim.** There exist a finite Turing machine $M$ over the Boolean alphabet and natural numbers $C,c$ such that, for every Boolean word $z$, $M$ halts after exactly $C(|z|+1)^c$ steps with output equal to the tail-link fragment formed from $z$.

**Proof.** The fragment is assembled from the fresh field, the literal field, and fixed Boolean words. The fresh and literal fields are polynomial-time computable by the request-field result (`Complexity.satReq_fields_poly`). Prepending a fixed true bit to the fresh field remains polynomial-time computable, by composing the linear-time prepend operation with the fresh-field computation (`Complexity.sat_pt_linear`, `Turing.FinTM.computesFunInTime_prepend`, `Complexity.PolyTimeComputable.comp`). The two fixed separators and the fixed middle word are polynomial-time computable as constant functions (`Complexity.sat_pt_const`). Repeatedly concatenating these pieces preserves polynomial-time computability (`Complexity.sat_pt_append`), giving precisely the tail-link fragment.

**Key facts.** `Complexity.satReq_fields_poly`, `Complexity.sat_pt_linear`, `Turing.FinTM.computesFunInTime_prepend`, `Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_const`, `Complexity.sat_pt_append`.
