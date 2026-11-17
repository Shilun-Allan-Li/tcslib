<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReqLink_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Link Decision

**Claim.** There exist a finite Turing machine $M$ over the Boolean alphabet and natural numbers $C,c$ such that, for every Boolean word $z$, $M$ halts after exactly $C(|z|+1)^c$ steps with output the one-bit word whose bit is the tail-link decision for $z$.

**Proof.** The link decision is the conjunction of two tests: whether the phase field is the fixed word $1^3$, and whether the second bit of the polarity field is true. Both fields are polynomial-time computable (`Complexity.satReq_fields_poly`). Equality with a fixed word is polynomial-time decidable (`Complexity.sat_pt_eq`). For the second test, take the tail of the polarity field and then its first bit; these list operations preserve polynomial-time computability under composition (`Complexity.sat_pt_tail`, `Complexity.sat_pt_head`, `Complexity.PolyTimeComputable.comp`), after which equality with the one-bit word $[\mathrm{true}]$ is again polynomial-time decidable (`Complexity.sat_pt_eq`). Combining the two Boolean tests gives the one-bit conjunction output by `Complexity.sat_pt_and`.

**Key facts.** `Complexity.satReq_fields_poly`, `Complexity.sat_pt_eq`, `Complexity.sat_pt_tail`, `Complexity.sat_pt_head`, `Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_and`.
