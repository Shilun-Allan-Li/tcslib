<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReqStep_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Next-State Program

**Claim.** The word-level next-state function that maps a Boolean word to its next encoded seam word is polynomial-time computable.

**Proof.** The next-state program first computes the fresh, consumed, phase, remainder, polarity, and literal fields; each is polynomial-time computable (`Complexity.satReq_fields_poly`). It also forms the consumed field with an extra true bit, the fresh field with an extra true bit, and the consumed field extended by a unary encoding of the literal length. These are polynomial-time constructions using concatenation and unary-length computation (`Complexity.sat_pt_append`, `Complexity.sat_pt_unaryLength`). The program then follows its nested cases: it tests whether the phase is $1^4$, whether the remainder begins with no bit or with false, whether the phase is empty or $[\mathrm{true}]$, whether the polarity is empty, and whether the link decision holds. Such fixed-word tests are polynomial-time computable (`Complexity.sat_pt_eq`), and the link test is polynomial-time computable (`Complexity.satReqLink_poly`). In each branch, the output is either the first decoded field or a packed pair built from the computed fresh and consumed fields and a fixed phase; these outputs are polynomial-time computable (`Complexity.sat_pt_fields`, `Complexity.sat_pt_pack`). The polynomial-time conditional construction combines the branches in the same order as the definition (`Complexity.sat_pt_cond`), proving the result.

**Key facts.** `Complexity.satReq_fields_poly`, `Complexity.sat_pt_append`, `Complexity.sat_pt_unaryLength`, `Complexity.satReqLink_poly`, `Complexity.sat_pt_eq`, `Complexity.sat_pt_fields`, `Complexity.sat_pt_pack`, `Complexity.sat_pt_cond`.
