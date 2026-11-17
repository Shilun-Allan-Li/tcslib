<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearProof_checks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Checks for the Constructed Proof

**Claim.** For an input whose complete quadratic value is one, the constructed proof table satisfies every endpoint and transition check.

**Proof.** Split according to the seed, which selects either an endpoint check or one of the transition checks. For the linear-prefix endpoint at zero, the constructed value is the encoding of the empty prefix sum, hence false. For the quadratic-prefix endpoint at zero, the truncated input is zero, so its complete quadratic value is zero and the constructed value is false. At the terminal endpoint, the full truncation is the encoded input itself: the full-prefix identity (`completeQuadraticPrefixBit_full`) reduces the table value to the complete quadratic value of the input, which is one by hypothesis; the encoding of true is one (`pcppBoolF₂Equiv_true`). For a linear transition at coordinate $i$, the constructed next prefix is the current prefix plus the encoded input bit, by the prefix increment identity (`completeQuadraticLinearPrefixBit_succ`). For a product transition, the constructed product entry is the encoding of the product of the current prefix value and the encoded input bit; multiplication of Boolean encodings agrees with conjunction (`pcppBoolF₂Equiv_and`), so this is exactly the required Boolean conjunction. Finally, for a quadratic-prefix transition, the next quadratic prefix is the current quadratic prefix plus the product of the linear prefix and the encoded input bit, by the quadratic-prefix increment identity (`completeQuadraticPrefixBit_succ`). Thus each possible seed checks successfully.

**Key facts.** `FABL.completeQuadraticLinearPrefixBit_succ`, `FABL.completeQuadraticPrefixBit_full`, `FABL.pcppBoolF₂Equiv_true`, `FABL.pcppBoolF₂Equiv_and`, `FABL.completeQuadraticPrefixBit_succ`.
