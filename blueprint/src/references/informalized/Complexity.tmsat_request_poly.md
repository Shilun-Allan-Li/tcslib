<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_request_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Request Assembly

**Claim.** The map sending a bit string to its timed request is polynomial-time computable.

**Proof.** The field-extraction lemma `tmsat_fields_poly` supplies polynomial-time procedures for the code, input, width, clock, padded certificate, and validity flag. The clock's binary representation is also polynomial-time computable: first form the pair of the identity input with the clock field, project its second component, then apply the linear-time procedure for producing the binary representation of a list's length. The pair-decoding identity for encoded pairs confirms that this composition returns exactly the binary representation of the clock-field length. Next, `tmsat_pt_take` shows that truncating the padded certificate to the width-field length is polynomial-time computable. Pairing these component procedures, using closure of polynomial-time computability under pair encoding, produces the specified request on valid inputs. Finally, polynomial-time computability is preserved by a conditional whose Boolean test is polynomial-time computable (`polyTimeComputable_ite`); on invalid inputs the chosen output is the fixed encoding, which is constant-time computable.

**Key facts.** `Complexity.tmsat_fields_poly`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.pairMapSnd`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`, `Complexity.tmsat_pt_take`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`.
