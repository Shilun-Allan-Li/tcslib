<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satVerdict_false_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-time plain verifier verdict

**Claim.** The function sending each Boolean word $z$ to the one-bit word containing the plain-mode verifier verdict on $z$ is polynomial-time computable.

**Proof.** The proof first builds a polynomial-time conditional computation from three components: the polynomial-time split-validity test, the polynomial-time safe-value computation, and the constant output $[\mathrm{false}]$ (`Complexity.sat_pipeline_poly`, `Complexity.satSafeValue_poly`, `Complexity.polyTimeComputable_const`, and `Complexity.polyTimeComputable_ite`). It then identifies this conditional computation with the plain verifier verdict. If the split search fails, both return false. If it succeeds at $i$, the encoded input is decoded into a prefix and a witness; when parsing the prefix succeeds, the split-validity and safe-value conditions reduce to the decoded formula's evaluation on that witness. When parsing fails, decoding uses the fallback formula, and the syntax-validity condition ensures the safe branch does not accept it. The parsing characterization (`Std.Sat.CNF.syntaxOK_spec`) and the fact that decoding a successful parse returns that formula (`Turing.pairDecode_pairEncode` together with the pipeline definitions) justify these identifications. Thus the conditional computation has exactly the plain verdict as output, proving polynomial-time computability.

**Key facts.** `Complexity.sat_pipeline_poly`, `Complexity.satSafeValue_poly`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Std.Sat.CNF.syntaxOK_spec`, `Turing.pairDecode_pairEncode`.

**Caveat.** The supplied upstream statements do not include the detailed definitions of the pipeline components, so the branch-by-branch identification with the plain verdict can only be summarized from the proof's unfolding and simplification.
