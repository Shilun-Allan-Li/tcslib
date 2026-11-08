<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderShiftOr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under Shifted Disjunction

**Claim.** If the verifier associated to a Boolean predicate is efficient in the model, then testing that predicate on the exclusive-or of a witness string with one of polynomially many blocks of a second string gives an efficient two-witness predicate.

**Proof.** Take polynomial-time languages $V_1,V_0$ witnessing efficiency of the verifier, and retain the accepting-language witness $V_1$. The language $V_1$ is in $	extsf P$. The block-XOR closure theorem says that the language of encoded pairs for which some allowed block makes the verifier's accepting condition hold is also in $	extsf P$ (`Complexity.mem_P_of_blockXorAny`). Use this language as the two-witness predicate's accepting language. On an encoded triple, the two decoding identities for `pairEncode` recover exactly the original strings: the first two components are $x,u$, and the final component is $v$ (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). Thus membership in the chosen language says that there is an index below $a'(|x|+1)^{k'}$ for which the encoded pair formed from $x$ and the exclusive-or of $v$ with the indicated block of $u$ belongs to $V_1$. By the verifier's defining equivalence, this is exactly the condition that one of the corresponding evaluations of $M$ is true. Hence the two-witness predicate is efficient.

**Key facts.** `Complexity.mem_P_of_blockXorAny`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
