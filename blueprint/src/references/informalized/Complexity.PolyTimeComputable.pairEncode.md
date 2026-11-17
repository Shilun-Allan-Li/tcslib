<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.PolyTimeComputable.pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-time pair encoding

**Claim.** If $f$ and $g$ are polynomial-time computable, then so is the function sending $x$ to the pair encoding of $f(x)$ and $g(x)$, where the first component is duplicated bit by bit, followed by the separator $01$ and then the second component.

**Proof.** The proof builds the target encoding through several polynomial-time pairing stages. The linear-time machines for duplicating a string and extracting either component of a decoded pair, together with the linear-time pair-concatenation machine, yield polynomial-time functions (`Complexity.polyTimeComputable_of_linear`, using `Turing.FinTM.computesFunInTime_pairDup`, `Turing.FinTM.computesFunInTime_pairFst`, `Turing.FinTM.computesFunInTime_pairSnd`, and `Turing.FinTM.computesFunInTime_pairConcat`). Repeatedly composing these functions with $f$ and $g$, and applying the polynomial-time operation that changes only the second component of a pair, constructs nested encodings from which the concatenation-and-projection stages assemble the desired pair encoding. Closure under composition (`Complexity.PolyTimeComputable.comp`) ensures every stage remains polynomial-time. The decoding identities for a valid encoding (`Turing.pairDecode_pairEncode`) and the identity describing how a second-component map acts on an encoding (`Complexity.pairMapSnd_pairEncode`) verify that the assembled output is exactly the pair encoding of $f(x)$ and $g(x)$; the reassociation used in the final concatenation is `Complexity.pairEncode_append`.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairMapSnd`, `Complexity.pairEncode_append`, `Complexity.pairMapSnd_pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairConcat`, `Turing.FinTM.computesFunInTime_pairDup`, `Turing.FinTM.computesFunInTime_pairFst`, `Turing.FinTM.computesFunInTime_pairSnd`, `Turing.pairDecode_pairEncode`.

**Caveat.** The proof uses a multi-stage nested-encoding construction; the supplied upstream statements do not give the full definitions of the component maps or the intermediate functions, so the exact intermediate decoding and assembly identities cannot be spelled out from this payload alone.
