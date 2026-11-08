<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.realSignEncodedFunction_affineFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of an Affine Boolean Function

**Claim.** The real sign encoding of $x\mapsto b+a\cdot x$ equals $x\mapsto (-1)^b\chi_a(x)$.

**Proof.** Evaluate both functions at an arbitrary $x$. The affine sign function evaluation formula (`affineSignFunction_apply`) expresses the right-hand side as the real sign value of the encoding of $b$, multiplied by the Walsh character at $a,x$. The character evaluation formula (`vectorWalshCharacter_apply`) identifies that character with the binary sign of $a\cdot x$. By `signEncode_add`, encoding $b+a\cdot x$ is the product of the encodings of $b$ and $a\cdot x$. Real sign values turn that product into the product of their real sign values, and the sign-value identity (`signValue_signEncode_eq_binarySign`) identifies the second value with the binary sign just obtained. The two evaluations agree for every $x$.

**Key facts.** `FABL.affineSignFunction_apply`, `FABL.vectorWalshCharacter_apply`, `FABL.signEncode_add`, `FABL.signValue_signEncode_eq_binarySign`.
