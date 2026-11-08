<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.compositionLocalAssignment_composeThreeQueryProof -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Local Assignment Identity

**Claim.** For every input word, original proof word, and verifier seed, evaluating the composed input-and-proof word at the reduction's local addresses gives the extension of the encoded outer local bits by the reduction's local auxiliary witness.

**Proof.** It suffices to compare the two assignments at each coordinate. Use the decomposition of a coordinate of the local assignment into either an outer query position or an auxiliary position. In the outer-query case, the address is the lifted version of an original input-or-proof address. The identity for evaluating the composed word at lifted outer addresses (`inputProofWord_composeThreeQueryProof_liftOuterAddress`) says this value is exactly the original outer local bit; encoding both sides as signs gives the required equality. In the auxiliary case, the address points to the auxiliary block of the composed proof. By the definition of that proof, this bit is the sign encoding of the local auxiliary witness for the given seed. The extension of the outer assignment by that witness has precisely this value at the auxiliary coordinate. Thus the assignments agree at every coordinate.

**Key facts.** `FABL.inputProofWord_composeThreeQueryProof_liftOuterAddress`.
