<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.inputProofWord_composeThreeQueryProof_liftOuterAddress -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer word under address lifting

**Claim.** Evaluating the word formed from the input word and composed proof at a lifted address agrees with evaluating the original input and proof words at that address.

**Proof.** Split into the two types of address. For an input address, lifting leaves the address unchanged, and both evaluations return the corresponding entry of the input word. For a proof address $j$, lifting sends it to the proof position obtained by appending the auxiliary positions after the original proof positions. The composed proof at this position is exactly the original proof's value at $j$, by the preservation of old proof positions under composition (\texttt{FABL.composeThreeQueryProof_castAdd}). Thus the evaluations agree in either case.

**Key facts.** `FABL.composeThreeQueryProof_castAdd`.
