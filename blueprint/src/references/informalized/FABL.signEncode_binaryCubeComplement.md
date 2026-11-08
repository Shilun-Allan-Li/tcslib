<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.signEncode_binaryCubeComplement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign encoding under complementation

**Claim.** Complementing coordinate $i$ of a binary vector makes its sign encoding at that coordinate the negative of the original sign encoding.

**Proof.** Coordinate complementation adds $1$ in the two-element field at coordinate $i$. The sign encoding converts addition in that field into multiplication of signs (`signEncode_add`), so the new encoding is the old encoding multiplied by the encoding of $1$. The latter is $-1$, giving the negative of the original sign.

**Key facts.** `FABL.signEncode_add`.
