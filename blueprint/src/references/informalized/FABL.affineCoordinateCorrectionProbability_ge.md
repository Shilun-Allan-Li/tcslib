<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineCoordinateCorrectionProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Correction Success Bound

**Claim.** If a sign-valued function $f$ is within relative Hamming distance $\delta$ of the character encoded by $w_0$, then for every coordinate $i$, the probability that its local correction in direction $i$ equals the sign encoded by $w_0(i)$ is at least $1-2\delta$.

**Proof.** Identify the character encoded by $w_0$ with the binary parity character on the support of its frequency vector (FABL.f₂SignCharacter_eq_binaryParitySign). The local-correction success bound for a function within distance $\delta$ of a parity character then gives probability at least $1-2\delta$ of returning that parity character's value in direction $e_i$ (FABL.localCorrection_successProbability). This value is the encoding of the frequency's $i$th coordinate: the character evaluated at a standard basis vector reads precisely that coordinate (FABL.f₂SignCharacter_standardBasis), and the cube equivalence sends $w_0(i)$ to its corresponding binary-field value (FABL.pcppBoolCubeEquiv_apply). Rewriting that encoded value as the sign associated to the Boolean value (FABL.pcppBoolSignEquiv_eq_signEncode) gives the claimed probability.

**Key facts.** `FABL.localCorrection_successProbability`, `FABL.f₂SignCharacter_eq_binaryParitySign`, `FABL.f₂SignCharacter_standardBasis`, `FABL.pcppBoolCubeEquiv_apply`, `FABL.pcppBoolSignEquiv_eq_signEncode`.

**Caveat.** The supplied informal statement describes a different theorem; this account follows the formal statement and proof source.
