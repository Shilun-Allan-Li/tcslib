<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.localAuxiliaryWitness_satisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction by the Local Auxiliary Witness

**Claim.** If the verifier accepts the local transcript formed from the input and proof, then the seed’s formula is satisfied by the encoded local query bits together with the auxiliary assignment selected by the local witness construction.

**Proof.** By the reduction’s completeness property, acceptance for these local query bits implies that there exists an auxiliary assignment for which the formula evaluates to $-1$. In the accepting branch of the witness construction, the selected assignment is precisely a witness supplied by completeness. Its defining witness property therefore gives the required evaluation.
