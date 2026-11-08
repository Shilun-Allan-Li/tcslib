<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.splitCharacterFunctionTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect completeness

**Claim.** Every function that is a split character is accepted by the split character tester with probability one.

**Proof.** Write the function as the split character indexed by some $\gamma$, as guaranteed by the definition of the property. For any seed $(x,y,h)$, the inverse coordinate map sends the three queried points back to $(h,x)$, $(0,y)$, and $(0,x+y)$. The character depends only on the second coordinate, so its values at these points are respectively the signs encoded by $\langle\gamma,x\rangle$, $\langle\gamma,y\rangle$, and $\langle\gamma,x+y\rangle$. Bilinearity gives $\langle\gamma,x+y\rangle=\langle\gamma,x\rangle+\langle\gamma,y\rangle$, and sign encoding turns addition into multiplication (`signEncode_add`). Consequently the product of the first two queried values equals the third for every seed, so the tester's acceptance indicator is constantly one. The expectation of this constant is one (`pmfExpectation_const_one`). The transcript expansion simply identifies the answers with the three queries (`NonadaptiveFunctionTester.transcript_apply`).

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.signEncode_add`, `FABL.pmfExpectation_const_one`.
