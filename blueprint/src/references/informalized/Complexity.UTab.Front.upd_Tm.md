<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.upd_Tm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register Tm

**Claim.** Replacing the value at position $3$ of the five-position register function by $v$ gives the function with values $a,b,c,v,f$.

**Proof.** Evaluate both functions at each position. The updated position $3$ has value $v$; the update leaves positions $0,1,2,4$ unchanged, with values $a,b,c,f$. The resulting values match the claimed function at every position, proving equality.
