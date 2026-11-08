<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfSignPlusMass_add_minus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Masses Sum to One

**Claim.** If $f$ takes only the values $-1$ and $1$, then under any probability mass function on a finite set, the masses of the points where $f$ is $1$ and where it is $-1$ sum to $1$.

**Proof.** At each point, exactly one of the two sign conditions holds, so the two indicator functions sum to the constant function $1$. The expectation of their sum is the sum of their expectations (\texttt{FABL.pmfExpectation_add}); the expectation of the constant function $1$ is $1$ (\texttt{FABL.pmfExpectation_const}). These expectations are precisely the two sign masses.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`.
