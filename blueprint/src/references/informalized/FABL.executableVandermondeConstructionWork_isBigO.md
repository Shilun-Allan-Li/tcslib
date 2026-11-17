<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeConstructionWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound on construction work

**Claim.** The executable Vandermonde construction work is asymptotically bounded by a constant multiple of $(\mathrm{scale}+1)^8$ over the specified input family.

**Proof.** The construction work is bounded pointwise by the input's polynomial budget (\texttt{FABL.executableVandermondeConstructionWork_le_polynomialBudget}). By definition, this budget is $2^{17}(\mathrm{scale}+1)^8$. Thus the norm of the real-valued work is at most the constant $2^{17}$ times $(\mathrm{scale}+1)^8$ for every input. A uniform pointwise bound of this form supplies the required big-$O$ bound.

**Key facts.** `FABL.executableVandermondeConstructionWork_le_polynomialBudget`.
