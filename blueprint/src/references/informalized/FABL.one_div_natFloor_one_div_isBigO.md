<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.one_div_natFloor_one_div_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Floor Asymptotic Bound

**Claim.** As $\delta$ tends to zero through nonnegative values, $1/\lfloor1/\delta\rfloor$ is $O(\delta)$ on a right neighborhood of zero.

**Proof.** Use the right neighborhood $0\le\delta\le1/2$ and the constant $2$ in the definition of the big-$O$ bound. At $\delta=0$, the numerator expression is zero by the convention for the natural floor of the extended reciprocal, so the bound holds. For $0<\delta\le1/2$, the reciprocal-floor estimate gives $1/\lfloor1/\delta\rfloor\le2\delta$ (`FABL.reciprocal_natFloor_one_div_bounds`). Both sides are nonnegative there, so this is also the required bound on their absolute values. Thus the big-$O$ estimate holds throughout that right neighborhood.

**Key facts.** `FABL.reciprocal_natFloor_one_div_bounds`.
