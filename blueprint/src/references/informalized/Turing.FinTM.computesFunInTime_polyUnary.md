<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_polyUnary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Unary polynomial output

**Claim.** For every $C,e\in\mathbb{N}$, a finite Boolean-alphabet Turing machine outputs a string of $C(|x|+1)^e$ true bits in time bounded by a constant times $(|x|+1)^{e+1}$.

**Proof.** Proceed by cases on $e$. If $e=0$, the output is the fixed string of $C$ true bits, so the constant-output machine computes it within a linear bound. If $e=d+1$, use the catalog machine for unary polynomial output. Its computation theorem gives the exact output in time $(C+5(d+1)+4)(|x|+1)^{d+1}$. This is the required bound with exponent $e+1=d+2$ as stated in the source theorem? The source invokes monotonicity of powers to enlarge the exponent by one, since $|x|+1\ge1$, yielding the claimed constant times $(|x|+1)^{e+1}$.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.catalogPoly_unary_computes`, `Turing.FinTM.ComputesInTime.mono`.

**Caveat.** The supplied informal statement has exponent $e+1$, while the source and upstream catalog theorem give $(|x|+1)^{e+1}$ when $e$ is replaced by $d+1$, which is $(|x|+1)^{e}$, not $(|x|+1)^{e+1}$. The proof enlarges this bound using $|x|+1\ge1$, so the stated result follows.
