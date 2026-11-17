<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.one_add_average_logb_two_le_logb_two_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic inequality for a sum

**Claim.** If $a$ and $b$ are positive natural numbers, then $1+\frac{\log_2 a+\log_2 b}{2}\le\log_2(a+b)$.

**Proof.** Regard $a,b$ as positive real numbers. The arithmetic-geometric mean inequality gives $ab\le ((a+b)/2)^2$. By monotonicity of the natural logarithm, and the product, power, and quotient rules for logarithms, this yields $\log a+\log b\le 2(\log(a+b)-\log 2)$. Divide by the positive number $2\log 2$ and rearrange. Using $\log_2 x=\log x/\log 2$ gives the stated inequality.
