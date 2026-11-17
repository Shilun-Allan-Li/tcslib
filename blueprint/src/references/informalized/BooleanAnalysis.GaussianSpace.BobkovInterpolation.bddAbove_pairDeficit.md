<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.bddAbove_pairDeficit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Interpolation Deficits

**Claim.** Under the stated continuity and endpoint assumptions, the interpolation deficits are bounded above on $[0,1]\times[0,\infty)$.

**Proof.** First consider the function $t\mapsto L(t,0)$. It is continuous on the compact interval $[0,1]$, so its image is bounded above by some real number $M$ (continuity of the zero-clock pair length, `continuousOn_pairLength_zero`). For any admissible $t,c$, the shift $b^2(1-t^2)$ is nonnegative, so $c\le c+b^2(1-t^2)$. Monotonicity of the square root, followed by the lower bound of the pair length by the square root of its clock, gives $\sqrt c\le L(1,c+b^2(1-t^2))$. On the other hand, the pair length at clock $c$ is at most $\sqrt c+L(t,0)$ (`pairLength_clock_le`). Subtracting these inequalities shows that the deficit $L(t,c)-L(1,c+b^2(1-t^2))$ is at most $L(t,0)$, hence at most $M$.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.continuousOn_pairLength_zero`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_clock_le`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.sqrt_clock_le_pairLength`.
