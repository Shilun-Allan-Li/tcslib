<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.ComputesInSpace.computesFunInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space Gives a Time Bound

**Claim.** If the machine computes every output using at most $c(\lfloor\log_2 |x|\rfloor+1)$ work-tape cells, then it computes the function within the stated polynomial time bound.

**Proof.** Fix an input $x$. By the space-bounded computation hypothesis, there is a time $t$ at which the machine outputs $f(x)$ and uses at most $c(\lfloor\log_2 |x|\rfloor+1)$ cells. The configuration-count bound converts this computation into one within $\mathrm{configBound}(|x|,c(\lfloor\log_2 |x|\rfloor+1))$ steps (`ComputesInTime.of_spaceUsed_le`). The logarithmic-space estimate bounds this quantity by the polynomial displayed in the claim (`configBound_logSpace_le`). Monotonicity of computation with respect to the time bound then gives computation within that polynomial bound (`ComputesInTime.mono`). As $x$ was arbitrary, this holds for every input.

**Key facts.** `Turing.FinTM.ComputesInTime.of_spaceUsed_le`, `Turing.FinTM.configBound_logSpace_le`, `Turing.FinTM.ComputesInTime.mono`.
