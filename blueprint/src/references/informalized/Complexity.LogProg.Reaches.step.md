<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.Reaches.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step extension of reaching

**Claim.** If $c_0$ has the specified reference form, the program has no oracle call at its state, one step from $c_0$ yields $c_1$, and $c_1$ reaches $c_2$ relative to $c,r,p$, then $c_0$ reaches $c_2$ relative to $c,r,p$.

**Proof.** Take a witnessing time $T$ for the run from $c_1$ to $c_2$. The run from $c_0$ reaches $c_2$ after $1+T$ steps: the run-composition identity (\texttt{rrun_add}), the assumed one-step endpoint, and the witness for $T$ give the endpoint equality. An intermediate time $t<1+T$ is either $0$ or at least $1$. At time $0$, the given equality identifies the configuration with the required reference form, and the state has no oracle call. In the latter case write $t=1+t'$; the run-composition identity and the one-step equality reduce the claim to the intermediate-time condition for the run from $c_1$, since $t'<T$.

**Key facts.** `Complexity.LogProg.rrun_add`.
