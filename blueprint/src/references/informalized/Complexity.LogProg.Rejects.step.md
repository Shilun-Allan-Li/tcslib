<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.Rejects.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step extension of rejection

**Claim.** If $c_0$ has the specified reference form, the program has no oracle call at its state, one step from $c_0$ yields $c_1$, and the computation from $c_1$ rejects relative to $c,r,p$, then the computation from $c_0$ rejects relative to $c,r,p$.

**Proof.** Let $T$ witness rejection from $c_1$. The run from $c_0$ for $1+T$ steps has the same halting state, rejecting output, and register-head positions as that run: apply the run-composition identity (\texttt{rrun_add}) and the given one-step endpoint. For intermediate times, time $0$ has the required reference form by hypothesis, and its state has no oracle call. Every other intermediate time is $1+t'$ for some $t'<T$; composing the runs reduces its required reference-form and no-call conditions to those supplied by the rejection witness from $c_1$.

**Key facts.** `Complexity.LogProg.rrun_add`.
