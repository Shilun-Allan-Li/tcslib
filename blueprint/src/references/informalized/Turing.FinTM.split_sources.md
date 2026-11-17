<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.split_sources -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Split-Source Construction

**Claim.** For every $C,e$, there is a source machine and start state whose unary output has length $C(|s|+1)^e$, whose running time obeys the stated bound, and whose associated split-solver machine is the prescribed loop controller.

**Proof.** Split on whether $e$ is zero. If $e=0$, choose the machine that emits the fixed word of $C$ ones, with its initial state as the source state and running time $B(l)=C+1$. The constant-output result (`splitSource_constant`) gives the exact output and unchanged tapes for every bank word. The bound follows directly from the stated coefficient when $e=0$. The definition of the solver gives the required loop-controller identity.

If $e$ is positive, write it as $r+1$ and choose the polynomial unary generator with level $r$, started at its loop state, with $B(l)=\operatorname{catalogPolyCost}(l+1,C,r+1)+1$. Its exact output and halting behavior follow from `splitSource_poly`. The cost estimate (`catalogPolyCost_le`), applied with $q=l+1$ and exponent $r+1=e$, gives $B(l)\le (C+1+5e)(l+1)^e+1$. Again, the definition of the solver gives the required controller identity.

**Key facts.** `Turing.FinTM.splitSource_constant`, `Turing.FinTM.splitSource_poly`, `Turing.FinTM.catalogPolyCost_le`.
