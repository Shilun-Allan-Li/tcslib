<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_repeat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated macrosteps over a unary segment

**Claim.** For each $j\le B$, after $j(6R+8)$ steps from macrostep-check with unary head at $1$ and guide head at $0$, the machine is in macrostep-check with unary head at $j+1$ and guide head at $0$.

**Proof.** Induct on $j$. The case $j=0$ is the initial configuration. For the successor case, the induction hypothesis gives the macrostep-check configuration at unary coordinate $j+1$. Since $j+1\le B$, the unary hypothesis supplies a unit marker there. The exact-cycle result (`macroCfg_cycle`) then advances the machine by $6R+8$ steps to macrostep-check at unary coordinate $j+2$, with the guide head still at $0$. The runs concatenate using the addition rule for iteration (`runFrom_add`), and the step-count identity $(j+1)(6R+8)=j(6R+8)+(6R+8)$ completes the induction.

**Key facts.** `Complexity.macroCfg_cycle`, `Turing.MultiTapeTM.runFrom_add`.
