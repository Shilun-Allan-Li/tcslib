<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.avoid_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoiding Halt-Forcing States

**Claim.** If the machine's output after $T$ steps is the initial output followed by $b\ne\beta$, then at every time $t<T$ its state cannot satisfy $X$.

**Proof.** Fix $t<T$ and suppose the machine is in a state $q$ satisfying $X$. By hypothesis, the next step halts and appends $\beta$. Thus the run is halted at time $t+1$; all later steps leave that halted configuration unchanged. The run at time $T$ is consequently the run at time $t+1$ (`runFrom_succ_eq_step'`, `runFrom_add`, and `runFrom_of_halt`). The output at time $t$ extends the initial output by some list $u$ (`runFrom_output_extends`), so the final output is the initial output followed by $u$ and then $\beta$. Comparing this with the assumed final output, cancellation of the common initial output gives $u++[\beta]=[b]$. Hence $u$ must be empty and $b=\beta$, contradicting $b\ne\beta$.

**Key facts.** `Complexity.LogProg.runFrom_output_extends`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
