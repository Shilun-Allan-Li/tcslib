<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.bdOK_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Validity at a Computation Time

**Claim.** Under the table-agreement and size hypotheses, the boundary-validity predicate evaluated on the numerical assignment at time $t$ is true for the configuration after $t$ steps on input $x$.

**Proof.** First, the table’s Boolean symbol answers at time $t$ and address $1$ represent the actual input read at each of the two nonzero directions: this follows from the table-agreement hypothesis via the answer-to-read identity ($\texttt{sv\_true\_none}$). Likewise, at time $t+1$ and address $|x|+1$, the table answer represents the input read at the corresponding signed offset. The bounds $t+1<2^W$ and $|x|+2<2^W$ ensure these table indices are in range.

Unfold the boundary predicate and use the numerical assignment to replace its encoded symbols by these reads. The run at time $t+1$ is one machine step from the configuration $c$ at time $t$ ($\texttt{runFrom\_succ\_eq\_step'}$), and the one-step input-read rule identifies each next read with the current configuration’s read rule ($\texttt{RI\_step}$). If $c$ is halting, the predicate is immediate. Otherwise split on the transition’s input-head movement. For a stationary move, the boundary condition holds directly. For a right move, either the current read is already blank at the relevant boundary, making the clamp condition true, or the next read at the far right offset is blank; the latter follows because that offset lies beyond the input word ($\texttt{RI\_far}$). The left-move case is the same argument with the negative offset. In each case the disjunction defining boundary validity is true.

**Key facts.** `Complexity.Meyer.sv_true_none`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.RI_step`, `Complexity.Meyer.RI_far`.
