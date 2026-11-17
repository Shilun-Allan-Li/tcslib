<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinQueryProgram_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Work Bound

**Claim.** For every outcome in the support of the Goldreich–Levin query program, the charged work is at most the stated work budget.

**Proof.** Apply the run-up work bound at the full number $n$ of stages: every supported outcome has work at most $n$ times the sum of the per-stage controller work and the bound for estimating the candidates at that stage (\texttt{goldreichLevinQueryRunUpTo\_work\_le}). The definition of the full program identifies it with this run-up at $n$, and the definition of the work budget is exactly the resulting expression. Substituting these definitions gives the claimed inequality.

**Key facts.** `FABL.goldreichLevinQueryRunUpTo_work_le`.
