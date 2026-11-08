<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_output_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Length Bound

**Claim.** After $t$ steps of a multi-tape Turing machine, the output length is at most its initial length plus $t$.

**Proof.** First, a single step increases the output length by at most one: the output after the step is the previous output followed by either no symbol or one symbol. Now induct on $t$. At zero steps the output is unchanged, giving the bound. For the successor case, the run for $t+1$ steps is one step applied to the run for $t$ steps ($\mathrm{runFrom\_succ\_eq\_step'}$). The one-step bound and the induction hypothesis give an output length at most $(|c.\mathrm{output}|+t)+1=|c.\mathrm{output}|+(t+1)$.

**Key facts.** `Turing.MultiTapeTM.step_output`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
