<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Diagonalization.lean :: Complexity.UC_not_computable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uncomputability of the Diagonal Function

**Claim.** For every machine representation scheme, the function that returns the diagonal value as a one-bit string is not computable.

**Proof.** Assume for contradiction that a machine $M$ computes the diagonal function. Convert it, with at most a quadratic time-bound change, to an equivalent machine $M'$ with one work tape (`one_work_tape_binary`), and encode $M'$ by a code-machine object $N$ whose computations agree with those of $M'$ (`exists_codeTM`). Set $\alpha$ to be the representation of $N$. The encoding-decoding identity (`MachineCode.decode_encode`) says that the machine decoded from $\alpha$ is exactly $N$. Thus, on input $\alpha$, it halts with output the one-bit diagonal value at $\alpha$.

If that value is false, `UC_eq_false_iff` says the decoded machine also halts on the same input with output $[\mathrm{true}]$. These two outputs must agree by uniqueness of output for halting computations (`ComputesInTime.output_unique`), but the assumed output is $[\mathrm{false}]$, a contradiction. If the value is true, the run just obtained has output $[\mathrm{true}]$, so `UC_eq_false_iff` forces the diagonal value to be false, again a contradiction. Therefore no machine computes the diagonal function.

**Key facts.** `Turing.FinTM.Computes.exists_computesFunInTime`, `Turing.FinTM.one_work_tape_binary`, `Turing.exists_codeTM`, `Turing.MachineCode.decode_encode`, `Complexity.UC_eq_false_iff`, `Turing.FinTM.ComputesInTime.output_unique`.
