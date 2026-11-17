<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Halting.lean :: Complexity.UC_computable_of_HALT_computable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting-to-Diagonal Computability Reduction

**Claim.** If the halting predicate for a machine coding scheme is computable, then its diagonal function is computable.

**Proof.** Let $D$ compute the halting predicate, and let $U$ be the universal machine for the coding scheme. A machine can first form the self-pair of its input and run $D$ on that pair; write $p(\alpha)$ for the resulting bit, which says whether the machine decoded from $\alpha$ halts on input $\alpha$ with some output. The composition and partial-composition results provide machines realizing these stages (`exists_comp_partial`), and the paired-input construction is computable (`computesFunInTime_pairEncode_diag`). Build a conditional machine that, when $p(\alpha)$ is false, returns true, and when it is true, runs $U$ on the self-pair and changes its output by the rule $r(w)=[\mathrm{false}]$ if $w=[\mathrm{true}]$, and $r(w)=[\mathrm{true}]$ otherwise. The conditional construction (`exists_cond`) gives a machine computing this function, with the fixed outputs and the test of whether an output equals $[\mathrm{true}]$ implemented by `computesFunInTime_const` and `computesFunInTime_ifEq`.

To verify its output, split according to $p(\alpha)$. If it is false, the decoded machine does not halt on its own code with output $[\mathrm{true}]$, so the diagonal value is true by `UC_eq_true_iff`; the constructed machine returns that bit. If $p(\alpha)$ is true, there are an output $w$ and a time at which the decoded machine halts on input $\alpha$ with output $w$, by `HALT_pairEncode_eq_true_iff`. The universal simulation theorem gives a halting run of $U$ on the self-pair with the same output. If $w=[\mathrm{true}]$, the diagonal value is false by `UC_eq_false_iff`, and the postprocessing returns false. If $w\ne[\mathrm{true}]$, output uniqueness for halting runs (`ComputesInTime.output_unique`) rules out any run with output $[\mathrm{true}]$; hence the diagonal value is true by `UC_eq_true_iff`, and the postprocessing returns true. Thus the conditional machine computes the diagonal function in both cases.

**Key facts.** `Turing.computesFunInTime_pairEncode_diag`, `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.exists_comp_partial`, `Turing.universal`, `Turing.FinTM.exists_cond`, `Complexity.HALT_pairEncode_eq_true_iff`, `Complexity.UC_eq_true_iff`, `Complexity.UC_eq_false_iff`, `Turing.FinTM.ComputesInTime.output_unique`.
