<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltRun_eq_some_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting output characterization

**Claim.** The halting-run result on input $x$ under choices $w$ equals $o$ exactly when the resulting configuration is halted and its output is $o$.

**Proof.** Unfold the definition of the halting-run result and split according to whether the resulting state is `none`. If it is `none`, the result is the singleton option containing the output, so equality with `some o` is equivalent to the output being $o$. If the state is not `none`, the result is `none`, which cannot equal `some o$; likewise, the conjunction on the right is impossible.
