<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pad_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation on a Padded Tape Bank

**Claim.** Under the stated transition compatibility condition, running the larger machine for $t$ steps from the padded configuration gives the padding of the configuration reached by running the smaller machine for $t$ steps.

**Proof.** Use the step-by-step commutation principle: if a map carries each source step to the corresponding target step, then it carries every finite run to the target run (`Turing.MultiTapeTM.runFrom_comm_of_step`). Here the map is padding. Check one step from an arbitrary source configuration. If its state is halting, both machines leave their configurations fixed, and padding preserves that configuration. If its state is $q$, the padded state is $\mathrm{emb}(q)$. The first $k$ scanned symbols are exactly those of the source configuration, and the input symbol is unchanged. The transition compatibility hypothesis therefore makes the larger machine’s action the padding of the source action. Applying this action commutes with padding by the action-application identity (`enumCont_pad_apply`). Thus the step condition holds, and the finite-run principle yields the result for every $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Complexity.enumCont_pad_apply`.
