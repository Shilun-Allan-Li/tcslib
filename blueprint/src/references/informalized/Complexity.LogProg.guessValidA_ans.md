<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean :: Complexity.LogProg.guessValidA_ans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance of the valid-input checker

**Claim.** For every Boolean input word and oracle with no query indices, the checker accepts in exactly three steps from its prescribed initial configuration if and only if the input is a unary-prefix pair with canonical payload.

**Proof.** The initial state makes a binary choice: the choice bit selects either the branch to validate the input or the branch that immediately returns false. The nondeterministic-answer decomposition (`nans_choose`) expresses acceptance at length three as acceptance along one of these branches with two steps remaining. The immediate-false branch cannot produce acceptance. On the validation branch, the deterministic-step decomposition (`nans_det`) reduces the question to the effect of the validity check. If the input is valid, that check advances to the final state, where the next deterministic step returns true; the halted-run characterization (`nans_halted`) then confirms acceptance. If the input is invalid, the check halts with false, and the same halted-run characterization rules out acceptance. Thus acceptance is equivalent to validity.

**Key facts.** `Complexity.LogProg.nans_choose`, `Complexity.LogProg.nans_det`, `Complexity.LogProg.nans_halted`.
