<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_loopCfgTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration-Level Loop Machine

**Claim.** Under the stated counter, invariant, startup, and round hypotheses, there is a finite machine whose configurations encode successive rounds, preserve empty output through the last prescribed round, halt with output $[\mathrm{false}]$ afterward, and implement each round’s acceptance or update behavior within a uniform bound.

**Proof.** Apply the loop-host contract theorem with the requested acceptance predicate and with the output chunk fixed to $[\mathrm{true}]$, in non-search mode. The hypotheses provide exactly the counter computation, invariant preservation, clean startup at the anchor, and bounded round behavior required by that contract. It produces a loop-host machine and a coefficient with the claimed sequence of configurations: the designated configurations through index $R(|x|)$ have empty output, the next is halted with output $[\mathrm{false}]$, and each round either halts with $[\mathrm{true}]$ when the acceptance predicate holds or reaches the next encoded configuration otherwise. Specializing the contract’s output list to the singleton $[\mathrm{true}]$ and unfolding the chosen host gives precisely the stated result.

**Key facts.** `Turing.FinTM.loopHost_contracts`.
