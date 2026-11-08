<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFuel_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop fuel run simulation

**Claim.** Running the loop fuel source machine for $t$ steps from the loop fuel configuration built from $c$ gives the loop fuel configuration built from the configuration reached by running $F$ for $t$ steps from $c$.

**Proof.** The loop fuel machine is obtained by adjoining unused work tapes to $F$, and its starting configuration adjoins the same blank tapes to $c$. Apply the simulation theorem for adding tapes on the right (`rightCfg_run`) to identify its run with the right-padded configuration of $F$'s run. The padding is exactly the one used to define the loop fuel configuration, so the two configurations are equal.

**Key facts.** `Turing.FinTM.rightCfg_run`.
