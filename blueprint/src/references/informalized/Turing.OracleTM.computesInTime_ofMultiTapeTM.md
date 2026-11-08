<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.computesInTime_ofMultiTapeTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Simulation of a Plain Machine

**Claim.** The oracle machine obtained by embedding a deterministic machine computes $y$ on input $x$ within $t$ steps exactly when the original machine is halted after $t$ steps with output $y$.

**Proof.** First, the embedded machine’s initial configuration is the oracle embedding of the original initial configuration, by the initial-configuration embedding identity (`Turing.Cfg.embedOracle_init`). The run correspondence theorem (`Turing.OracleTM.runFrom_ofMultiTapeTM`) then identifies the embedded machine’s configuration after $t$ steps with the oracle embedding of the original machine’s configuration after $t$ steps. Finally, embedding preserves the output (`Turing.Cfg.embedOracle_output`) and preserves whether the state is halting (`Turing.Cfg.embedOracle_state_eq_none`). Thus the two conditions defining computation in time $t$ agree componentwise, proving the equivalence.

**Key facts.** `Turing.Cfg.embedOracle_init`, `Turing.OracleTM.runFrom_ofMultiTapeTM`, `Turing.Cfg.embedOracle_state_eq_none`, `Turing.Cfg.embedOracle_output`.
