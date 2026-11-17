<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCanon_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Canonizer Run Correspondence

**Claim.** At every time $t$, the timed canonizer's run on the nested encoding agrees with a buffered second-phase configuration formed from the canonizer's run on $\alpha$, for some Boolean tag, with the specified input position, buffer contents, and heads.

**Proof.** Split the total time into the startup duration $4|b|+3|\alpha|+8$ and the remaining $t$ steps, using the run-addition law (`runFrom_add`). The startup theorem (`timedCanon_start`) identifies the configuration at the split with the buffered second-phase configuration whose simulated canonizer is initially on $\alpha$, whose tag is true, and whose input position and buffer tapes have the stated values. Now apply the buffered second-phase simulation theorem (`bufferedSecondCfg_run`) for the next $t$ steps. It supplies a Boolean tag at the end and identifies the resulting buffered machine configuration with one built from the canonizer's actual configuration after $t$ steps. This is exactly the required correspondence. The length identity for the nested encoding (`timed_input_length`) supplies the bound needed to form the indicated input-head position.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.timedCanon_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.timed_input_length`.
