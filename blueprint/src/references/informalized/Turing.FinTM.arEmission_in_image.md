<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arEmission_in_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitted Symbols Lie in the Embedding Image

**Claim.** If the machine computes the stated binary function on embedded inputs within the given time bound, then any symbol emitted by its next transition on such an input lies in the image of the embedding.

**Proof.** The computation hypothesis yields both that the run at time $T(|x|)$ has halted and that its output is the letterwise embedding of the required output (`Turing.FinTM.computesInTime_iff`). First suppose $t<T(|x|)$. The symbol emitted by the transition at time $t$ appears in the output after that transition: the successor-run identity and the step-output formula express the next output as the current output followed by the emitted symbol (`Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`). Since this next output is a prefix of the final output (`Turing.MultiTapeTM.output_prefix`), the emitted symbol occurs in the final output, which is a list of embedded symbols. Hence it equals $e(b)$ for some binary symbol $b$. Now suppose $t\ge T(|x|)$ and write $t=T(|x|)+d$. The run-addition law and the fact that a halted configuration remains fixed show that the configuration at time $t$ is already halted (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`). A halted configuration emits no symbol (`Turing.MultiTapeTM.outputSymbol_of_halt`), contradicting the assumption that the transition emits $a$. Thus only the first case can occur.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`, `Turing.MultiTapeTM.output_prefix`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.outputSymbol_of_halt`.
