<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonBoolBranch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine branching on a computed Boolean value

**Claim.** A finite Boolean-alphabet machine computing the Boolean value $p(x)$ in linear time can be converted into a finite machine that reaches one of two distinct blank-tape exit states according to that value, within a linear time bound, and reaches neither exit state earlier.

**Proof.** Apply the strict installation construction (`canonStrictInstall`) to the given machine and the one-symbol output function $x\mapsto[p(x)]$. It supplies a machine that, on an argument word, halts at a distinguished exit while leaving a canonical state word encoding its output on its work tapes, with a linear time bound and no earlier visit to that exit. Choose one work tape, available because the construction guarantees at least one. The new machine first copies its input onto that tape (`inputCopyTM_run_ofCfg`), then runs the installed computation with the input as its argument, using the seam-composition run and first-return results (`seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`). At the installed exit, the state word is the singleton $[p(x)]$. A final one-step Boolean-pop routine (`canonBoolPop_run`) reads that bit, clears the tape, and enters the corresponding Boolean exit state. The two exit states are distinct by injectivity of the Boolean tagging. The first-return properties for the component machines ensure neither exit is visited before the final routine enters it. The copy, computation, and fixed final steps together fit a bound of the form $a(|x|+1)$ for a suitable natural number $a$.

**Key facts.** `Turing.MachineFormat.canonStrictInstall`, `Turing.inputCopyTM_run_ofCfg`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.MachineFormat.canonBoolPop_run`.
