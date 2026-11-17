<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/WholeProgram.lean :: Light.Compiler.steps_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the verdict tail

**Claim.** Given the tail code and the stated memory and range conditions, execution reaches a configuration within three steps where the result location contains the word for $r$, memory agrees with its initial value outside the result and decision locations, and the next instruction terminates with the verdict that is true exactly when the decision flag is false or $r$ is positive.

**Proof.** The first tail instruction copies the value at the main-frame stack location into the result location. Since the zero location holds zero, the addition-step rule (`WordRAM.steps_add`) realizes this copy in one step. The result cell then contains the word for $r$; agreement with the original memory outside the result and decision locations follows because this first write is at the result location (`WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`).

If the decision flag is false, the next instruction accepts. The code-prefix facts `WordRAM.CodeAt.tail` and `WordRAM.CodeAt.head`, together with the acceptance rule (`WordRAM.step_accept`), give the required terminating verdict after the single copy step.

If the flag is true, the next instruction computes $0-r$ in the decision register by the subtraction-step rule (`WordRAM.steps_sub`). The following branch tests this value. The assumed range condition is precisely the condition needed for the branch rule (`WordRAM.steps_bltz`); since $0-r<0$ exactly when $r>0$, a positive $r$ branches to the accept instruction, while a nonpositive $r$ proceeds to reject. In either case, the appropriate terminating-step rule (`WordRAM.step_accept` or `WordRAM.step_reject`) gives the verdict, which is exactly the stated Boolean condition. These two further steps preserve the result cell because they write only the decision register, so agreement outside the two designated locations persists by repeated use of `WordRAM.AgreeOutside.update`. The true-flag path uses three steps in total, and the false-flag path uses one.

**Key facts.** `WordRAM.steps_add`, `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `WordRAM.CodeAt.tail`, `WordRAM.CodeAt.head`, `WordRAM.step_accept`, `WordRAM.steps_sub`, `WordRAM.steps_bltz`, `WordRAM.step_reject`.
