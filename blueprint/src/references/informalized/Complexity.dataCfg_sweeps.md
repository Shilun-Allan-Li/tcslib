<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_sweeps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair of data sweeps

**Claim.** Starting from seek-left at guide coordinate $0$, the simulator performs a forward and backward data sweep and returns to macrostep-check at unary head $u+1$ after $6R+7$ steps, with the stated updated data tapes and neighbor registers.

**Proof.** Use the forward-prefix result for $2R+1$ steps, the full distance from the left guide edge at $-R$ to the right boundary at $R+1$. It yields tapes whose cached left-neighbor payloads encode the preceding coordinate; at the far boundary, the assumed blank vector supplies the required endpoint data. At the right boundary the forward-turn transition changes the phase to backward and resets the neighbor registers. Apply the backward-prefix result for another $2R+1$ steps, using the cached-neighbor identity obtained from the forward sweep. At the left boundary, the assumed blank vector and the backward-turn transition move the guide head back inside and change the phase to return-center. The center-run result then traverses the remaining $R+1$ positions to the origin and enters macrostep-check, with unary head advanced to $u+1$. Throughout the backward sweep, the recorded movement selects the appropriate cached neighboring payload; the resulting tape identity is exactly the piecewise update in the claim. The initial seek takes $R+2$ steps by `dataCfg_seek_run`. Adding the four travel segments gives $(R+2)+(2R+1)+1+(2R+1)+1+(R+1)=6R+7$. The run-addition and successor-step laws justify composing these segments.

**Key facts.** `Complexity.dataCfg_forward_prefix`, `Complexity.dataCfg_forward_turn`, `Complexity.dataCfg_backward_prefix`, `Complexity.dataCfg_backward_turn`, `Complexity.dataCfg_center_run`, `Complexity.dataCfg_seek_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
