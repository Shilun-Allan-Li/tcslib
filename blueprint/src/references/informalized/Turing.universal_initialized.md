<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_initialized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Machine Startup Configuration

**Claim.** For the given code scheme and strings $\alpha,x$, the universal machine reaches within the startup bound a right-block extension of the interpreter configuration for the decoded machine's initial configuration, with the table cursor at $2\ell+q_0+3$.

**Proof.** Run the canonizer for $T=3|\alpha|+4+c.\mathrm{canonizerTime}(|\alpha|)$ steps, and call the resulting configuration $src$. Canonizer correctness (Turing.universalCanon_complete) says that it has halted, has output the decoded machine's serialization, and has its input head at the prescribed encoded-input position. The capture-start result (Turing.universalCapture_start) then places the universal machine in its captured interpreter block after some $t\le T+1$ steps; the captured-block identity (Turing.universalCaptured_right) identifies that block as a right extension of the interpreter's initial configuration, retaining the canonizer's tapes and head positions. The serialization-header decomposition (Turing.universal_serialization_header) writes the table as the pair-encoded state-count bits followed by $q_0$ unary ones and a delimiter. The interpreter initialization result (Turing.universalInterpreter_initialize) runs this initial configuration for $d=L+2\ell+2q_0+7$ steps and places it in the main phase with table cursor $2\ell+2+q_0+1=2\ell+q_0+3$. The capture/interpreter simulation identity (Turing.universalCapture_interpreter_run) and the run-addition law (Turing.MultiTapeTM.runFrom_add) combine these stages. Taking the final time to be $t+d$, the estimate $t\le T+1$ gives the stated startup bound; the remaining configuration fields agree by the definitions of the initial and simulation configurations and the canonizer's output and input-position facts.

**Key facts.** `Turing.universalCanon_complete`, `Turing.universalCapture_start`, `Turing.universal_serialization_header`, `Turing.universalInterpreter_initialize`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universalCaptured_right`, `Turing.universalCapture_interpreter_run`.
