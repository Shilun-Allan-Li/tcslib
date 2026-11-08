<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_initialized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed machine startup

**Claim.** For an effective coding scheme $c$ and bit strings $b,\alpha,x$, the timed universal machine reaches within $4|b|+S$ steps a framed timed-interpreter configuration lifted from the decoded machine's initial configuration on $x$, with clock word $b$ and table cursor at the specified header position.

**Proof.** Run the timed canonicalizer for $T=4|b|+3|\alpha|+8+\text{canonizerTime}(|\alpha|)$ steps. The canonicalizer completion result says that it has halted with output equal to the decoded machine's serialization, its input head at the required position, and its clock tape containing $b$ with its head at the end (`timedCanon_complete`). The capture-start lemma then shows that the timed captured machine enters its framed timed-interpreter phase after some $t\le T+1$ steps (`timedCapture_start`); the captured frame retains the canonicalizer's work tapes and head positions (`timedCaptured_frame`). The serialization header decomposition supplies the initial-state unary prefix (`universal_serialization_header`). The interpreter-initialization lemma uses that header to position the table cursor and state tape at the prescribed initial checkpoint (`timedCut_Interpreter_initialize`), after $d=|\text{serialization}|+2|\operatorname{bin}(m)|+2q_0+7$ steps. This initialization run is nonhalting, so replaying it through the timed interpreter is valid (`timed_replay`); the framed simulation preserves it (`timedFrame_run`). The run-composition law combines the canonicalizer/capture phase and replay phase (`runFrom_add`). The pair-encoding length formula identifies the input-head position in the nested encoding (`universal_pair_length`). Finally, the displayed choices of $T$ and $d$, together with the startup-bound definition, give the claimed upper bound.

**Key facts.** `Turing.timedCanon_complete`, `Turing.timedCapture_start`, `Turing.universal_serialization_header`, `Turing.timedCut_Interpreter_initialize`, `Turing.timed_replay`, `Turing.timedFrame_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_pair_length`.
