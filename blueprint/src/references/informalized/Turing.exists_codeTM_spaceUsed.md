<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.exists_codeTM_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coded Machine Preserving Time and Space

**Claim.** Every finite Boolean machine with exactly one work tape has a code normal form machine that preserves time-bounded computation and has the same total work-tape space usage at every time and on every input.

**Proof.** Represent the finite state set $Q$ by a finite initial segment. Since the machine has an initial state, $Q$ is nonempty, so its cardinality $N$ is positive; hence $N=(N-1)+1$. Choose an equivalence between $Q$ and the $N$ states of $\mathrm{Fin}(N)$, and relabel the machine's states along this equivalence. Its one tape and all tape operations are unchanged, so this relabeled machine is in code normal form. Relabeling carries every run from the initial configuration to the state-mapped original run (`Turing.MultiTapeTM.relabelState_runFrom_init`), preserving whether it halts and its output. Thus the existential space witness in the definition of time-bounded computation transfers in either direction, proving the computation equivalence. Relabeling also leaves the visited tape-head positions, and therefore the space used, unchanged (`Turing.MultiTapeTM.relabelState_spaceUsed`).

**Key facts.** `Turing.MultiTapeTM.relabelState_runFrom_init`, `Turing.MultiTapeTM.relabelState_spaceUsed`.
