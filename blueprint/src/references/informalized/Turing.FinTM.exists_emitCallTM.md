<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_emitCallTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Emitting Call Simulation

**Claim.** A finite Boolean machine can simulate a given machine as a clean call: from an entry configuration holding $a$ on the first work tape, it reaches an exit configuration with the same tape contents and head positions, and with output $f(a)$, in time bounded linearly by the given computation time and the relevant word lengths.

**Proof.** Apply the emitting-call construction to $M$, with emission enabled. Its call lemma supplies a machine, entry and exit states, and a uniform bound with coefficient $24+13M.k$. Specialize the lemma’s input to $x$ and its argument to $a$; use the hypothesis that $M$ computes $f(a)$ within $T(|a|)$ steps. The lemma gives a positive completion time within the stated bound, guarantees no earlier visit to the exit state, and identifies the final configuration as the clean exit configuration with the original argument tape restored and output $f(a)$. The constructed machine has at least one work tape by the call lemma’s construction. The theorem takes the same coefficient and transfers the call lemma’s intermediate-time condition to the formulation that only quantifies over positive intermediate times.

**Key facts.** `Turing.FinTM.emCall_first`.
