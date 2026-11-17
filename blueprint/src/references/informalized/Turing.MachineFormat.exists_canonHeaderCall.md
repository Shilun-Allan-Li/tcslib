<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Header Call Machine

**Claim.** For every machine format $F$, a finite Boolean-alphabet machine with at least one work tape reaches a designated exit with the canonical header on tape zero and all other tapes empty, in positive linear time, and does not reach that exit at an intermediate positive time.

**Proof.** The pair-first projection machine computes the canonical header in linear time. Apply the input-call construction to this computation: it produces a machine that starts with blank work tapes, writes the computed word in the designated state-word layout, and reaches its exit for the first time at a positive step. The construction's bound is $c(T(|\alpha|)+|\alpha|+|canonHeader(\alpha)|+1)$. Since the canonical header has length at most $|\alpha|$, substituting $T(n)=a(n+1)$ bounds this by $c(a+2)(|\alpha|+1)$, as required.

**Key facts.** `Turing.FinTM.computesFunInTime_pairFst`, `Turing.FinTM.exists_inputCallTM`, `Turing.MachineFormat.canonHeader_length`.
