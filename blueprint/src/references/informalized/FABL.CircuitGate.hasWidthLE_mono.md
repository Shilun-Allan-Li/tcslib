<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitGate.hasWidthLE_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of representation width

**Claim.** If a function has width at most $u$ in the normal form associated with a gate and $u\le v$, then it has width at most $v$ in that same normal form.

**Proof.** If the gate is AND, the hypothesis supplies a CNF representing the function with width at most $u$. Keep that same CNF; transitivity of the width inequalities gives width at most $v$. If the gate is OR, the hypothesis instead supplies a DNF with width at most $u$, and the same argument with that DNF proves the result.
