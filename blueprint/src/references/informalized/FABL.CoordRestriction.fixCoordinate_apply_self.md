<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.fixCoordinate_apply_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State at the Fixed Coordinate

**Claim.** After fixing coordinate $i$ according to $s$, the restriction state at $i$ is the state determined by $s$.

**Proof.** The operation fixing coordinate $i$ is a function update: it replaces the value at $i$ by the state determined by $s$. Evaluating this update at its own updated coordinate therefore gives exactly that state.
