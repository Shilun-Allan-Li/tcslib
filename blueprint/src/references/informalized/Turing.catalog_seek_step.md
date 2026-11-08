<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_seek_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seek Step Head Update

**Claim.** Under the stated transition condition, one step from the configuration with phase $q$ and head $i$ shifted by $z$ produces the configuration with phase $q'$ and head $i$ shifted by $z+m$.

**Proof.** Apply the machine-step formula for an action that moves a single work-tape head without writing (`Turing.step_of_tapeAction_move`). It leaves the input position and tape contents unchanged, changes the state to $q'$, and updates head $i$ from its current position by adding $m$. In the starting configuration that position is the original position plus $z$, so the new position is the original position plus $z+m$. All other work-tape heads are unchanged. Comparing the resulting configuration componentwise gives the stated equality.

**Key facts.** `Turing.step_of_tapeAction_move`.
