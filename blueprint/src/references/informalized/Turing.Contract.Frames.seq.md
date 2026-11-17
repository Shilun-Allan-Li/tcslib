<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.Frames.seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frames Under Sequential Composition

**Claim.** If the first and second contracts preserve work-tape contents outside their respective frame sets, then their sequential composition preserves contents outside the union of the first frame set and the second frame set evaluated at the linked parameter and renamed first endpoint.

**Proof.** Fix an index, a starting configuration satisfying the entry-state and precondition hypotheses, a tape, and a position outside the union of the two relevant frame sets. The first contract's frame property says that this position's content is unchanged between the starting configuration and the first endpoint. The endpoint has the required second entry state by the trajectory fact for sequential composition (Turing.Contract.seq_traj); the linked precondition then allows the second contract's frame property to apply. Since the position is outside the second frame as well, its content is unchanged from the first endpoint to the final endpoint. Chaining the two equalities gives the claimed preservation. Renaming the final state does not alter tape contents, by the state-renaming preservation fact (Turing.Cfg.SameOutside.mapState); the two preservation steps combine by the transitivity fact for preservation outside frames (Turing.Cfg.SameOutside.trans).

**Key facts.** `Turing.Contract.seq_traj`, `Turing.Cfg.SameOutside.trans`, `Turing.Cfg.SameOutside.mapState`.
