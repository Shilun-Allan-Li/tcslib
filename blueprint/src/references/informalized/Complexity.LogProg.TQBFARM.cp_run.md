<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.cp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Copy Operation

**Claim.** Under the stated register bounds, zero scratch register, and bound on the source-plus-destination sum, the copy operation reaches its exit label with the source value added to the destination and all other registers unchanged; every earlier configuration satisfies the guard and register bound.

**Proof.** The machine’s seven phases at a copy site implement the usual bounded copy loop: repeatedly decrease the source while increasing the destination and the scratch counter, then use the scratch counter to restore the source. The scratch counter starts at zero, and the source and destination are distinct from each other and from that counter, so these updates preserve the intended values of the other registers. The loop’s intermediate values stay within the bound: the destination never exceeds its final value, which is bounded by the assumed source-plus-destination sum, while the other registers remain bounded. The general copy-loop theorem supplies the resulting guarded reachability (`Complexity.LogProg.copy_run`). Its hypotheses hold here: the register distinctness is `cp_ne`; the instruction phases are those prescribed by the machine; the zero scratch hypothesis is given; and `St.Bd.toV` and the assumed sum bound provide the required register bounds. Applying that theorem gives the stated endpoint and guard.

**Key facts.** `Complexity.LogProg.TQBFARM.cp_ne`, `Complexity.LogProg.TQBFARM.St.Bd.toV`, `Complexity.LogProg.copy_run`.
