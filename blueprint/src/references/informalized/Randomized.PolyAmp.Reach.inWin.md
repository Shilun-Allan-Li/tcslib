<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.Reach.inWin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachable Configurations Have Bounded Representatives

**Claim.** Every reachable configuration has a representative whose work heads and nonblank tape contents lie within the prescribed window, and whose configuration code at that window size is unchanged.

**Proof.** By reachability, choose a finite choice word $u$ whose run from the initial configuration has the same machine state, input-head position, work tapes, work-head positions, and output summary as $C$. The space hypothesis and $sp(|x|)\le S$ imply that this run's final configuration lies in the window of radius $S`, by the bounded-window result for runs (`BPLInP.inWin_run`). Take that final configuration as $D$. Its core and output summary agree with those of $C$ by the chosen reachability witness, so their combined core-and-summary data agree. The configuration-code invariance theorem then gives equal codes at window size $S$ (`Complexity.Codec.cfgWord_congr`); taking the code of equal configuration words yields the required code equality.

**Key facts.** `Randomized.BPLInP.inWin_run`, `Complexity.Codec.cfgWord_congr`.
