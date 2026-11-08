<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleMark_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Bookmark Marking Step

**Claim.** From the specified bookmark configuration with nonzero position $p$, one dispatch step produces the marked configuration, updating the origin and side markers while leaving the other stated data in place.

**Proof.** Because $p\ne0$, the origin tape, which has its sole true marker at cell $0$, is blank under the second head at $p$. Thus the bookmark transition takes its branch for an absent marker: it enters the corresponding origin state, writes false on tape 1 at cell $p$, and writes the side bit on tape 2 at cell $0$ while moving that head to position $1$. The first two heads do not move, and the other tapes, input-head position, and output are unchanged. These are exactly the contents and head positions specified by the marked configuration.
