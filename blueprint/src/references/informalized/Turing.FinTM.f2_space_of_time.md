<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_space_of_time -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bounded by Time

**Claim.** If a finite Boolean Turing machine halts on input $x$ after exactly $T$ steps, then its total space usage through any time is at most $k(T+1)$, where $k$ is its number of work tapes.

**Proof.** The computation-time characterization (Turing.FinTM.computesInTime_iff) gives that the run at time $T$ is halted. For each tape, every head position visited through time $t$ was also visited through time $T$, unless its visit occurred later than $T$. In that latter case, write the time as $T$ plus a nonnegative remainder. By the run-addition identity (Turing.MultiTapeTM.runFrom_add) and the fact that a halted run stays fixed (Turing.MultiTapeTM.runFrom_of_halt), the head position then equals its position at time $T$. Hence the set of positions visited on each tape through time $t$ is contained in the set visited through time $T$. The latter set has at most $T+1$ elements, since it is the image of the $T+1$ times from zero through $T$. Summing this per-tape bound over the $k$ work tapes gives $k(T+1)$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
