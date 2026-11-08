<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_space_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound from Head Radius

**Claim.** If every work-tape head position throughout the run from the initial configuration lies between $-B$ and $B$, then the total space used through any time is at most $k(2B+1)$.

**Proof.** Fix a tape. Every position it visits through time $t$ lies in the integer interval $[-B,B]$ by hypothesis. This interval contains exactly $2B+1$ integers, so the number of distinct visited positions on that tape is at most $2B+1$. Summing this bound over the $k$ work tapes yields total space at most $k(2B+1)$.
