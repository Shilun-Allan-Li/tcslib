<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPrepare_extra -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extra Preparation Step

**Claim.** For every natural number $k$ and Boolean words $w,s$, one step of the preparation machine from its scan configuration at position $|s|$ gives its ready configuration in state $1$, with the flag recording whether $|w|<|s|$ and the first work-tape head at $|s|-1$.

**Proof.** At scan position $|s|$, the first work-tape head is reading the blank cell just beyond the stored word $s$. Thus the machine takes its state-$0$ transition for a blank cell: it moves the first work-tape head one place to the left, writes true on each other tape at cell $|s|$, and enters state $1$, retaining the length-comparison flag. The input head does not move, and the output remains empty. The write on each other tape changes its catalog from cells $0$ through $|s|-1$ to cells $0$ through $|s|$, by the catalog-tape write identity (`f2_catalogPolyTape_write`). The input-head position is unchanged because a zero movement fixes it (`moveInputPos_zero`). These componentwise facts give exactly the stated ready configuration.

**Key facts.** `Turing.FinTM.f2_catalogPolyTape_write`, `Turing.moveInputPos_zero`.
