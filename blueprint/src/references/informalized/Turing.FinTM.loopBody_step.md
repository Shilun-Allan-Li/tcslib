<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBody_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Stop Wrapper

**Claim.** If the body configuration has state $q$ and the pair $(q=a, r=\mathrm{false})$ does not occur, then one wrapper step agrees with one body step, embeds the successor with release bit false, and sets the flag to true exactly if the successor is halted, otherwise retaining the old flag.

**Proof.** Write $A$ for the body's transition action at state $q$ on the current input and work symbols. Since the configuration is live in state $q$, the body's next configuration is obtained by applying $A$. The wrapper's forbidden stopping condition is false by hypothesis, so it takes its ordinary branch: on the original tapes it uses exactly $A$, maps a live successor state to the corresponding wrapper state with release bit false, and writes true to the extra flag cell precisely when $A$ halts. The remaining wrapper tape cells are untouched. Consequently the original work tapes and head positions, input-head position, and output agree with the embedded body successor; the extra cell has the claimed flag value. This is the asserted configuration equality.
