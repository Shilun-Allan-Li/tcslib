<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Sweep Read Update

**Claim.** After the simulator reads the blocks at coordinates $a$ through $a+n-1$, its read table is the one initialized from $c$ at coordinate $a+n$. The frontier has advanced by $nk$, the encoded blocks have been moved to the reversed left stack with preceding-block head flags recorded, and the right stack and output are unchanged.

**Proof.** Apply the general forward-sweep result `sweep_run` to the list of cells in the zone from $a$ through $a+n-1$, using `readVisit` as the local update. Its transition hypothesis holds because, on an encoded cell, the simulator advances one position to the right, writes the updated encoding, and updates the read table by the prescribed visit. The result says that after one step per cell the state records the fold of these visits, the frontier increases by the length of the encoded list, and the visited cells appear in reverse order on the left stack; the untouched right stack and output are preserved. The read-zone identity (`read_zone`) identifies that fold with the read table at $a+n$ and the zone whose preceding-block head flags have been recorded. Finally, the zone-length formula (`tapeZone_length`) gives length $nk$, and the integer cast identifies the frontier increment with $nk$.

**Key facts.** `Turing.FinTM.sweep_run`, `Turing.FinTM.read_zone`, `Turing.FinTM.tapeZone_length`.
