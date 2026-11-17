<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_origin_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the origin cell

**Claim.** If the tape initially stores the one-symbol word $[\mathrm{true}]$, overwriting its origin cell with blank leaves the tape blank at every integer cell.

**Proof.** Check the tape cell by cell. At $z=0$, the update explicitly replaces the stored symbol by blank. If $z\ne0$ and $z<0$, the tape is blank there by the definition of the buffer tape. If $z>0$, then the corresponding natural-number index is positive, while the word has length one; consequently that cell is also blank. Thus every cell is blank after the update.
