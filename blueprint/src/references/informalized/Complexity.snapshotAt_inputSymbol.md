<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.snapshotAt_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol at the Scheduled Position

**Claim.** For an oblivious machine, the scanned input symbol on $x$ after $t$ steps is the bit of $x$ at the input-head position scheduled on the all-zero word of the same length, with blank at either boundary.

**Proof.** Obliviousness gives equality between the input-head position after running on $x$ and the scheduled position obtained on the all-zero word of the same length. Let $c$ be the configuration reached on $x$ at time $t$; it remains to identify its scanned symbol with the input bit at its own head position. If that position is $0$, the configuration's input-symbol definition gives blank, as does the definition of the input-bit lookup. Otherwise the head position is positive. Since it is a finite position below $|x|+2$, it is either an interior input position or the right boundary. The input-symbol-at-position lemma identifies the scanned symbol with the list lookup at position one less; at the right boundary this lookup is out of range and hence blank. This is precisely the boundary-aware input-bit lookup.

**Key facts.** `Complexity.oblivious_schedule_eq`, `Turing.FinTM.inputSymbol_at`.
