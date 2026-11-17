<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrict_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Form of a Fixed Sign Restriction

**Claim.** Applying the coordinate rules that leave $J$ free and fix the other coordinates according to $z$, then converting a binary input to signs and evaluating $f$, agrees with fixing the outside signs in $f$ and evaluating on the signs encoded from the binary input.

**Proof.** Compare both functions at an arbitrary binary input. The completion of the coordinate rules is, by the completion formula for a fixed sign restriction (`complete_coordRestrictionOf`), the sign vector formed from the fixed outside assignment $z$ and the signs encoding the input on $J$. This is exactly the input used by the extended sign restriction after converting the binary input coordinatewise to signs. Evaluating $f$ on these equal sign vectors proves the equality.

**Key facts.** `FABL.complete_coordRestrictionOf`.
