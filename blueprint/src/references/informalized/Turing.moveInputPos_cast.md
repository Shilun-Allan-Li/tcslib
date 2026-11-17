<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.moveInputPos_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Change of Position Range

**Claim.** If $n+2=m+2$, identifying the two position ranges commutes with moving a position by any sign and clamping to the range.

**Proof.** The equality $n+2=m+2$ implies $n=m$. After substituting this equality, the two position ranges and their casts are identical, so both sides are the same move and the claim follows by reflexivity.
