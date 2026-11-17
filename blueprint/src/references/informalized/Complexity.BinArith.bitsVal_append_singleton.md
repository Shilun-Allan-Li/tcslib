<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.bitsVal_append_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of an Appended Bit

**Claim.** For a finite Boolean list $w$ and a bit $b$, appending $b$ adds $b$ times $2^{|w|}$ to the value of $w$.

**Proof.** Induct on the list. For the empty list, its value is zero, and appending the single bit gives precisely its value as a bit. For a list with first bit $c$ and remaining list $w$, the defining equation gives the value as $c$ plus twice the value of the remaining list. Apply the induction hypothesis to the appended remaining list, and use $|c::w|=|w|+1$; the resulting expression agrees with the value of the original list plus $b$ times $2^{|c::w|}$ by distributivity.
