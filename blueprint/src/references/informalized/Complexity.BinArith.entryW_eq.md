<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.entryW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of an Encoded Arithmetic Entry

**Claim.** For all natural numbers $p,f,r,y$, the arithmetic entry obtained from the nested pair encoding of their binary representations is the binary representation of $(r+p-fy\bmod p)\bmod p$, with subtraction taken in the natural numbers.

**Proof.** Unpacking the outer and inner pair encodings recovers, in order, the binary representations of $p,f,r,y$. Their bit values are therefore those four natural numbers. Unfolding the entry computation, its innermost multiplication yields $fy$, and reducing gives $fy\bmod p$. The next subtraction-and-addition stage forms $r+p-(fy\bmod p)$ in the natural numbers; the final reduction takes this quantity modulo $p$. The output is the binary representation of that result, as claimed.
