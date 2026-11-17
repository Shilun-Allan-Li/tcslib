<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.natCast_sub_mod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction modulo a positive modulus

**Claim.** For $p>0$, the residue of $r+p-(x\bmod p)$ modulo $p$ equals the residue of $r$ minus the residue of $x$ in $\mathbb{Z}/p\mathbb{Z}$.

**Proof.** Casting a remainder modulo $p$ into $\mathbb{Z}/p\mathbb{Z}$ gives the same residue as casting the original number, and the cast of $p$ is zero. Because $x\bmod p<p$, the natural-number subtraction is valid and its cast agrees with subtraction in the ring. Consequently the left side casts to $r+0-x=r-x$, as claimed.
