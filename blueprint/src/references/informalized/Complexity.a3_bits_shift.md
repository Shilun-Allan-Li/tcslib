<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_bits_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary digits of a power-of-two multiple

**Claim.** For natural numbers $C,p$ with $C\ne0$, the binary digit list of $C\cdot2^p$ is $p$ zero bits followed by the binary digit list of $C$.

**Proof.** Induct on $p$. For $p=0$, the assertion reduces to the fact that the empty list of leading zeros leaves the digits of $C$ unchanged. For the successor step, write $C2^{p+1}=2(C2^p)$. The induction hypothesis’s nonzero condition holds because both $C$ and $2^p$ are nonzero. The binary-digit doubling rule (`Nat.bit0_bits`) says that doubling a nonzero number prepends one zero bit. Applying it and then the induction hypothesis gives one zero followed by the $p$ zeros and the digits of $C$, which is the required list of $p+1$ zeros followed by those digits.
