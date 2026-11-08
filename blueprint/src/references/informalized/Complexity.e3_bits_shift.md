<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_bits_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary expansion after a power-of-two shift

**Claim.** For natural numbers $C,p$ with $C\ne0$, the binary expansion of $C\cdot 2^p$ is the list of $p$ zero bits followed by the binary expansion of $C$.

**Proof.** Induct on $p$. When $p=0$, multiplication by $1$ leaves the binary expansion unchanged, and the list of zero bits is empty. For the successor step, $C\cdot2^{p+1}=2(C\cdot2^p)$. The binary expansion of twice a nonzero number is obtained by placing a zero bit at its beginning. The induction hypothesis applies because $C\cdot2^p$ is nonzero, and prepending this additional zero to the existing $p$ zeros gives the required list of $p+1$ zeros.
