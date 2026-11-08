<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bits_getLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Bit of a Binary Expansion

**Claim.** If the binary bit list of $n$ is nonempty, then its final bit is $1$.

**Proof.** Use strong induction on $n$. The zero case is impossible under the nonemptiness assumption, since $0$ has the empty binary list. For positive $n$, write $n=2\lfloor n/2\rfloor+b$ with parity bit $b$. Then $\mathrm{bits}(n)=b::\mathrm{bits}(\lfloor n/2\rfloor)$ (`bits_two_mul_add`). If the quotient's bit list is empty, its value is zero; since the value of the binary expansion is the number itself (`bitsVal_bits`), the quotient must be zero. In that case positivity of $n$ forces $b=1$, and the full list is the singleton $[1]$. Otherwise the quotient's bit list is nonempty, and the induction hypothesis says its last bit is $1$. Prepending $b$ does not change that last bit, proving the claim.

**Key facts.** `Complexity.LogProg.bits_two_mul_add`, `Complexity.LogProg.bitsVal_bits`.
