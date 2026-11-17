<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bitsVal_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Expansion

**Claim.** For every natural number $n$, the value of its binary bit list is $n$.

**Proof.** Use strong induction on $n$. For $n=0$, the binary list is empty and its value is $0$. For positive $n$, write $n=2\lfloor n/2\rfloor+b$, where $b$ is the parity bit. The binary expansion satisfies $\mathrm{bits}(n)=b::\mathrm{bits}(\lfloor n/2\rfloor)$ (`bits_two_mul_add`); when the quotient is zero, the parity bit is $1$, as required by that lemma's hypothesis. By the recursive definition of the value, the value of this list is $b+2\,\mathrm{bitsVal}(\mathrm{bits}(\lfloor n/2\rfloor))$. The quotient is smaller than $n$, so induction makes this $b+2\lfloor n/2\rfloor=n$.

**Key facts.** `Complexity.LogProg.bits_two_mul_add`.
