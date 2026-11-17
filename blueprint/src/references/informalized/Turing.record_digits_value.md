<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.record_digits_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Bounded Binary Digit List

**Claim.** When $v<2^w$, the base-two value of the first $w$ binary digits of $v$ is $v$.

**Proof.** Induct on the width $w$, generalizing over $v$. At width zero, the bound forces $v=0$, and both sides are zero. For width $w+1$, the digit list consists of the low bit of $v$ followed by the first $w$ digits of $\lfloor v/2\rfloor$. The induction hypothesis applies to the quotient because $v<2^{w+1}$ implies $\lfloor v/2\rfloor<2^w$. The base-two value of a list with first digit $b$ is $b+2$ times the value of the remaining list. The low bit is the remainder of $v$ modulo two, either zero or one; combining it with twice the quotient gives $v$ by Euclidean division.
