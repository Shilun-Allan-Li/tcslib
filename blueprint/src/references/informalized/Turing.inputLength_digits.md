<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLength_digits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits Under Increment

**Claim.** For every natural number $n$, there are $p$ and a Boolean list $v$ such that the digits of $n$ have one of the two stated carry forms, and the digits of $n+1$ are $p$ zeros followed by one and then $v$.

**Proof.** Use the binary recursion for natural numbers. At zero, choose $p=0$ and the empty suffix: the digits of zero are empty, and those of one are the single digit one. For a number formed by appending a binary bit to $n$, split on that bit. If it is zero, choose $p=0$ and suffix $n.bits$. The binary append rule gives the old digits as the digits of $n$ followed by zero, and incrementing this even number gives the digits of $n$ followed by one. If the appended bit is one, apply the induction hypothesis to $n$, obtaining $p,v$ and the two digit descriptions. Appending the final one adds one to the initial run of ones in the old description, so the old number has the required form with $p+1$. For the incremented number, the appended-one value plus one is twice $n+1$; doubling appends a zero to the digits of $n+1$. The induction hypothesis describes those digits as $p$ zeros, then one, then $v$, so the new digits are $p+1$ zeros, then one, then $v$, as required.
