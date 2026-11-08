<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedBorrow_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Subtraction Decrements Positive Value

**Claim.** For a Boolean word of positive little-endian value, subtracting an incoming borrow flag set to true yields a word whose value plus one equals the original value.

**Proof.** Induct on the word. The empty-word case contradicts the assumed positivity, since its value is zero. For $b::bs$, split on $b$. If $b$ is false, positivity of the whole word implies positivity of the tail. Apply the induction hypothesis to the tail: its borrowed output value plus one is the tail's value. The recursive subtraction flips the leading false bit to true and passes a true carry to the tail. Using $\mathrm{Nat.bit}(false,n)=2n$ and $\mathrm{Nat.bit}(true,n)=2n+1$, the desired equality reduces to twice the tail equality, with the added one accounted for, and follows by arithmetic. If $b$ is true, the carry passed to the tail is false; `timedBorrow_false` leaves the tail unchanged and returns false. The leading bit remains true, so the output value is the original value minus one, giving the claimed equality directly from the bit-value formulas.

**Key facts.** `Turing.timedBorrow_false`.
