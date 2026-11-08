<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathWalk.lean :: Complexity.LogProg.size_eq_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Size Under Halving

**Claim.** Every nonzero natural number has binary size one greater than the binary size of its quotient by $2$.

**Proof.** The binary size of a natural number is the length of its `Nat.bits` list (`Nat.size_eq_bits_len`). Since $\tau\ne0$, its binary expansion has a leading low-order bit followed by the bits of $\tau/2$ (`bits_eq_cons`). Thus its bit list is a cons whose tail is the bit list of $\tau/2$; taking lengths gives $\operatorname{size}(\tau)=\operatorname{size}(\tau/2)+1$.

**Key facts.** `Complexity.bits_eq_cons`.
