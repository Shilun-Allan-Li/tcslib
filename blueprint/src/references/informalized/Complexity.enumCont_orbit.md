<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of Fixed-Width Binary Increment

**Claim.** For every width $w$ and every $i<2^w$, iterating the overflow-stopping increment operation $i$ times from the all-false word of length $w$ yields the length-$w$ little-endian binary representation of $i$, retaining leading zeros.

**Proof.** Induct on $i$. At $i=0$, the starting word is the representation of zero (`enumWord_zero`). For the successor case, the induction hypothesis identifies the current word with the representation of $i$. Since $i+1<2^w$, the increment operation on that representation produces the representation of $i+1$: `enumCont_inc_eq` identifies the fixed-width increment with the equivalent enumeration increment, and `enumInc_word` gives its value when there is no overflow. The iterate therefore has the claimed value after $i+1$ steps.

**Key facts.** `Complexity.enumWord_zero`, `Complexity.enumCont_inc_eq`, `Complexity.enumInc_word`.
