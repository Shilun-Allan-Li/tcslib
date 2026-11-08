<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathWalk.lean :: Complexity.LogProg.ups_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length loop from multiplication

**Claim.** Given the stated register bounds, zero scratch and walk-length registers, and the size bound, the length-loop entry has the same acceptance probability $q$ as the supplied walk-start states.

**Proof.** The proof builds the initialization chain backward from the walk-start routine. First, it clears the inner counter and applies the increment routine for each of the five additions by $2n$, producing the required value $10n$ in the scratch-sum register. The addition result (`ups_ad`) handles each such loop; the register bound follows from $100n^4+10n\le B$. The proof then invokes the first multiplication routine (`ups_mul`) to form $n(10n)$ in the scratch-product register. A second multiplication routine forms the walk-length value $n(10n)\cdot n(10n)=100n^4$; the displayed identity is elementary algebra, and the size assumption bounds this value by $B$. The auxiliary inequality $n(10n)\le100n^4+10n$ ensures the intermediate register values also fit within the bound. At this point, the supplied hypothesis applies with outer counter $n(10n)$ and arbitrary allowed inner counter. The deterministic clears and register-record equalities preserve the same termination and probability property throughout the chain, yielding the claim at $lc(0)$.

**Key facts.** `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.ups_ad`, `Complexity.LogProg.ups_mul`, `Complexity.LogProg.UPS.of_eq`.
