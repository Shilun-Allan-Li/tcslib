<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time First-Bit Truncation

**Claim.** The function taking a bit word to its prefix of length at most one is polynomial-time computable.

**Proof.** Use the finite-state word map whose state remains true after reading each bit, which emits nothing in state true and emits the current bit in state false, and whose initial state is false. The general finite-state word-map theorem gives polynomial-time computability of this map (`Complexity.clA5Map_poly`). To identify its output, observe that starting in state true, it emits nothing on every word; induction on the word proves this. Starting in state false, the map emits the first bit, if there is one, and then enters state true, so all later bits are ignored. For the empty word it emits nothing. Hence its output is exactly the prefix of length at most one, proving the claim.

**Key facts.** `Complexity.clA5Map_poly`.
