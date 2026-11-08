<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tail Function

**Claim.** The function removing the first bit of a bit word, and returning the empty word for empty input, is polynomial-time computable.

**Proof.** Use a finite-state word map that begins in state false, emits the first bit it reads, and then enters state true; in state true it emits every subsequent bit. The general finite-state word-map theorem makes this map polynomial-time computable (`Complexity.clA5Map_poly`). Indeed, from state true the map reproduces its input, as induction on the word shows. From state false it emits nothing on the empty word; on a nonempty word it skips the first bit and then reproduces the remaining tail using the state-true behavior. Thus the map is exactly the tail function.

**Key facts.** `Complexity.clA5Map_poly`.
