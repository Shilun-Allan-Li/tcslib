<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.iterate_measure_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration reaches zero measure

**Claim.** Suppose a property is preserved by $g$, the natural-number measure strictly decreases under $g$ whenever it is positive on a state satisfying the property, and $g$ fixes such a state when its measure is zero. Then after $n$ iterations from any state satisfying the property with measure at most $n$, the measure is zero.

**Proof.** Fix the starting state and induct on the bound $n$. When $n=0$, the measure is at most zero, hence is zero already; zero iterations leave it unchanged. For the successor bound, apply $g$ once and then use the induction hypothesis for the remaining $n$ iterations. If the starting measure is zero, the fixed-point assumption says this first step leaves the state unchanged, so its measure remains zero and is at most $n$. If the measure is positive, strict decrease makes the new measure smaller than the old one, hence at most $n$. The property is preserved as well, so the induction hypothesis applies to the new state. In either case, after the remaining iterations the measure is zero.
