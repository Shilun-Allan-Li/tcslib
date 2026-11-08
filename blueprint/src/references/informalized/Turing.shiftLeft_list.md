<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.shiftLeft_list -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversing a Left-Shifted List Update

**Claim.** Reversing the list obtained by updating the reversed word with the shifted values of $g$ and the final value $b_0$ gives the same result as updating the original word using the values of $g$ on its tail followed by $b_0$.

**Proof.** Proceed by cases on the list. For the empty list, both sides are empty. For a nonempty list $a::w$, its reverse is `w.reverse ++ [a]`. In the zip on the left, the corresponding value list has one extra final entry, `g(a)`, beyond `b₀ :: w.reverse.map g`; zip truncates to the length of the reversed word, so that extra entry has no effect. Thus the left-hand zip is the zip of `w.reverse ++ [a]` with `b₀ :: w.reverse.map g`.

Both lists in this last zip have the same length. Reversing a zip of equal-length lists is the zip of their reversals in reverse order (`List.reverse_zipWith`). Reversing the two inputs gives `a :: w` and `w.map g ++ [b₀]`, respectively. Reversing the resulting list back cancels the reversal, yielding exactly the right-hand side.
