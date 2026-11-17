<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Indices_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Header Indices

**Claim.** For every finite Boolean Turing machine $M$, the initial, state, input, work, and accept residual ordinals extracted from a word each have polynomial-time computable unary encodings.

**Proof.** Start with the cursor length and the extracted instance, both polynomial-time computable by `clA5Cursor_native`. Filling a word to a specified length is polynomial-time computable (`clNative_fill`), so composing this with the cursor computation gives the first residual ordinal, obtained by subtracting the instance length from the cursor length (`clA5Sub_native`). Subtracting one more, using a constant unary word (`clA5_pt_const`), gives the state residual ordinal. Subtract the encoded horizon, whose unary encoding is available from `clA5Sizes_native`, to obtain the input residual ordinal. The work residual ordinal subtracts the horizon plus one; form that sum using `clA5Add_native` and the constant unary word, then apply `clA5Sub_native`. Finally, the accept residual ordinal subtracts $M.k$ times the horizon-plus-one quantity: `clA5Times_native` supplies that product and `clA5Sub_native` performs the final subtraction. These are exactly the five asserted unary computations.

**Key facts.** `Complexity.clA5Cursor_native`, `Complexity.clNative_fill`, `Complexity.clA5Sub_native`, `Complexity.clA5_pt_const`, `Complexity.clA5Sizes_native`, `Complexity.clA5Add_native`, `Complexity.clA5Times_native`.
