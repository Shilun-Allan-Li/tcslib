<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clSymbolDecode_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the Optional-Symbol Code

**Claim.** Decoding the two-bit encoding of any optional Boolean symbol returns that same optional symbol.

**Proof.** If the symbol is absent, its encoding has first bit false, so the decoder returns none. If it is present with value $b$, its encoding has first bit true and second bit $b$, so the decoder returns some $b$. These cases establish the identity for every optional Boolean symbol.
