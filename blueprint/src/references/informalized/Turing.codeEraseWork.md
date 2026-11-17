<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeEraseWork -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Action Erasure Law

**Claim.** For every bit string, discarding the decoded work-tape write and head movement gives the same result as first consuming any two-bit pair and then consuming a second pair unless it is $01$.

**Proof.** The work-action reader parses a write first and then parses a sign from the remaining suffix. Discarding the write value leaves exactly the result of consuming its two-bit code, by the write-reader erasure law (`codeEraseWrite`). To erase the subsequent sign parsing, use the fact that binding a continuation of the suffix commutes with first discarding the value (`codeErase_bind`), and then apply the sign-reader erasure law (`codeEraseSign`): it consumes a second pair precisely when that pair satisfies the sign code's validity condition. The resulting two successive pair skippers are the stated work skipper.

**Key facts.** `Turing.codeEraseWrite`, `Turing.codeErase_bind`, `Turing.codeEraseSign`.
