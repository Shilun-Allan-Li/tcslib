<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.length_restW_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for the remainder

**Claim.** For every bit string $w$, the selected remainder word has length at most $|w|$.

**Proof.** The body of $w$ is obtained by dropping four bits, so its length is at most $|w|$. The one-pass remainder transducer never increases length, by the bound `Complexity.BinArith.length_uRest_le`. Thus both `midW` (the transducer applied to the body) and `rest2W` (the transducer applied once more) have length at most the body's length. The definition of `restW` selects either `midW`, the body itself, or `rest2W`; each has length at most $|w|$, as required.

**Key facts.** `Complexity.BinArith.length_uRest_le`.
