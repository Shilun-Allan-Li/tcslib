<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.BPDecidesInTime.flipOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Flipping Preserves Bounded-Error Decision

**Claim.** If $N$ halts within $T(|x|)$ steps and outputs the membership indicator for $L$ with probability at least $2/3$, then the machine obtained by flipping every output bit halts within the same time and outputs the complement-language indicator with probability at least $2/3$.

**Proof.** Fix an input $x$. The flipped machine halts within the same time bound as $N$ (`Turing.FinNDTM.flipOutput_haltsWithin_iff`). The indicator of the complement language is the bitwise complement of the indicator of $L$, as is verified by splitting into the cases $x\in L$ and $x\notin L$. On every choice word, the flipped machine’s output is the original output with its bits complemented (`Turing.FinNDTM.flipOutput_outputWith`). Because bitwise complementation is injective, the flipped output equals the complement indicator exactly when the original output equals the $L$ indicator. The two events therefore have equal probability (`Randomized.randProb_congr`), preserving the $2/3$ lower bound.

**Key facts.** `Turing.FinNDTM.flipOutput_haltsWithin_iff`, `Turing.FinNDTM.flipOutput_outputWith`, `Randomized.randProb_congr`.
