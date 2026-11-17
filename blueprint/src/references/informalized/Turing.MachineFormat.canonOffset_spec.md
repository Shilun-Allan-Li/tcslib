<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonOffset_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical offset value and length

**Claim.** For every Boolean word $w$, the canonical offset has binary digit value $2|w|+3$ and length at most $|w|+2$.

**Proof.** The canonical offset begins with $1$, followed by the canonical count for the binary expansion of $|w|$. By the canonical-count identity (`canonCount_spec`), folding the count bits with the binary-bit operation gives the fold of the input bits plus one. The fold-to-digit-value identity (`foldr_bit_eq_ofDigits`) therefore identifies the offset's digit value with the binary value of the leading $1$ followed by those bits. The binary-expansion identity (`codeBitsNat_bits`) says that the bits encode $|w|$, so the leading bit and added one yield $2|w|+3$. For the length bound, the canonical count has length $|w|.bits.length+1$ by `canonCount_spec`. The length of the binary expansion is at most $|w|$ (from the standard bound on the size of a natural number), and adding the offset's leading bit gives the claimed bound.

**Key facts.** `Turing.MachineFormat.canonCount_spec`, `Turing.foldr_bit_eq_ofDigits`, `Turing.codeBitsNat_bits`.
