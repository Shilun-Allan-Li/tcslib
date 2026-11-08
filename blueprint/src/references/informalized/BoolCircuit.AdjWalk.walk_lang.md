<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.walk_lang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Decidability of Indexed Languages

**Claim.** Under the stated canonicality, polynomial-size, and logspace adjacency assumptions, the indexed language described by $p$ is decidable in logarithmic space, given the two hypotheses connecting valid descriptions and the circuit encoding bits to $p(1^n,i)$.

**Proof.** First, the logspace adjacency hypotheses give logspace deciders for all five oracle languages used by the walk: size, the four vertex types, and edges. Apply the simulation theorem for register programs with logspace oracles (`Complexity.LogProg.arm_decides_poly`) to the walk. It remains to show that this walk decides the indexed language with a polynomial register bound.

For a valid input, write it as the prescribed paired encoding of a unary word and a canonical binary payload $w$. The canonical-binary representation theorem identifies $w$ with the bits of the natural number represented by $w$. The walk’s halting theorem (`BoolCircuit.AdjWalk.walk_halts`) says that on this unary input and index it halts with the corresponding circuit-encoding bit, combined with $\ell$ if the index is in range. By the hypothesis relating these bits to $p(1^n,i)$, this is exactly the indicator of membership in the indexed language: the paired-encoding membership equivalence (`Complexity.pairEncode_mem_indexLang`) and the indicator characterization (`Complexity.LogProg.indicator_eq_decide`) make that identification explicit.

Canonicality bounds the circuit encoding length by a cubic polynomial in its size (`BoolCircuit.AdjWalk.length_encode_le_of_canonical`). The circuit family’s polynomial size bound then bounds the walk’s registers by a polynomial in the input length. The valid input’s unary portion cannot exceed its total length, so this is a polynomial register bound of the form required by the simulation theorem.

For an invalid plain encoding, the indicator of the indexed language is false: if it were a member, the hypothesis that a positive instance has a nonempty description would force the first component to be unary, contradicting invalidity. The machine rejects such inputs immediately, with bounded registers. Thus the walk decides the language on both valid and invalid inputs, and the simulation theorem yields logarithmic-space decidability.

**Key facts.** `BoolCircuit.AdjWalk.length_encode_le_of_canonical`, `BoolCircuit.AdjWalk.walk_halts`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.indicator_eq_decide`, `Complexity.pairEncode_mem_indexLang`, `BoolCircuit.AdjWalk.preS_walk`, `Complexity.LogProg.AHalt.mono`, `Complexity.LogProg.canon_bits`, `BoolCircuit.AdjWalk.eq_replicate_of_descr_ne`, `Complexity.LogProg.arm_decides_poly`.
