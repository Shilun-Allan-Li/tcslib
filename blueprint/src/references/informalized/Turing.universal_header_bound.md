<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_header_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialized Header Length Bound

**Claim.** For a machine $M$ in code normal form, the binary length of its canonical serialization is at least $2\ell+2+q_0+1$, where $\ell$ is the bit length of its state-count parameter and $q_0$ is its initial state index.

**Proof.** By the serialization-header decomposition (Turing.universal_serialization_header), the serialized word is a pair encoding of the state-count bits and a second component beginning with $q_0$ copies of $1$, followed by a $0$. The pair-encoding length formula (Turing.universal_pair_length) gives total length $2\ell+2$ plus the length of that second component. Its indicated prefix has length $q_0+1$, so the total is at least $2\ell+2+q_0+1$.

**Key facts.** `Turing.universal_serialization_header`, `Turing.universal_pair_length`.
