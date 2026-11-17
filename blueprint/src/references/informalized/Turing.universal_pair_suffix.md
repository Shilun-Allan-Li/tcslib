<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_pair_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix Lookups

**Claim.** At position $2|\alpha|+2+j$ in the paired encoding, the optional bit is exactly the optional bit at position $j$ in $x$.

**Proof.** First, the doubled prefix has length $2|\alpha|$: this follows by applying the pair encoding length formula to the empty suffix and subtracting the two separator entries. The encoding is therefore the concatenation of that prefix, the separator, and $x$. A lookup beyond the prefix and separator lands in the suffix; subtracting their total length $2|\alpha|+2$ from the requested index leaves $j$. Hence the optional lookup equals $x[j]?$.

**Key facts.** `Turing.universal_pair_length`.
