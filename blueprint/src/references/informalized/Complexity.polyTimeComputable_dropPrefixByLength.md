<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.polyTimeComputable_dropPrefixByLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Removal

**Claim.** For a bit string parsed into components $a$ and $b$ by the aligned pair parser, with empty strings used when decoding fails, dropping the first $|a|$ bits from $b$ is polynomial-time computable.

**Proof.** The proof instantiates the general machine-transfer theorem for a program whose output is known on every input. Specifically, it uses the prefix-removal program with its scan label and the polynomial time bound $5(|z|+1)$. The total-correctness result for that program says that, on input $z$, it halts with output `drop z`, which is the stated function, within this bound (`PrefixByLength.goes_total`). The general theorem then turns this per-input program correctness and time bound into polynomial-time computability (`CounterProg.polyTimeComputable_of_goes`).

**Key facts.** `Complexity.CounterProg.polyTimeComputable_of_goes`, `Complexity.PrefixByLength.goes_total`.
