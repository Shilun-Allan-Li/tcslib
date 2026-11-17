<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationValidity_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Validity Encoding Length

**Claim.** Under the stated lower bound on $C$, the serialized configuration-validity CNF has length at most $(3B+7)C^2(s+n+2)^3$, where $B$ is the coefficient specified in the statement.

**Proof.** The raw encoding-length estimate bounds the serialized formula by $\bigl(B(s+n+2)^2+2C(s+n+1)\bigr)\bigl(C(s+n+1)+3\bigr)+1$ (`configurationValidity_size_raw`). Set $t=s+n+1$. The lower bound on $C$ gives $1\le C$, and $t\ge1$. The normalization inequality `codec_size_normalize` bounds the raw expression by $(3B+7)C^2(t+1)^3$. Since $t+1=s+n+2$, this is the claimed estimate.

**Key facts.** `Complexity.configurationValidity_size_raw`, `Complexity.codec_size_normalize`.
