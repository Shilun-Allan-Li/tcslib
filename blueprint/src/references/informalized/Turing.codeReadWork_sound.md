<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadWork_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of work-action decoding

**Claim.** If the work-action reader succeeds on $x$, returning an optional work-tape write $w$, a head movement $m$, and suffix $r$, then $x$ is the encoding of $w$ followed by the encoding of $m$, followed by $r$.

**Proof.** Unpack the successful work-action read into its two stages: the write reader returns some write and intermediate suffix $r_1$, and the sign reader on $r_1$ returns some movement and suffix $r$. The returned pair and suffix identify these values with $w$, $m$, and $r$. By soundness of the write reader (`Turing.codeReadWrite_sound`), $x$ is the encoding of $w$ followed by $r_1$. By soundness of the sign reader (`Turing.codeReadSign_sound`), $r_1$ is the encoding of $m$ followed by $r$. Substitution and associativity of list concatenation yield the stated decomposition of $x$.

**Key facts.** `Turing.codeReadWrite_sound`, `Turing.codeReadSign_sound`.
