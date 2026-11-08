<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Under Concatenated Choice Words

**Claim.** Running the machine under the concatenation $ww'$ has the same effect as running it first under $w$ and then under $w'$.

**Proof.** Induct on $w$, allowing the starting configuration to vary. If $w$ is empty, running under the concatenation $w'$ is just running under $w'$ from the unchanged configuration. If $w$ begins with $b$ and has remainder $v$, the concatenation is $b$ followed by $v++w'$. The leading-bit run equation (`Turing.NDTM.runWith_cons`) rewrites the run as a run under $v++w'$ from the configuration after the $b$-step. The induction hypothesis splits that run into first $v$ and then $w'$. Applying the leading-bit equation once more identifies the first part with running under $b::v$, giving the claimed identity.

**Key facts.** `Turing.NDTM.runWith_cons`.
