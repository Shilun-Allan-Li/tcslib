<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_counter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A machine for writing the binary length

**Claim.** There exist a natural number $K$, a finite state set $S$ with decidable equality, a deterministic machine $R$ with $K+1$ work tapes and Boolean symbols, entry and exit states, and a natural number $B$, such that for each Boolean word $x$, the machine started with its first tape blank and input $x$ reaches the exit configuration with the binary expansion of $|x|$ on that tape, does not reach the exit state earlier, and uses at most $B$ times one plus the binary expansion length of $|x|$ in space through that time.

**Proof.** Take the machine supplied by the input-length machine existence theorem, which computes the binary expansion of the input length and provides a bound $C$ on each work-head displacement in terms of the input length. Start it in the specified initial configuration, with an empty first tape and all other tapes blank. These initial contents satisfy the theorem's required blank-region hypotheses. Its conclusion gives a halting time, the required binary output, and the fact that the exit state was not reached earlier. The output configuration agrees with the stated configuration: on the first tape, the machine's stored binary digits occupy the relevant nonnegative positions, while positions outside their range remain blank by the buffer-restriction lemma; every other tape remains blank. For the space estimate, fix a tape. Every position visited by its head through the halting time lies in the integer interval from $-C(|x.\mathrm{length.bits}|+1)$ to $C(|x.\mathrm{length.bits}|+1)$, by the displacement bound and the initial head position zero. Thus its visited-position set has at most $2C(|x.\mathrm{length.bits}|+1)+1$ elements. Summing over the $K+1$ tapes bounds total space by $(K+1)(2C(|x.\mathrm{length.bits}|+1)+1)$, which is at most $(K+1)(2C+1)(|x.\mathrm{length.bits}|+1)$. Choose $B=(K+1)(2C+1)$.

**Key facts.** `Complexity.exists_inputLengthTM`, `Complexity.b3a_buffer_restrict`.
