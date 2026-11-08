<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_scan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a suffix of the input

**Claim.** When dropping the first $i$ bits of $y$ gives $w_i$, the scan machine has a finite safe path from its scan-reading configuration to the exit configuration determined by the access check of $w_i$ and $k$.

**Proof.** Proceed by two-step induction on the scanned word $w_i$, since the machine treats matching duplicated bits as one unit. If the word is empty, the input read is absent, so the machine rejects and restores its counter head; the read and reject path lemmas give this run (`access_read`, `access_reject`). If the word has one bit, it reads that bit and then finds no second bit, so it again rejects after restoring (`access_read`, `access_inc_pointer`, `access_reject`).

For a word beginning $b b'$, first read $b$, advance the input pointer, and read $b'$ (`access_read`, `access_jump`, `access_inc_pointer`). If $b=b'$, the pair is a valid doubled symbol: the machine advances past the pair, and scanning continues on the remaining suffix by the induction hypothesis. The access check is unchanged when a duplicated pair is removed (`accessCheck_dup`). If the bits differ and $b=0$, the scan enters its tail-processing phase; the tail's canonicality characterization identifies the result of that phase (`accessTail_canonical`), and `access_tail_run` completes the rest of the computation. If instead $b=1$ and $b'=0$, the malformed pair causes immediate rejection and restoration (`access_reject`). These cases exhaust unequal Boolean pairs. The hypotheses on $i$ and $k$ ensure the pointer increments and all intermediate configurations remain within the safe range, as required by the cited path lemmas.

**Key facts.** `Complexity.LogProg.access_read`, `Complexity.LogProg.access_reject`, `Complexity.LogProg.access_inc_pointer`, `Complexity.LogProg.access_jump`, `Complexity.LogProg.accessCheck_dup`, `Complexity.LogProg.accessTail_canonical`, `Complexity.LogProg.access_tail_run`.
