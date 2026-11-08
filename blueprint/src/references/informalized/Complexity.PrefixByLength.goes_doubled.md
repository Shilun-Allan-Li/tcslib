<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_doubled -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a Doubled Prefix

**Claim.** For either program parameter, all bit strings $u,t$ and every $n$, on input formed by doubling each bit of $u$ and appending $t$, the program starting at scan with register $n$ and position $0$ returns to scan with register $n+|u|$ and position $2|u|$, adding no output, in at most $3|u|$ steps. This holds for any output already printed.

**Proof.** Induct on $u$. For the empty string, the input is just the tail, and zero steps leave the machine at scan with its initial register and position; the zero-step run is the identity (`Complexity.CounterProg.run_zero`). For $u=b::u'$, the first copy of $b$ is read at scan, and the second is read at the corresponding second-bit label. Both reads consume one bit and return the machine to the bump label, without changing the register or output (`Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`). The bump instruction increments the register once and returns to scan (`Complexity.PrefixByLength.goes_inc_one`). Apply the induction hypothesis to $u'$ with initial register $n+1$. Its input is the remaining doubled prefix followed by the tail; prepending $[b,b]$ shifts the starting position by two while preserving the rest of the run (`Complexity.CounterProg.Goes.prepend_input`). Concatenating the two reads, increment, and inductive run gives the claimed final register and position, with no output (`Complexity.CounterProg.Goes.trans`). The step bound is one step per read, one increment, and at most $3|u'|$ further steps, hence at most $3|u|$; the final parameter and bound bookkeeping is captured by `Complexity.CounterProg.Goes.congr`.

**Key facts.** `Turing.dbl_nil`, `Complexity.CounterProg.run_zero`, `Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`, `Complexity.PrefixByLength.goes_inc_one`, `Complexity.CounterProg.Goes.prepend_input`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
