<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Program Correctness

**Claim.** For every finite bit string $x$, the specified 13-register oracle program, started in its length-testing state with all registers zero and no answer recorded, halts with answer true exactly when $x$ encodes a pair of binary numerals whose product is the third numeral. Throughout every step before halting, its configuration satisfies the program’s safety conditions and every register is at most $4(|x|+1)$.

**Proof.** First, the length-testing loop counts the input length in register $1$. The input-length oracle answers each query by whether its position is within the input, as guaranteed by the oracle-query calculation (`mult_queries`); the input-length loop lemma (`inputLength_loop`) therefore reaches the first pair scan with register $1=|x|$, preserving safety. The scan lemma (`mult_scan`) then parses the outer pair. If parsing fails, the input cannot belong to the multiplication language (`mult_bad_decode`), and the program returns false. If parsing succeeds, the parser reconstruction theorem (`eq_pairEncode_of_pairDecode`) identifies the input as an encoding of a first field and a tail. The scan has advanced register $0$ to the end of that first field, and its length equation follows from the pair-encoding length formula (`length_pairEncode`). The register-update bound (`register_update_le`) keeps the changed counters within the stated limit.

Next, the copy routine (`mult_copy`) saves the first field’s endpoint. The scan is repeated on the tail: failure to parse its nested pair again forces rejection by `mult_bad_decode`, while success reconstructs the nested encoding and yields $x=\operatorname{pairEncode}(a,\operatorname{pairEncode}(b,c))$. The pair-encoding length formula supplies the corresponding register bounds and offsets. With those fields prepared, the multiplication computation and its answer are supplied by `mult_prepare_run`; chaining the length loop, both scans, and the two copy routines to that run proves the claimed answer and safety throughout.

**Key facts.** `Complexity.LogProg.inputLength_loop`, `Complexity.mult_queries`, `Complexity.LogProg.register_update_le`, `Complexity.mult_scan`, `Complexity.mult_bad_decode`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Complexity.mult_copy`, `Complexity.mult_prepare_run`, `Complexity.LogProg.AReach.halt`.
