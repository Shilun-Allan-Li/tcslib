<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.parse_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing Run of the Codec Program

**Claim.** For every bit string $y$ and codec mode other than the step mode, either there is a shaped representation of $y$ with bounded parsing counters and a bounded run to the halving stage with the specified register values, or no such representation exists and the program halts false, respecting its precondition and register bound throughout.

**Proof.** 1. Begin by bounding the input length by the global register bound, using `length_le_bnd`. The first parsing phase (`parse_x`) either finds an outer decomposition $y=\langle x,r\rangle$ and reaches the first prefix-scan state, or proves that no such decomposition exists and that the program halts false. The latter case already gives the second alternative.

2. In the decomposition case, the drop identity for pair encoding (`pe_drop`) identifies the remaining suffix as $r$. The prefix-scan result (`pr_run`) either rejects when decoding that suffix fails or advances the prefix pointer past the encoded first component. If decoding fails, the decoder equation for an encoded pair (`pairDecode_pairEncode`) and injectivity (`pairEncode_inj`) show that no claimed nested representation could exist; the program's rejection yields the required false halt (`halt_rej`).

3. If decoding succeeds, write $r=\langle w,sw\rangle$ using the reconstruction property of the decoder (`eq_pairEncode_of_pairDecode`). The register values after the first scan are adjusted to the exact encoded-prefix length by the reachability register-cast fact (`Reach.cast`). A second drop calculation identifies the remaining suffix as $sw$. The scan-and-width phase (`sw_run`) either establishes that this suffix is canonical and short enough, while reaching the next counter-halving state with bounded $Q_1$ and $Cap$, or rejects.

4. In the successful branch, canonicality identifies $sw$ with the binary representation of its numerical value (`canon_eq_bits`). Set $s$ to that value. The canonicality theorem for binary representations (`canon_bits`) and the width conclusion from `sw_run` give the shape condition and its bit-length bound; the run and counter bounds are the ones supplied by that phase. Concatenating the parsing, prefix-scan, and suffix-scan runs uses reachability transitivity (`Reach.trans`).

5. In the rejection branch, the scan theorem says the suffix is not canonical or is too long. If a shaped representation with a valid width existed, pair-encoding injectivity would identify its components with $x$ and $w$, and canonicality of `Nat.bits s` (`canon_bits`) would contradict the scan's rejection condition. Chaining the earlier run with the rejection halt gives a false halt from the initial configuration (`AReach.halt`). If the initial outer parse failed, its no-decomposition conclusion directly rules out every shaped representation. This proves the stated alternatives.

**Key facts.** `Complexity.Codec.length_le_bnd`, `Complexity.Codec.parse_x`, `Complexity.Codec.pe_drop`, `Complexity.Codec.pr_run`, `Complexity.Codec.pairEncode_inj`, `Complexity.Codec.halt_rej`, `Turing.pairDecode_pairEncode`, `Turing.eq_pairEncode_of_pairDecode`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.sw_run`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.canon_bits`, `Complexity.Codec.Reach.trans`, `Complexity.LogProg.AReach.halt`, `Turing.length_pairEncode`.
