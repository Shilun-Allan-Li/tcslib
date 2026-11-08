<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.Cfg.embedOracle_workTapeSymbols -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbols Under Embedding

**Claim.** For any configuration $c$ of a machine with $k$ work tapes and any work-tape index $i$, the optional symbol under tape $i$'s head in the embedded configuration equals the optional symbol under tape $i$'s head in $c$.

**Proof.** By definition, the symbol scanned on tape $i$ is the tape content at that tape's head position. The embedding preserves the content of each work tape and the corresponding head position; evaluating the embedded tape at its embedded head therefore gives the original tape content at its original head.
