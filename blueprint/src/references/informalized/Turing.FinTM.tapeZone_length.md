<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.tapeZone_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a zone

**Claim.** The zone of $n$ blocks, each encoding $k$ work tapes, has length $nk$.

**Proof.** Induct on the number $n$ of blocks, allowing the starting coordinate to vary. For zero blocks the zone is empty, with length $0=0\cdot k$. In the successor case, the zone is the first row concatenated with the zone of the remaining $n$ blocks. The first row has length $k$ by the single-block length result (`Turing.FinTM.tapeRow_length`), and the induction hypothesis gives length $nk$ for the rest. Thus the total length is $k+nk=(n+1)k$.

**Key facts.** `Turing.FinTM.tapeRow_length`.
