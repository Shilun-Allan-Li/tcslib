# Complete Bob program worker handoff

Worker `/root/evaluation` proved `YaoHybridProof.BobProgram.output_poly` in the new
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobProgram.lean` (146 lines).
The six prior helpers and immutable v1 evidence remain unchanged.

The theorem composes the generic description decoder, initial-key machine, raw table
selector, garbled-evaluation host, and output reader. Its only semantic interface
hypotheses are the canonical description equation, valid output vertices, encoded
initial-key equation and length, the current-table equation, and the decoded-pair
list equation. The common-input, message and answer selectors are arbitrary total
polynomial-time word functions. No Yao definition is imported or copied. The conclusion
is the explicit output-comparison vector after library `runWith`/`evalGate`.

## Reuse and overlap

Reuse searches are in `reuse-search.log`. The proof directly uses:

- `DescriptionDecoder.readCircuit_encode` and its polynomial-time decoder;
- `BobInit.initWords_poly` through the supplied initial-key reader equation;
- `BobTables.tableSelector_poly`/`tableSelector_host` for the exact table reconstruction;
- `garbledRunWith_poly`, including its already proved time/state envelopes;
- `BobIO.outputWord_poly`/`outputWord_layout` for the final vector;
- `DAGCircuit.size_eq`, `length_runWith`, and the initial-length reader for output validity;
- `polyTimeComputable_reencodeWords` for arbitrary decoding-pair messages.

No probability, list, encoding, traversal or machine lemma is rederived. The word-level
composition is the new complete consumer contract; it defines no copied semantic object.
There is no new host promotion or frozen-file change in this task.

## Verification

`bobprogram-02.log` passes with no diagnostics. `bobprogram-01.log` is the preserved
missing-prerequisite environment result: no declaration elaborated because the initial
seed omitted `ChunkScanner.olean`; the lead supplied the complete closure before retry.
All four whole-file A/B strict/coe seals pass with `-DmaxErrors=0` over the full imported
TCSlib closure. The file is absent at the issue base. The existing seal-generator paired
controls from immutable evidence `b/` apply unchanged: the preamble is identical and only
the evidence output path differs.

The original batch was interrupted during its terminal trace at the user's explicit pause;
all four seals had completed. Its partial raw log and exact source snapshot are retained.
After explicit resume, the absent old process handle and lead process check were verified;
only the terminal trace was rerun. The completed trace prints the sole stored constant's
signature, standard axioms, and an empty transitive sorry closure.

Every Lean command uses the shared three-slot wrapper, tag `sc-yao-b`, with the private
`.lake/sc-yao-oleans` tree. No child commit or delivery push was made.
