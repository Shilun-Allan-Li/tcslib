# Subagent c: complete tape-to-seed bridge

Source: `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinSeedRelabel.lean`. Namespace `...YaoHybridProof.CoinSeedRelabel`.
399 lines,29 source declarations,49 stored constants, width<=100. No sorry.

## Contract

`assignmentEmbedding` embeds every assignment of arity<=2 in Fin4 by its binary
fold. `assignmentPerm` reuses Mathlib's finite-embedding permutation extension
to extend XOR. `assignmentPerm_unused` fixes every code>=2^arity, hence codes
1/2/3 for arity0 and2/3 for arity1. `keyMask`, `rowPerm`, `shiftMask` are padded
by false/identity outside real vertices, gates and arguments. Exact readers and
explicit unused-coordinate preservation contracts are included.

The three relabel_getD lemmas identify exact key, nonce and shift offsets.
`seed_relabel` takes a seed function and four coordinate-reader hypotheses
(keys, first nonce half, second nonce half, permutation bits), not a copied
sampler definition. It proves that applying that seed to the relabeled tape
is exactly RelabelGarbling.relabelSeed applied to the original seed. It
requires C.size<=S and each gate arity<=2, with no positive-width assumption.
The public tape permutation is CoinRelabel.relabel S n (keyMask...)
(rowPerm...) (shiftMask...). No probability machinery is re-proved.

## Search, reuse and overlap disclosure

RowFromCoins.assignmentFold_eq_two is reused directly for the fold's first-two
bit formula. Bool.toNat bounds and List's public ofFn/getD readers recover
the bits for injectivity; Mathlib viaFintypeEmbedding and its image/non-image
readers extend the existing xorPerm. RelabelGarbling readers and CoinRelabel
exact offset readers are reused; no foreign TCSlib definition is unfolded.

SY-5: nearest unmerged sc-garble a73072f1 result is Garbling/CoinBlocks.lean
assignmentFold_small (line38), giving the same arity<=2 code bound and
injectivity via finite arity case analysis. This is a general re-derivation
of that encoding fact, now using agent-a's public two-bit equation and digit
bounds; the finite permutation extension, padded masks and sampler equality
are new consumers. The earlier CoinRelabel evidence preserves the consulted
CoinBlocks source. No unmerged helper is imported.

## Verification

CoinSeedRelabel-11 normal check PASS, zero errors. Subsequent source-only
formatting split two long lines; all four whole-file strict/coe by eval A/B
seals of that formatted source PASS with -DmaxErrors=0. Axioms-01 PASS prints
all29 source declarations and enumerates all49 stored constants, with
standard axioms only and every transitive closure sorried=[]. Both error
forms are counted in results.jsonl and seals/results.jsonl. Original failed
probes/source versions are preserved. Seal runners follow the earlier
sc-garble-derived c/relabel tools, copied with only evidence path changes;
provenance is retained in c/relabel and the original c scripts.

No controls or style-lint run was started before the user's relocation pause.
The lead must run final merged checks. No commits by this agent.
