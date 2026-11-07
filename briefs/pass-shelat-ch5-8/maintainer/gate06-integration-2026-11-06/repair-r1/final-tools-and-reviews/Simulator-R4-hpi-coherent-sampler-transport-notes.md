# Simulator R4: coherent dependent sampler transport in hπ

One unapplied follow-up for the existing `hπ` block inside `attemptAt_poly`, current source 310–318. It replaces only the dimension-rewriting simplifier and its closing `all_goals rfl`.

- Current source: `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean`.
- Required current source SHA256: `0ad712e26071f91a0bcce913d287e9c3c26b66bf8be7650a15b22d63813d5ed4`.
- Proposed full source SHA256 (memory only): `c71b97692b83cbcda650bc5b3d27f5762b40a8784db209d5872823c41784c1a5`.
- Patch SHA256: `ae62cd49d6ce04a551d182de0f95adc8a0fb313a788ed2ce93b9fdbd5d3becce`.
- Current graph-decoder owner SHA256: `a2a354fd0a89b117022922f416b431a26393b207dbf65e72c4f9a6e3c4247ddc`.
- Current public sampler owner SHA256: `c37dd3e13e4cd00afa895e9dd78d193f4dee2e59f8913add41d025f37f861302`.

## Exact hidden argument

R4 old-collector diagnostic log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/diagnostic-evidence/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R4_Simulator/native/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R4_Simulator.log`
SHA256 `e051b365ea9e7b64524d50a017788452ed8cfb8bb0f7cdda99ec4d53ad6da818`.

The validated diagnostic reports five source errors, with hπ at source 318/probe 368. The displayed residual sides hide the essential difference: the RHS `Option.getD` default `1` retains an `OfNat`/`One` instance indexed by `Fin ((decGraph graphWord).fst)`, while the visibly rewritten permutation arguments and the LHS default use `Fin (Nat.sqrt graphWord.length)`. The closing `rfl` would require the sealed foreign decoder to compute.

Root's PP-only log confirms the hidden instance at lines 1134–1231 and 1389–1499:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/repair-r1/debug-native/PP-only-R4-Simulator.log`
SHA256 `9b6752c4864955f1c0bf69e1b55d8b09befa0585de97a843d40f356d26eea2a6`.

No unverified `simp +instances` or nonexistent configuration is used.

## One-block term route

Keep the existing public composition/pair projections. Before rewriting any dependent dimensions, name the already-existing graph word and permutation tape as local data lets.

1. Apply `congrArg` to the first projection of the full public Sigma reader `decGraph_eq graphWord`, then compose with `instanceVertexCount_eq.symm`. This gives `hcount : (decGraph graphWord).1 = instanceVertexCount x` without reading the decoder body.
2. Use `congrArg encPerm` on `(samplePerm_eq nDec tape).symm` to fold the complete existing `permFromCoins ... |>.getD 1` value back into `samplePerm nDec tape`. Its option, default identity, and hidden instance retain their coherent original index throughout this step.
3. Apply `congrArg (fun k : ℕ => encPerm (samplePerm k tape)) hcount`. The whole family is List-valued, so transporting its numeric parameter carries all dependent permutation/default details together.

The two equality proofs are composed directly as a term. There is no tactic rewrite that could close prematurely on an unsealed native check before a later tactic, no dependent simplifier rewrite inside the default instance, and no body unfolding of foreign `decGraph`, `samplePerm`, permutation sampling, or encoding definitions.

The only new names are local data aliases and a local equality. They introduce no algorithm, host, public/private helper definition, assumption, or new tactic block. The public reader signatures were inspected in the current sources (`Encoding.lean:135`, `GraphIsomorphism.lean:231,360`). The existing hπ and enclosing theorem headers, all parameters/security premises, algorithms/data, and admissions are unchanged.

## Remaining errors and verification limits

The other four R4 source errors at 167, 186, 450, and 469 are untouched; no additional proof block is proposed here. Old-row diagnostic validity does not establish final dynamic coverage.

Static comparison pins the exact current source, preserves every byte outside this one block, and leaves its `by`-block and admission counts unchanged. Current source bytes were rechecked before saving the artifacts. No library/Git/evidence/native-object mutation, Lean/cache/build command, or computer app occurred. This follow-up remains uncompiled; root must run the ordinary and sealed checks serially and inspect their exact source hashes.

**Ready to run**
