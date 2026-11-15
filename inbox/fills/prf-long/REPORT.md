# Fill `prf-long` · checkpoint 2 · D3 (cumulative: D1, D2, D3)

**Worker** Claude. **Unit** `prf-long` (ruling B3: the PRF machinery of [PS10, Theorem 99.2] at `ℓ(n)`-bit
outputs). **Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` (`cryptography/pass-shelat-ch2-4`), read
from the exchange at `b97d359517f8cebbf7e03071e30bc21e66c8403e` (pack verified: `evidence/logs/inputs-check.log`).
**Proof branch** `fill/prf-long` (local); at this checkpoint three commits over the base:

| commit | content |
|---|---|
| `94e7c1eb09f8cfd27389d5282962e3e95bdf4bcf` | checkpoint 1: D1, D2 (delivered as exchange commit `6941fe671`) |
| `200b6b502d26bfcf72215ce403f7821561a311ba` | checkpoint 2: D3 |
| `eff869dc9…` (full hash in `patches/COMMITS.tsv`) | checkpoint 2: the readers `histBlockLenOut_eq`, `adviceBoundOut_eq` (lint check 8, see *Lint*) |

This unit proves no admitted target and removes no `sorry`.

## Checkpoint 2 (brief: D3)

### D3 · `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` (572 → 890 lines, ≤ 1000)

The two machine theorems, as drafted (namespace `TCSlib.Cryptography.MultiMsg`):

```lean
theorem exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true])

theorem exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true])
```

`exists_queryChainOut_nuppt` is the base proof of `exists_queryChain_nuppt` run on the string layer below
(`postFunOut ℓ`, `maskOfOut`, `adviceBoundOut q ℓ`, `preFun_encodeHistOut`, `postFunOut_layout`); the machine
construction itself (`exists_comp`, `exists_seq`, `exists_withAdvice`, `exists_split`, `buildTree` by induction
on the remaining budget) is unchanged. `exists_oneQuery_nuppt` is a corollary, no second machine: the chain
machine for `D ∘ pairFstD` (`NUPPT.exists_comp`) with `q = const 0` and the zero mask; the one-entry tuple
`⟨⟨⟦r⟧, ⟦0 + g r⟧⟩, []⟩` is read back by `pairFstD`, the point `r` is the one-point tuple
(`Equiv.funUnique`, `finCongr`), and `D`'s coins go to the composite by `NUPPT.coinsCongr`.

**String layer at answer width `ℓ`** (new; every new `def` has its reader beside it):

| new declaration | signature (abridged) | reader / lemmas |
|---|---|---|
| `histBlockOut` | `{n l} (p : (Fin n → Bool) × (Fin l → Bool)) : List Bool` | `histBlockOut_eq`, `length_histBlockOut` (`= 4n + 2l + 6`), `pairFstD_pairFstD_histBlockOut` |
| — | — | `encodeHist_eq_flatMapOut {ℓ₁ ℓ₂}` : `encodeHist h = h.flatMap histBlockOut` |
| `histBlockLenOut` | `(ℓ : PolyExpr) : PolyExpr` (`4·var + 2·ℓ + 6`) | `histBlockLenOut_eq`, `eval_histBlockLenOut` |
| `maskBlockOut` | `{l} (n : ℕ) (w : Fin l → Bool) : List Bool` | `maskBlockOut_eq`, `length_maskBlockOut`, `zipWith_xor_histBlockOut_maskBlockOut` |
| `postCountOut`, `postOffsetOut`, `postQueryOut`, `postFunOut` | `(ℓ : PolyExpr) (z : List Bool) : List Bool` | `…Out_eq` each; `polyTimeComputable_postFunOut`, `postFunOut_layout` |
| `maskOfOut` | `{l k} (n : ℕ) (v : Fin k → Fin l → Bool) : List Bool` | `maskOfOut_eq`, `length_maskOfOut` (`= k (4n + 2l + 6)`) |
| `adviceBoundOut` | `(q ℓ : PolyExpr) : PolyExpr` | `adviceBoundOut_eq`, `eval_adviceBoundOut` |
| — | — | `preFun_encodeHistOut {n l k}` (the masked canonical history at width `l`) |

Bridges (`rfl` or `simp only` inside this owned file, as Rule 10 allows): `histBlock_eq_histBlockOut`,
`maskBlock_eq_maskBlockOut`, `maskOf_eq_maskOfOut` (all `rfl`), and `postCount_eq_postCountOut`,
`postOffset_eq_postOffsetOut`, `postQuery_eq_postQueryOut`, `postFun_eq_postFunOut` (case `ℓ = .var`; the block
lengths `6n + 6` and `4n + 2n + 6` agree by `omega` after `eval_histBlockLen`, `eval_histBlockLenOut`).

Deviations from the brief's list, disclosed:

* **`postQueryOut` added.** The brief lists `postQuery` among the width-free helpers to reuse, but `postQuery`
  reads `postOffset`, whose block length is `histBlockLen = 6n + 6`; at width `ℓ(n)` the offset must be
  `postOffsetOut ℓ`, so the query move needs its `Out` form too (with its reader and the bridge).
* **`maskBlockOut` takes `n` explicitly** (`maskBlockOut n w`): `n` occurs only in the zero prefix
  `0^{4n+4}`, so it cannot be inferred from `w : Fin l → Bool`. Likewise `maskOfOut n v`.
* `histBlockLen`, `eval_histBlockLen` and `adviceBound` are kept as they are (frozen definitions; the bridges use
  `eval_histBlockLen`). `adviceBound` is no longer used by `exists_queryChain_nuppt` (now a re-derivation), but it
  stays: deleting a base declaration is outside the frozen-statement rule.

**Re-derived** as the case `ℓ = var` / `l = n` (their sketches now say so): `length_histBlock`,
`encodeHist_eq_flatMap`, `pairFstD_pairFstD_histBlock`, `length_maskBlock`, `zipWith_xor_histBlock_maskBlock`,
`polyTimeComputable_postFun`, `length_maskOf`, `postFun_layout`, `preFun_encodeHist`, and
`exists_queryChain_nuppt := exists_queryChainOut_nuppt D q .var v` (the remaining difference is
`PolyExpr.var.eval n` against `n`, notation by Q1). Reused as they are, as the brief lists: `length_flatMap_of_length`,
`flatMap_range_blocks`, `flatMap_const_*`, `dbl_append`, `zipWith_xor_*`, `take_drop_ofFn_blocks`, `blockMapFun`,
`takePolyFun`, `dropPolyFun`, `preFun`, `postHist`, `postPoints`, `postBudget`, `postAns`, `postVerdict`,
`length_flatten_of_length`, `decodeOracleMove_query`/`_ret`, `flatMap_ofFn`. No ledger row.

**Why the chain machine is not built from the Games/Efficiency templates** (T2
`Games.exists_interactiveHandlerMachine`, T4 `exists_toOracleAdversary_of_bitCodec`, which work at any `ℓ₁`,
`ℓ₂`). `exists_queryChainOut_nuppt` keeps the existing `n`-bit construction of this file (pre-processor `preFun`,
uniform post-processor, advice, split coins) and changes only its string layer, so that `exists_queryChain_nuppt`
becomes literally its case `ℓ = var` and the file's own helpers are reused. Rebuilding it from T2/T4 would (a) add
a second construction of the same machine beside the one this file already has, the duplication this unit is
meant to remove, and (b) add an import edge from `ReductionMachine` (position 152 of `order.txt`) to
`Games/Efficiency` (position 194; it does not import `FromPRF`, so there would be no cycle, but it is not in this
file's closure today).

## Checkpoint 1 (brief: D1 and D2), delivered as `6941fe671`

### D1 · `Pseudorandom/Functions/Asymptotic/Defs.lean` (447 → 480 lines)

```lean
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q)

theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n))
```

Both as drafted. Re-derived: `prfAdv_toOracleAdversary := prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q`
(the explicit `ℓ₂ := .var` is needed: without it the elaborator must solve `PolyExpr.eval ?ℓ₂ n =?= n` and times
out) and `PRF.negligible_prfAdv := hF.pseudorandom.negligible_prfAdv D q`.

### D2 · `Encryption/PrivateKey/FromPRF/Hybrid.lean` (349 → 511 lines)

All names and signatures as drafted, in `section Concrete` with the added variable `{l : ℕ}`:
`prfEncRealOut` (+`prfEncRealOut_apply`), `otpEncOut` (+`otpEncOut_apply`), `multiMsgAdvOut`,
`eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy`, `acceptProb_oracleDist_multiMsgAdvOut`,
`prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut`, `distAdv_prfEncRealOut_le`,
and the three `rfl` bridges `prfEncReal_eq_prfEncRealOut`, `otpEnc_eq_otpEncOut`,
`multiMsgAdv_eq_multiMsgAdvOut`. Binder note: `prfEncRealOut_apply`, `eval_multiMsgAdvOut`,
`multiMsgAdvOut_boundedBy` and the bridges carry `omit [Fintype K]`/`omit [Fintype ρ]` exactly as their `n`-bit
originals do (otherwise the section's instance arguments would be included and the `n`-bit re-derivations, which
omit them, could not supply them).

**Re-derived** as the case `l = n` (through the bridges): `prfEncReal_apply`, `eval_multiMsgAdv`,
`multiMsgAdv_boundedBy`, `acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`,
`distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`, `distAdv_prfEncReal_le`; their `**Proof sketch.**`
paragraphs now say "the case `l = n` of …", and the full sketches moved to the `Out` lemmas. `chainTree`,
`uprob_not_injective_le` and `pushesUniform_comp_injective` are reused as they are (the collision bound concerns
the `n`-bit points only).

In all three files the new declarations sit before the `n`-bit ones they serve (the base declarations keep their
relative order).

## Frozen-statement check

`evidence/headers/headers-cp2.txt` (tool `evidence/tools/headers.py`): every base declaration of the seven
scope files (`Asymptotic/Defs`, `FromPRF/Hybrid`, `FromPRF/ReductionMachine`, `FromPRF/HybridLemmas`,
`FromPRF.lean`, `Pseudorandom/Functions.lean`, `Encryption/PrivateKey.lean`) is present in the same order, with
its header, its `omit … in` lines and its statement prose (the docstring before `**Proof sketch`) byte-identical,
and every `def`/`abbrev`/`structure`/`instance` byte-identical in full: **0 differences** (ReductionMachine:
44 base declarations, 82 at this checkpoint, 38 added). Control (`evidence/headers/control-cp2.txt`, files in
`control-cp2/`): one character changed in the header of `exists_queryChain_nuppt` is reported as exactly one
difference. The checkpoint-1 run and control are kept (`headers-cp1.txt`, `control-cp1.txt`).

## Checks at this checkpoint

* **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; no cgroup memory limit, headroom = MemAvailable
  ≈ 15.5 GiB; disk 11.0 GiB free at first (below the 12 GiB floor), so I removed only this session's own
  finished worktrees (`/workspace/prfbase`, `/workspace/folds`; their branches keep their commits): 14.15 GiB free.
* **Packages and cache.** `.lake/packages` is a symlink to this host's populated tree at exactly the
  manifest's pins (the addendum's alternative; the manifest at `7b307d62` is byte-identical to that tree's).
  `evidence/logs/packages-check.log`: "packages: 11 match, 0 mismatch, 4 absent". The 111 Mathlib roots
  computed from `order.txt` equal `roots.txt`; the narrowed `lake exe cache get` (111 roots) exited 0, "No
  files to download" (2,400 decompressed from the cache tool's existing store of 2,402 archives, populated by
  earlier sessions on this host: `cache-store.log`); no zero-size olean; probe `import
  Mathlib.Algebra.BigOperators.Field` passed (`cache-probe.log`).
* **Bootstrap** (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`): 434/434 exit 0, 0 error
  diagnostics with `^\S+\.lean:\d+:\d+: error[:(]` (`evidence/base/bootstrap-errors.txt`). Its history
  (`bootstrap-run.log`): the first background loop ran `sweep.py` without `-I` for 8 modules and was restarted
  with `python3 -I`; I paused it after 176 modules to try the edits, then restored the base sources and rebuilt
  every module from position 149 (the first owned module) at the base before finishing (first-pass rows in
  `bootstrap-pass1.tsv`).
* **Base sorry census** (`evidence/base/sorry-census-base.txt`): 40 declarations in 19 modules, equal to
  `base-sorries.txt`.
* **Checkpoint sweep** (`evidence/cp2/`): every module of `order.txt` from position 149 (`Asymptotic/Defs`, the
  first owned module) to the end (`order-cp2.txt`, 286 modules), at commit `eff869dc9` (the 148 modules before
  it import nothing that changed and were checked in the bootstrap): **286/286 exit 0, 0 error diagnostics**
  (`sweep-errors.txt`, rows `sweep.tsv`, raw logs `sweep/`, run log `sweep-run.log`). Sorry census over all 434
  modules (checkpoint logs first, bootstrap logs for the first 148): `sorry-census-cp2.txt`, **identical** to the
  base census (40 declarations in 19 modules).
  A first cp2 run, at `200b6b502`, was stopped by me after 7 modules (all exit 0) when the lint showed the two
  missing readers; its rows and logs are kept in `evidence/cp2/aborted/`, and the sweep above was restarted from
  position 149 after the reader commit. The checkpoint-1 sweep (286/286, 0 errors, census identical) is kept in
  `evidence/cp1/`.
* **Axioms at this checkpoint** (`evidence/axioms/axioms-cp2.log`, tool `axioms.py`): all 278 stored
  constants of `Asymptotic/Defs`, `FromPRF/Hybrid` and `FromPRF/ReductionMachine` depend on at most `propext`,
  `Classical.choice`, `Quot.sound`; the five endpoints of the brief: `[Classical.choice, Quot.sound, propext]`,
  as at the base (`axioms-base.log`). Of the base constants of these modules that are still stored, one has a
  **different** (still standard) list, disclosed: the re-derived `MultiMsg.encodeHist_eq_flatMap` went from
  `[propext]` to `[Quot.sound, propext]`, because its new proof passes the bridge under `List.flatMap` with
  `funext`. I will restore `[propext]` in the final (the term `encodeHist_eq_flatMapOut h` checks against the
  `n`-bit statement by unfolding `histBlock`, the bridge being `rfl`); the final sweep covers that change.
  At checkpoint 1 (`axioms-cp1.log`): 152 constants of `Asymptotic/Defs` and `FromPRF/Hybrid`, all standard, the
  base ones unchanged. Disclosed: two **auto-generated** equation lemmas, `multiMsgAdv.eq_1` and `otpEnc.eq_1`,
  were stored in `Hybrid`'s olean at the base only because the base proofs unfolded these definitions with
  `rw [multiMsgAdv, …]`/`simp only [otpEnc, …]`; the re-derived proofs go through the `rfl` bridges instead,
  so the lemmas are no longer realized there. They are not source declarations, nothing names them, and any
  later `rw`/`simp`/`unfold` realizes them on demand (the sweeps are clean). For the same reason checkpoint 2
  no longer stores, in `ReductionMachine`, the equation lemmas `histBlock.eq_1`, `maskBlock.eq_1`, `maskOf.eq_1`,
  `adviceBound.eq_1` and the compiler-generated auxiliaries of the replaced proofs
  (`encodeHist_eq_flatMap.match_1_1` and eight `_proof_…`/`_simp_…` constants of `exists_queryChain_nuppt`,
  `length_histBlock`, `length_maskBlock`, `postFun_layout`, `zipWith_xor_histBlock_maskBlock`); the full list
  is the difference of the two logs. None is a source declaration.
* **Width and size** (`evidence/checks/widths-cp2.txt`): no new line over 100 characters in the three changed
  files; the over-long lines listed there are byte-identical base lines (frozen text). Files ≤ 1000 lines
  (ReductionMachine 890).
* **Sketches** (`evidence/checks/sketches-cp2.txt`): every proof of 15 lines or more has a sketch;
  `exists_queryChainOut_nuppt` keeps the base proof's step comments and `exists_oneQuery_nuppt` has its own.
* **Lint** (`evidence/lint/`): base 92 FAIL / 101 WARN, checkpoint 92 / 101 (`lint-cp2.txt`). Line-set diff
  (`lintdiff-cp2.txt`): no new FAIL; two WARN lines **changed**, both check-8 lines of owned files, both
  shortened by bridges named after listed definitions (the effect the brief anticipates):
  * `Hybrid.lean`: "2 … chainTree, otpEnc" → "1 … chainTree" (bridge `otpEnc_eq_otpEncOut`);
  * `ReductionMachine.lean`: 16 → 10 definitions; `histBlock`, `maskBlock`, `maskOf`, `postCount`,
    `postOffset`, `postQuery` drop out (bridges `histBlock_eq_histBlockOut`, …, `postQuery_eq_postQueryOut`).
    The remaining ten are the base list minus those six; **no new definition is listed**. Before the reader
    commit the line also listed the new `histBlockLenOut` and `adviceBoundOut` (whose `eval_…` lemmas the
    heuristic does not count), which is why `histBlockLenOut_eq` and `adviceBoundOut_eq` were added.
* **Seals, controls, unfold scan**: base runs done (`evidence/seals/base/`, `evidence/base/rwids/`); the final
  runs come with the final delivery.

## Overlap and reuse (checkpoints 1 and 2)

| New declaration | Nearest relative | Relation |
|---|---|---|
| `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Asymptotic/Defs.lean` `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` | generalization to `ℓ₂`; the originals are **re-derived** from them. `SecureComputation/SpecialEncryptionSecurity.lean` `prfOut_var_iff` (DL-8) relates `PRFOut .var` to `PRF`; the new lemma takes `PRFOut`'s clause (2) as its hypothesis, as the brief requires (no import of `SecureComputation`). |
| `prfEncRealOut`, `otpEncOut`, `multiMsgAdvOut` and their lemmas | `FromPRF/Hybrid.lean` the `n`-bit originals | generalization to `l`; every listed original is **re-derived** (no ledger row). |
| `distAdv_prfEncRealOut_random_otp_le` | `Hybrid.lean` `distAdv_prfEncReal_random_otp_le`; `HardcoreBit.pushesUniform_restrict` (DL-2) via `pushesUniform_comp_injective` | reuses `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` as they are. |
| `acceptProb_otpEncOut` | `Hybrid.lean` `acceptProb_otpEnc`; `zipWith_xor_ofFn_add` (DL-2) | same Boolean-group relabelling; the original is re-derived. |
| `exists_queryChainOut_nuppt` | `ReductionMachine.lean` `exists_queryChain_nuppt`; Games/Efficiency T2/T4 | generalization to `ℓ`; the original is **re-derived**; not built from T2/T4 (see D3 above). |
| `exists_oneQuery_nuppt` | `exists_queryChainOut_nuppt` | its case `q = 0` with the zero mask and `D ∘ pairFstD`; no second machine, as the brief asks. |
| (width handling of all `Out` machine lemmas) | `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean:348`), `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean:228`) | those transport an oracle adversary's evaluation along a propositional width equality `ℓ' = ℓ` by `padFin`. The `Out` lemmas need no transport: the width `ℓ.eval n` is in their types, and the `n`-bit cases are taken at `ℓ = var`, where `PolyExpr.var.eval n` and `n` agree definitionally (Q1). Neither lemma is used or duplicated. |
| `histBlockOut`, `maskBlockOut`, `maskOfOut`, `postCountOut`/`postOffsetOut`/`postQueryOut`/`postFunOut`, `histBlockLenOut`, `adviceBoundOut` and lemmas | the `n`-bit string layer of `ReductionMachine.lean`; `NMSim.chunkMap`, `polyTimeComputable_blockMap` | generalization to `l`/`ℓ`; the `n`-bit lemmas are re-derived through bridges. The block maps reuse this file's `blockMapFun`/`polyTimeComputable_blockMapFun` (as the `n`-bit code does) rather than `NMSim.chunkMap`, which `ReductionMachine` does not import. |
| (reused) `take_drop_ofFn_blocks` | `EnsembleLemmas.take_drop_ofFn_blocks` (DL-9) | unchanged twin, used as before; DL-9 stays with the ledger. |
| (reused) `zipWith_xor_*` | the private `zipWith_xor_xor_self` copies (DL-40) | no new copy added. |

Searches: `evidence/overlap/dupsearch-base.log` (`evidence/tools/dupsearch.sh` on the issue base).

## Scope requests

None.

## Next

Final: D4 (`FromPRF/MultiMsgOut.lean`: `encodeTupleOut`, `MultiMsg.encodeList_eq_flatMap`,
`encodeTupleOut_eq_flatten`, `MultiMsg.exists_negligible_distAdv_prfEncRealOut`), the re-derivations of
`encodeTuple_eq_flatten` and `prfScheme_multiMessageSecure` in `FromPRF.lean`, the facade lines, the B1 consumer
map, the full sweep and the final evidence (axioms, seals with controls, unfold scan, lint, headers). All of it
already compiles locally.

## Patches and reproduction

`patches/000N-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer set from `COMMITS.tsv`, and reproduces every hash and the tree
(`evidence/amcheck/amcheck-cp2.log`; the checkpoint-1 log is kept).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, sources of probes and seals, tools); the
top-level `SHA256SUMS` covers every delivered file except itself; both checked against the delivered paths.
