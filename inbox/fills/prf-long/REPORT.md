# Fill `prf-long` · final (D1–D4, B1 consumer map)

**Worker** Claude. **Unit** `prf-long` (ruling B3: the PRF machinery of [PS10, Theorem 99.2] at `ℓ(n)`-bit
outputs). **Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` (`cryptography/pass-shelat-ch2-4`), read
from the exchange at `b97d359517f8cebbf7e03071e30bc21e66c8403e` (pack verified 7/7 and SOURCE 434/434:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/prf-long` (local), four commits over the base:

| commit | content | exchange |
|---|---|---|
| `94e7c1eb09f8cfd27389d5282962e3e95bdf4bcf` | checkpoint 1: D1, D2 | `6941fe671` |
| `200b6b502d26bfcf72215ce403f7821561a311ba` | checkpoint 2: D3 | `360670852` |
| `eff869dc9e20b37b5252f9681b616d8b74d7d4d5` | checkpoint 2: readers `histBlockLenOut_eq`, `adviceBoundOut_eq` | `360670852` |
| `40127c58490da57b824f9c4f8a384d7395b06dcb` | final: D4, the `FromPRF.lean` re-derivations, facade lines; `encodeHist_eq_flatMap` proof | this delivery |

This unit proves **no admitted target and removes no `sorry`** (census unchanged, below). Nothing of #311/#312
is imported or depended on.

## Files

| file | base lines | final lines | change |
|---|---|---|---|
| `Pseudorandom/Functions/Asymptotic/Defs.lean` | 447 | 480 | D1: 2 declarations added, 2 re-derived |
| `Encryption/PrivateKey/FromPRF/Hybrid.lean` | 349 | 511 | D2: 15 added, 8 re-derived |
| `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 572 | 889 | D3: 38 added, 10 re-derived |
| `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (**new**) | — | 163 | D4: 5 declarations |
| `Encryption/PrivateKey/FromPRF.lean` | 424 | 372 | 1 added (bridge), 2 re-derived; import + docstring lines |
| `Encryption/PrivateKey.lean` (facade) | 75 | 77 | one import, one Contents bullet |

Not changed: `FromPRF/HybridLemmas.lean`, `Pseudorandom/Functions.lean` (no module was added there). All files
≤ 1000 lines; no new line over 100 characters (`evidence/checks/widths-final.txt`).

## New declarations

The full headers of all **61** new declarations, in file order, are in `evidence/final/new-decls.txt` (tool
`newdecls.py`). The main statements (namespaces `TCSlib.Cryptography`, `….MultiMsg`):

```lean
-- D1 (Asymptotic/Defs.lean)
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

-- D2 (FromPRF/Hybrid.lean, section Concrete: {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ] {l : ℕ})
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool))
def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool))
def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool)
-- readers prfEncRealOut_apply, otpEncOut_apply, eval_multiMsgAdvOut, multiMsgAdvOut_boundedBy;
-- acceptProb_oracleDist_multiMsgAdvOut, prfAdv_multiMsgAdvOut, distAdv_prfEncRealOut_random_otp_le,
-- acceptProb_otpEncOut, and:
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n)
-- rfl bridges prfEncReal_eq_prfEncRealOut, otpEnc_eq_otpEncOut, multiMsgAdv_eq_multiMsgAdvOut

-- D3 (FromPRF/ReductionMachine.lean)
theorem MultiMsg.exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true])
theorem MultiMsg.exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true])
-- string layer: histBlockOut, maskBlockOut (n explicit), maskOfOut (n explicit), histBlockLenOut,
-- postCountOut, postOffsetOut, postQueryOut, postFunOut, adviceBoundOut, each with its `_eq`
-- reader; length_histBlockOut, encodeHist_eq_flatMapOut, eval_histBlockLenOut,
-- pairFstD_pairFstD_histBlockOut, length_maskBlockOut, zipWith_xor_histBlockOut_maskBlockOut,
-- polyTimeComputable_postFunOut, length_maskOfOut, eval_adviceBoundOut, postFunOut_layout,
-- preFun_encodeHistOut; bridges histBlock_eq_histBlockOut, maskBlock_eq_maskBlockOut,
-- maskOf_eq_maskOfOut (rfl), postCount/postOffset/postQuery/postFun_eq_…Out (case ℓ = var)

-- D4 (FromPRF/MultiMsgOut.lean, new)
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) : List Bool
theorem encodeTupleOut_eq … -- the defining equation
theorem MultiMsg.encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
theorem encodeTupleOut_eq_flatten {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten
theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n

-- FromPRF.lean
theorem encodeTuple_eq_encodeTupleOut {n q : ℕ}
    (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : encodeTuple v = encodeTupleOut v
```

All D1–D4 statements are **as drafted** in the brief. Disclosed deviations from the brief's lists:

* **`postQueryOut` added** (D3). The brief lists `postQuery` among the width-free helpers, but `postQuery` reads
  `postOffset`, whose block length is `histBlockLen = 6n + 6`; at width `ℓ(n)` the offset is `postOffsetOut ℓ`,
  so the query move needs its `Out` form (with reader and bridge).
* **`maskBlockOut n w`, `maskOfOut n v` take `n` explicitly**: `n` occurs only in the zero prefix `0^{4n+4}` and
  cannot be inferred from `w : Fin l → Bool`.
* **Two extra readers** `histBlockLenOut_eq`, `adviceBoundOut_eq` (the drafted names would have left the new
  `PolyExpr` definitions without a check-8 reader; see *Lint*).
* **Binder note (D2).** `prfEncRealOut_apply`, `eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy` and the bridges
  carry `omit [Fintype K]`/`omit [Fintype ρ]` exactly as their `n`-bit originals do.
* **D1 re-derivation** needs the explicit `(ℓ₂ := .var)`; without it the elaborator must solve
  `PolyExpr.eval ?ℓ₂ n =?= n` and times out.
* `encodeTuple_eq_encodeTupleOut` is proved by `rw [encodeTuple, encodeTupleOut_eq]`: `encodeTuple` is
  `FromPRF.lean`'s own definition, `encodeTupleOut` (foreign, new module) is read through its reader.

## Re-derivations

Every `n`-bit declaration the brief lists is **re-derived** from its `Out` form as the case `l = n` / `ℓ = var`
/ `ℓ₂ = var`; its `**Proof sketch.**` paragraph now says so (statements and headers byte-identical, see
*Frozen-statement check*). The complete per-declaration list with the new proof text is
`evidence/final/rederivations.txt` (tool `rederiv.py`: 22 `CHANGED`, 96 `same`; the tool skips the one `inductive`, `OracleMove`, which the header check
finds byte-identical).

| file | re-derived (new proof) |
|---|---|
| `Asymptotic/Defs` | `prfAdv_toOracleAdversary := prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q`; `PRF.negligible_prfAdv := hF.pseudorandom.negligible_prfAdv D q` |
| `Hybrid` | `prfEncReal_apply`, `eval_multiMsgAdv`, `multiMsgAdv_boundedBy`, `acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`, `distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`, `distAdv_prfEncReal_le` (each: rewrite by the bridges, `exact` the `Out` lemma) |
| `ReductionMachine` | `length_histBlock`, `encodeHist_eq_flatMap` (the term `encodeHist_eq_flatMapOut h`), `pairFstD_pairFstD_histBlock`, `length_maskBlock`, `zipWith_xor_histBlock_maskBlock`, `polyTimeComputable_postFun`, `length_maskOf`, `postFun_layout`, `preFun_encodeHist`, `exists_queryChain_nuppt := exists_queryChainOut_nuppt D q .var v` |
| `FromPRF.lean` | `encodeTuple_eq_flatten` (bridge + `encodeTupleOut_eq_flatten`); `prfScheme_multiMessageSecure` (from `MultiMsg.exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q` through `prfScheme_multiEncDist`, the bridges and `acceptProb_comp_equiv`) |

Kept as they are, by design (reused, as the brief lists): `chainTree`, `uprob_not_injective_le`,
`pushesUniform_comp_injective`; the width-free string helpers (`length_flatMap_of_length`, `flatMap_range_blocks`,
`flatMap_const_*`, `dbl_append`, `zipWith_xor_*`, `take_drop_ofFn_blocks`, `blockMapFun`, `takePolyFun`,
`dropPolyFun`, `preFun`, `postHist`, `postPoints`, `postBudget`, `postAns`, `postVerdict`,
`length_flatten_of_length`, `decodeOracleMove_query`/`_ret`, `flatMap_ofFn`). The frozen `n`-bit
**definitions** keep their bodies (the rule); each has a bridge to its `Out` form: `rfl` for `prfEncReal`,
`otpEnc`, `multiMsgAdv`, `histBlock`, `maskBlock`, `maskOf`, `encodeTuple`; by `simp only`/`rw` at `ℓ = var` for
`postCount`, `postOffset`, `postQuery`, `postFun` (block lengths `6n + 6 = 4n + 2n + 6`).

Ledger rows (nothing kept because a re-derivation was too invasive; these are the residues the maintainer may
want on the duplication ledger):

| declaration | status | reason |
|---|---|---|
| `MultiMsg.histBlockLen`, `eval_histBlockLen` (`ReductionMachine.lean`) | **ledger**: kept beside `histBlockLenOut`/`eval_histBlockLenOut` | frozen definition `6·var + 6`; `histBlockLenOut .var = 4·var + 2·var + 6` is a different `PolyExpr` term (equal after `eval`), so no `rfl` bridge; still used by the frozen `postCount`/`postOffset` and by their bridges |
| `MultiMsg.adviceBound` (`ReductionMachine.lean`) | **ledger**: kept, now **unused** | frozen definition; its only consumer was the base proof of `exists_queryChain_nuppt`, now a re-derivation (which uses `adviceBoundOut .var`); deleting a base declaration is outside the frozen-statement rule. No other use in TCSlib |
| private `encodeList_eq_flatMap` (`FromPRF.lean`) | **ledger**: kept, now **unused**, as the brief instructs ("leave the private copy in place") | its general public form is `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`) |
| `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`, new) | **ledger**: a third copy of the statement of the public `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`) | reusing it would put `BlockEncryptor` in `FromPRF.lean`'s closure, where the frozen private copy then fails to declare (clash probe); see *Overlap and reuse* and *Promotion requests* |

## B1 consumer map

This unit does **not** prove B1. The statement was read at the PR head
`46b780dc1b286f59da18e2d10f188b0faaab8088` (`stmt/pass-shelat-b1-multimsg`, file
`SecureComputation/SpecialEncryptionMulti.lean`, not imported and not depended on):

```lean
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G
```

`hG.pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) G).Indist (OracleEnsemble.random .var ℓ)`
(clause (2) of `PRFOut`, `SpecialEncryptionSecurity.lean:56`) is literally the hypothesis `hF` of
`OracleEnsemble.Indist.negligible_prfAdv` and of `MultiMsg.exists_negligible_distAdv_prfEncRealOut`, with
`F := G`; no conversion is needed. `PRFOut` is at the issue base, so this is checked: probe
`scratch-src/probe/B1Probe.lean` (log `evidence/final/b1-probe.log`: exit 0, no diagnostics) applies
`MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` (step 3) and
`hG.pseudorandom.negligible_prfAdv B (q.add (.const 1))` (step 1) to `hG : SecureComputation.PRFOut ℓ G`, and
`exists_oneQuery_nuppt` with `hG'.pseudorandom.negligible_prfAdv B (.const 1)` to the hypothesis of
`spDecStr_wrongKey`. The B1 file itself (#311) is not elaborated here.

How each step of the B1 sketch uses the delivered lemmas, with the final names:

0. **Reduction to tuples (`sc-garble`, not part of this unit).** For slices `(o_i, ℓ_i)` and messages `m_i` the
   consumer forms the masks `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i} : Fin (ℓ.eval n) → Bool` and shows
   that, up to the coin relabelling (`acceptProb_comp_equiv`), `sliceMultiEncDist G n q o len m` is
   `P_{o,ℓ} ∘ encodeTupleOut ∘ prfEncRealOut (G n) w`, reading `encodeTupleOut` only through
   `encodeTupleOut_eq`/`encodeTupleOut_eq_flatten` and `prfEncRealOut` only through `prfEncRealOut_apply`
   (Rule 10: the new module and `Hybrid` are foreign to `SecureComputation`). `D' = D ∘ P` with the maximizing
   slices as advice comes from `NUPPT.exists_comp`, `NUPPT.exists_withAdvice` and a block parser.
1. **PRF step.** Inside `MultiMsg.exists_negligible_distAdv_prfEncRealOut` (the consumer does not repeat it):
   the two machines `MultiMsg.exists_queryChainOut_nuppt D' q ℓ (μ n).1/.2`, identified with
   `multiMsgAdvOut w (D' ∘ encodeTupleOut)` by `MultiMsg.prfAdv_congr_equiv`, `eval_multiMsgAdvOut`,
   `encodeTupleOut_eq_flatten`; the hybrid bound `distAdv_prfEncRealOut_le` (whose PRF terms are
   `prfAdv_multiMsgAdvOut`); negligibility by `OracleEnsemble.Indist.negligible_prfAdv hG.pseudorandom B_b
   (.add q (.const 1))`.
2. **Random function and collision.** Inside `distAdv_prfEncRealOut_le`: `distAdv_prfEncRealOut_random_otp_le`
   (collision bound `C(q+1, 2) / 2^n` via `uprob_not_injective_le` on the `n`-bit points) and
   `acceptProb_otpEncOut` (the full `ℓ(n)`-bit pads are uniform, so every window of them is too: the
   consumer's `P` is applied after the bound, inside `D'`).
3. **Total.** `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` gives one negligible `ε`
   with `distAdv (encodeTupleOut ∘ prfEncRealOut (G n) w) (encodeTupleOut ∘ prfEncRealOut (G n) w')
   (D'.distinguisherL n) ≤ ε n` for **all** `n, w, w'`; since `ε` precedes the masks, the consumer's maximization
   over the finitely many fitting slices and message pairs (step 0, hard-wired in `D'`) gives B1's `ε`.
   `MultiMsg.negligible_choose_div_two_pow` is inside the total.

`spDecStr_wrongKey` (`SpecialEncryptionSecurity.lean:127`, hypothesis `hG' : PRFOut (.add .var ℓ) G'`): the
distinguisher samples `k'` (its own coins) and the point `r`, makes one query and compares the first `n` bits
of the answer with `E'(⟨k', r⟩)`; `exists_oneQuery_nuppt D (.add .var ℓ)` turns such a `D` (reading
`⟨⟦r⟧, ⟦g r⟧⟩`) into a one-query oracle machine with coins `(r, c)`, and
`OracleEnsemble.Indist.negligible_prfAdv hG'.pseudorandom B (.const 1)` makes its PRF advantage negligible
(`(PolyExpr.const 1).eval n = 1` by `PolyExpr.eval_const`). The random-function probability `2^{-n}` is the
consumer's.

`specialScheme_multiMessageSecure` follows from B1 by `specialScheme_multiMessageSecure_of_joint` (PR #311); it
uses nothing of this unit directly.

Gaps this unit leaves to `sc-garble` (as the brief assigns): step 0 (the slice post-processing `P`, the mask
construction and the fit `o_i + n + ℓ_i ≤ ℓ(n)`), the random-function probability of `spDecStr_wrongKey`.

## Edge cases (brief: *Check the edge cases*)

The generic statements carry **no side condition** on `n`, `ℓ` or `q`. `evidence/final/edge-cases.log` (probe
`scratch-src/probe/EdgeCases.lean`, run against the final olean tree: exit 0, no diagnostics) instantiates them:

* `ℓ(n) = 0`: `length_histBlockOut` at `l = 0` gives `4n + 6`; `exists_queryChainOut_nuppt` at `ℓ = const 0`.
* `n = 0`: `distAdv_prfEncRealOut_random_otp_le (n := 0)` simplifies to `≤ C(q+1, 2)`.
* `q(n) = 0`: `distAdv_prfEncRealOut_random_otp_le (q := 0)` simplifies to `≤ 0`.
* Budget `1` against `(PolyExpr.const 0).eval n + 1`: `exists_oneQuery_nuppt` states the literal `1` (the proof
  transports along `1 = (const 0).eval n + 1`); `hF.negligible_prfAdv B (.const 1)` reads as budget `1` after
  `PolyExpr.eval_const`.
* Malformed moves and the budget timeout: `exists_queryChainOut_nuppt` is an equality of `eval` for every
  oracle `g`; on the canonical history the post-processor emits a well-formed query `⟨[false], ρ_k⟩` for
  `k ≤ q(n)` (`decodeOracleMove_query`) and the verdict `[true, b]` at `k = q(n) + 1` (`decodeOracleMove_ret`),
  so neither the malformed-move nor the forced-`false` branch of `buildTree` is reached; this is proved, not
  assumed (`hquery`, `hret`, `main`).
* Block lengths `0 < 4n + 2ℓ(n) + 6` (`hpos` in `postFunOut_layout`; probe on `eval_histBlockLenOut`).
* The bridges at `l = n` and `ℓ = var` (probe: `encodeTuple_eq_encodeTupleOut`, `postFun_eq_postFunOut`).

## Frozen-statement check

`evidence/headers/headers-final.txt` (tool `evidence/tools/headers.py`): every base declaration of the seven
scope files (`Asymptotic/Defs`, `FromPRF/Hybrid`, `FromPRF/ReductionMachine`, `FromPRF/HybridLemmas`,
`FromPRF.lean`, `Pseudorandom/Functions.lean`, `Encryption/PrivateKey.lean`) is present in the same file and
order, with its header (keyword line to the top-level `:=`/`|`/`where`), its `omit … in` lines and its
statement prose (docstring before `**Proof sketch`) byte-identical, and every `def`/`abbrev`/`structure`/
`instance` byte-identical in full: **0 differences** (Defs 36 → 38 declarations, Hybrid 16 → 31,
ReductionMachine 44 → 82, FromPRF 23 → 24, HybridLemmas 7 → 7, facades 0 → 0; order kept). Control
(`evidence/headers/control-final.txt`, files in `control-final/`): one character changed in the header of
`prfScheme_multiMessageSecure` is reported as exactly **one** difference. The checkpoint runs and controls are
kept (`headers-cp1/cp2`, `control-cp1/cp2`). What changed in base declarations: proofs, `**Proof sketch.**`
paragraphs, module docstrings, added imports and declarations — nothing else.

## Checks

* **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; no cgroup memory limit, headroom = MemAvailable
  ≈ 15.5 GiB; disk 11.0 GiB free at first (below the 12 GiB floor), so I removed only this session's own
  finished worktrees (`/workspace/prfbase`, `/workspace/folds`; their branches keep their commits): 14.15 GiB.
* **Packages and cache.** `.lake/packages` is a symlink to this host's populated tree at exactly the manifest's
  pins (the addendum's alternative; the manifest at `7b307d62` is byte-identical to that tree's).
  `evidence/logs/packages-check.log`: 11 match, 0 mismatch, 4 absent. The 111 Mathlib roots computed from
  `order.txt` equal `roots.txt`; the narrowed `lake exe cache get` exited 0, "No files to download" (2,400
  decompressed from the store of 2,402 archives left by earlier sessions on this host: `cache-store.log`); no
  zero-size olean (`zero-oleans.log`); probe `import Mathlib.Algebra.BigOperators.Field` passed
  (`cache-probe.log`). No `lake build`, no unfiltered cache get; Python always as `python3 -I` (one exception,
  disclosed under *Bootstrap*).
* **Bootstrap** (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`): 434/434 exit 0, 0 error
  diagnostics with `^\S+\.lean:\d+:\d+: error[:(]` (`evidence/base/bootstrap-errors.txt`). History
  (`bootstrap-run.log`): the first background loop ran `sweep.py` without `-I` for 8 modules and was restarted
  with `python3 -I`; I paused it after 176 modules to try the edits, then restored the base sources and rebuilt
  every module from position 149 (the first owned module) at the base before finishing (first-pass rows:
  `bootstrap-pass1.tsv`).
* **Final recheck and sweep** (`evidence/final/`). Order: `order-final.txt` = `order.txt` with the new
  `FromPRF/MultiMsgOut` inserted at position 154, just before its consumer `FromPRF` (`reorder.log`, tool
  `reorder.py`). First the owned and new modules in order (`recheck.tsv`, `recheck/`: `Asymptotic/Defs`,
  `HybridLemmas`, `ReductionMachine`, `Hybrid`, `MultiMsgOut`, `FromPRF`: 6/6 exit 0, 0 errors), then the whole
  order, **all 435 modules from the first**, at `40127c584`: **435/435 exit 0, 0 error diagnostics** with
  `^\S+\.lean:\d+:\d+: error[:(]` (`sweep-errors.txt`, rows `sweep.tsv`, raw logs `sweep/`, run log
  `sweep-run.log`).
  Checkpoint sweeps (286 modules from position 149 each) are kept in `evidence/cp1/`, `evidence/cp2/`: both
  286/286, 0 errors, census identical; a first cp2 run that I stopped after 7 modules to add the two readers is
  kept in `evidence/cp2/aborted/`.
* **Sorry census** (`evidence/final/sorry-census-final.txt`, tool `sorrycensus.py`, from the final sweep's
  logs, all 435 modules): **40 declarations in 19 modules, identical** to the base census
  (`evidence/base/sorry-census-base.txt`) and to `base-sorries.txt`; no admission removed or added.
* **Axioms** (`evidence/axioms/axioms-final.log`, tool `axioms.py`; comparison
  `evidence/axioms/axioms-compare.txt`): every stored constant of the six changed/new modules (321) depends on at
  most `propext`, `Classical.choice`, `Quot.sound`; this includes all **61 new** declarations and all **22
  re-derived** ones. **Every base constant still stored has exactly its base axiom list** (0 changed; the
  checkpoint-2 change of `encodeHist_eq_flatMap` to `[Quot.sound, propext]` is undone: its proof is now the
  term `encodeHist_eq_flatMapOut h`, back to `[propext]`). The five endpoints `prfScheme_multiMessageSecure`,
  `exists_multiMessageSecure_of_exists_prg`, `Composability.prfFixedScheme_cpa`, `Composability.ccaScheme_cca2`,
  `exists_prf_of_exists_prg`: `[Classical.choice, Quot.sound, propext]` at base and final, **identical**.
  Disclosed: 15 base constants are no longer stored, all **auto-generated** (equation lemmas
  `multiMsgAdv.eq_1`, `otpEnc.eq_1`, `histBlock.eq_1`, `maskBlock.eq_1`, `maskOf.eq_1`, `adviceBound.eq_1`, and
  `match_`/`_proof_`/`_simp_` auxiliaries of the replaced proofs): the base proofs realized them by unfolding
  the definitions, the re-derived proofs go through the bridges. None is a source declaration or named
  anywhere; any later `rw`/`simp`/`unfold` realizes the equation lemmas on demand (the sweep is clean).
  Checkpoint logs: `axioms-cp1.log`, `axioms-cp2.log`.
* **Rule 10: seals** (`evidence/seals/final/`, tool `seals.py`, probe sources `scratch-src/seal/final/`; base
  runs `evidence/seals/base/`). Whole-file seals of every changed or new file over its full TCSlib import closure
  (every closure module foreign): all non-reducible TCSlib definitions and matchers made `local irreducible`;
  variant **A** treats `PolyExpr.eval` as notation (Q1), variant **B** seals it too; **strict** also seals the
  projection coercion `FinDist.instCoeFunForallReal`, **coe** exempts it. The harness re-verifies after the
  file that every request is still irreducible (`SEAL-VERIFY` lines). Errors counted with
  `^\S+\.lean:\d+:\d+: error[:(]`, attributed to the enclosing declaration.

  | file | A (strict = coe) | B (strict = coe): failing declarations | base B |
  |---|---|---|---|
  | `Asymptotic/Defs` (652 requests) | **pass** | 8 errors: `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary` (as at base); `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` (new) | 4 errors, the three base names |
  | `FromPRF/Hybrid` (617) | **pass** | pass | pass |
  | `FromPRF/ReductionMachine` (1577) | **pass** | 2 errors: `postFun_layout`, `exists_queryChain_nuppt` (re-derivations) | pass |
  | `FromPRF/MultiMsgOut` (1640, new) | **pass** | 1 error: `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | — |
  | `FromPRF.lean` (1772) | **pass** | 5 errors: `prfScheme`, `prfScheme_coinsEquiv`, `prfScheme_coinsEquiv_ofFn` (as at base); `prfScheme_multiMessageSecure` (re-derivation) | 4 errors, the three base names |
  | `Encryption/PrivateKey.lean` (2435) | **pass** | pass | pass |

  **Attribution.** Every B error (read in the raw logs) is an `Application type mismatch`/`Type mismatch`
  between `Fin n` and `Fin (PolyExpr.var.eval n)`, plus one cascade (`Unknown identifier
  prfAdv_toOracleAdversary_out` after that declaration failed): (i) the drafted statements of D1 and D4 take
  `OracleEnsemble.keyed (ℓ₁ := .var) F` with `F n : (Fin n → Bool) → …`, exactly like the base `PRF`; (ii) the
  re-derivations at `ℓ = var` (`exists_queryChain_nuppt := exists_queryChainOut_nuppt D q .var v`,
  `postFun_layout`, `prfScheme_multiMessageSecure`, `prfAdv_toOracleAdversary`) use `PolyExpr.var.eval n ≡ n`,
  which the brief names as notation (Q1) and says the re-derivations differ by. With `PolyExpr.eval` as notation
  (A, canonical) every file passes in both coe and strict forms; strict and coe give identical results for every
  file (the projection coercion is not reached by these files' proofs).
* **Rule 10: paired controls** (`evidence/seals/controls/`, tool `controls2.py`, source
  `scratch-src/controls/Controls.lean`; requests = the final census of everything the controls import, 1781–1783):
  six `CONTROL`/`READER` pairs on definitions of four owned files: C1 `MultiMsg.histBlockOut`, C4
  `MultiMsg.maskOfOut` (ReductionMachine), C2 `prfEncRealOut` (Hybrid), C3 `encodeTupleOut` (MultiMsgOut), C7
  `encodeHist` (Asymptotic/Defs), and C5 `PolyExpr.eval`. Unsealed: exit 0, no error. Sealed: **each negative
  fails exactly once** in all four variants (C5 only in the B variants, as designed: it closes when
  `PolyExpr.eval` is notation), every reader closes. The probe C6 (`FinDist`'s projection coercion read by `rfl`)
  closes in all variants (recorded, not a control). Two earlier attempts are kept, disclosed:
  `controls-attempt1/` (my C7 reader omitted `(ℓ₁ := .var)` and failed even unsealed) and `controls-attempt2/`
  (C7 on `OracleEnsemble.keyed`, whose statement `(keyed F).O n s` is itself ill-typed once `keyed` is sealed,
  so the reader failed too); C7 was then moved to `encodeHist`/`encodeHist_cons`. Only the logs of the attempts are
  kept; their sources differed from the delivered `Controls.lean` in C7 alone, as described.
* **Explicit-unfold scan** (`evidence/rwids/final/`, base `evidence/base/rwids/`; tools `rwids.py`,
  `rwids_run.py`, scan sources `scratch-src/rwids/`): every identifier passed to `rw`/`simp`/`unfold`/… in the six
  files, resolved in the file's namespace with its `open`s: **0 foreign TCSlib definitions, 0 core/Mathlib
  definitions** (base: 0 and 0). The 32 (file, definition) rows of class `own-def` (base: 27) are each the file's
  own definition: in `ReductionMachine` the new `…Out` definitions, the frozen ones inside their bridges and the
  helpers the base proofs already unfolded (`blockMapFun`, `takePolyFun`, `post…`); in `Hybrid` `chainTree`,
  `otpEncOut`, `multiMsgAdvOut`; in `FromPRF.lean` `encodeTuple` (in the bridge) and the base's
  `prfDecFun`/`prfDecWF`/`prfEncFun`; in `Asymptotic/Defs` the base's `buildTree`/`decodeOracleMove`.
  `MultiMsgOut` unfolds nothing. 222 identifiers are theorems; 63 are local hypotheses or private names.
* **Lint** (`evidence/lint/`): base 92 FAIL / 101 WARN (re-run at `7b307d62`, as the brief states), final
  **92 / 101** (`lint-final.txt`). Line-set diff (`lintdiff-final.txt`): **no new FAIL line**; two WARN lines
  **changed**, both check-8 lines of owned files, both **shortened** by bridges named after listed definitions
  (the effect the brief anticipates), and no new definition listed:
  * `Hybrid.lean`: "2 … chainTree, otpEnc" → "1 … chainTree" (bridge `otpEnc_eq_otpEncOut`);
  * `ReductionMachine.lean`: 16 → 10 definitions: `histBlock`, `maskBlock`, `maskOf`, `postCount`,
    `postOffset`, `postQuery` drop out (bridges `histBlock_eq_histBlockOut`, …, `postQuery_eq_postQueryOut`); the
    remaining ten are base names (`adviceBound`, `blockMapFun`, `dropPolyFun`, `histBlockLen`, `postAns`,
    `postBudget`, `postHist`, `postPoints`, `postVerdict`, `takePolyFun`).
  `FromPRF.lean`'s line (`prfDecFun`, `prfDecWF`, `prfEncFun`) is unchanged; `MultiMsgOut.lean` has no WARN or
  FAIL line. Every new public `def` has a reader beside it (`_eq`/`_apply`; `multiMsgAdvOut` through
  `eval_multiMsgAdvOut`); no new `abbrev`; no `@[simp]` added.
* **Sketches** (`evidence/checks/sketches-final.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph, except the base definition `prfScheme` (`FromPRF.lean`, a 17-line structure body, frozen and
  unchanged, listed at the base too). `exists_queryChainOut_nuppt` keeps the base step comments;
  `exists_oneQuery_nuppt` and `MultiMsg.exists_negligible_distAdv_prfEncRealOut` have their own. Every new public
  declaration has a docstring stating its formula; the main ones carry `[PS10, Definition 96.2 / Theorem 99.2,
  … with ℓ-bit outputs]`.
* **Compiler warnings**: over all 435 logs, 649 warnings at final against 650 at the base, and per module the same
  count except `ReductionMachine` (1 → 0: the base's unused simp argument `dbl_nil` at line 203 was in the
  proof of `zipWith_xor_histBlock_maskBlock`, now a re-derivation). `FromPRF.lean` keeps the base's one warning
  (unused simp argument `prfDecFun`, line 128 → 132, untouched proof). No new warning anywhere.

## Overlap and reuse

| New declaration | Nearest relative (`path:line` at the base) | Relation, and why not reused |
|---|---|---|
| `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean:430,441` `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` | generalization to `ℓ₂`; originals **re-derived**. `SecureComputation/SpecialEncryptionSecurity.lean:67` `prfOut_var_iff` (DL-8) relates `PRFOut .var` and `PRF`; the new lemma takes `PRFOut`'s clause (2) as its hypothesis (no import of `SecureComputation`), so DL-8 is untouched. |
| `prfEncRealOut`, `otpEncOut`, `multiMsgAdvOut` + readers, bridges | `FromPRF/Hybrid.lean:95,108,118` `prfEncReal`, `otpEnc`, `multiMsgAdv` | generalization to `l`; frozen definitions bridged by `rfl`; every lemma **re-derived**. |
| `acceptProb_oracleDist_multiMsgAdvOut`, `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_le` | `Hybrid.lean:142,157,321` | generalization; originals re-derived. |
| `distAdv_prfEncRealOut_random_otp_le` | `Hybrid.lean:243`; `HardcoreBit.pushesUniform_restrict` (DL-2) | reuses `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` unchanged; original re-derived. |
| `acceptProb_otpEncOut` | `Hybrid.lean:286`; `HardcoreBit.zipWith_xor_ofFn_add`, `distAdv_comp` (DL-2) | the same Boolean-group relabelling of the pads; original re-derived; no copy of the DL-2 lemmas. |
| `MultiMsg.exists_queryChainOut_nuppt` | `ReductionMachine.lean:461` `exists_queryChain_nuppt`; `Games/Efficiency.lean:844` T2 `exists_interactiveHandlerMachine`, T4 `exists_toOracleAdversary_of_bitCodec` | generalization to `ℓ`; original **re-derived**. Not built from T2/T4: it keeps this file's construction (`preFun`, uniform post-processor, advice, split coins) and changes only the string layer, so the `n`-bit theorem is literally its case `ℓ = var`; a T2/T4 build would be a second construction of the same machine beside the one the `n`-bit theorem needs, and would add an import edge from `ReductionMachine` (position 152 of `order.txt`) to `Games/Efficiency` (position 194; no cycle, as `Efficiency` does not import `FromPRF`, but not in the closure today). |
| `MultiMsg.exists_oneQuery_nuppt` | `exists_queryChainOut_nuppt` | its corollary (`q = const 0`, zero mask, `D ∘ pairFstD`); no second machine, as the brief asks. |
| (width handling of the `Out` machine lemmas) | `EncryptThenTag/Machines.lean:348` `ETTGame.eval_toOracleAdversary_len`, `OracleFromPRF/Reduction.lean:228` `PRFGame.eval_toOracleAdversary_width` | those transport an oracle adversary's `eval` along a propositional width equality via `padFin`. The `Out` lemmas need no transport (the width `ℓ.eval n` is in their types) and the `n`-bit cases use `PolyExpr.var.eval n ≡ n` (Q1). Neither lemma is used or restated. |
| string layer (`histBlockOut`, `maskBlockOut`, `maskOfOut`, `postCountOut`, `postOffsetOut`, `postQueryOut`, `postFunOut`, `histBlockLenOut`, `adviceBoundOut` + lemmas) | the `n`-bit string layer, `ReductionMachine.lean:50–445` (`histBlock` … `preFun_encodeHist`); `NMSim.chunkMap`, `Complexity.polyTimeComputable_blockMap` | generalization; `n`-bit lemmas re-derived via bridges. The block maps reuse this file's `blockMapFun`/`polyTimeComputable_blockMapFun`, as the `n`-bit code does, not `NMSim.chunkMap` (NonMalleability, not imported here). `histBlockLen`/`adviceBound` stay (ledger rows above). |
| (reused) `MultiMsg.take_drop_ofFn_blocks` | `EnsembleLemmas.take_drop_ofFn_blocks` (DL-9) | unchanged twin, used as before; DL-9 stays open on the ledger; no new copy. |
| (reused) `zipWith_xor_*` | the private `zipWith_xor_xor_self` copies (DL-40) | no new copy added. |
| `encodeTupleOut`, `encodeTupleOut_eq`, `encodeTupleOut_eq_flatten` | `FromPRF.lean:237,250` `encodeTuple`, `encodeTuple_eq_flatten` | generalization; `encodeTuple` bridged (`encodeTuple_eq_encodeTupleOut`), `encodeTuple_eq_flatten` re-derived. |
| `MultiMsg.encodeList_eq_flatMap` (public) | **`Asymptotic/BlockEncryptor.lean:60` `TCSlib.Cryptography.encodeList_eq_flatMap`** (same statement); `FromPRF.lean:241` private `encodeList_eq_flatMap`; `ClassP/BinaryArith/Words.lean:49` `encWords` (same right-hand side, other definition) | **duplicate, disclosed (ledger row)**. I found the public BlockEncryptor lemma only in the final search (`dupsearch-final.log`); the brief asked for the general form to be published in the new module. It cannot simply be reused: `MultiMsgOut` is imported by `FromPRF.lean`, and with `BlockEncryptor` in that closure the frozen private `encodeList_eq_flatMap` of `FromPRF.lean` (namespace `TCSlib.Cryptography`) fails with "a non-private declaration … has already been declared" (probe `scratch-src/probe/ClashProbe.lean`, log `evidence/final/clash-probe.log`: exactly that one error, exit 1); that is presumably why the base has the private copy. Hence the namespace `MultiMsg`. Resolution for the maintainer: see *Promotion requests*. |
| `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | `FromPRF.lean:348` `prfScheme_multiMessageSecure` | the scheme-free total at width `ℓ`; the original is **re-derived** from it. |

Searches (`evidence/tools/dupsearch.sh`): `evidence/overlap/dupsearch-base.log` on the issue base and
`evidence/overlap/dupsearch-final.log` on the final tree (names and statement shapes of every new declaration
against TCSlib and Mathlib sources).

## Scope requests

None. Every change is in the pre-approved files plus the new module `FromPRF/MultiMsgOut.lean` (imported by the
facade `FromPRF.lean`; `Encryption/PrivateKey.lean` got one import and one Contents bullet).

## Promotion and reader requests

* **Promotion request (resolves two ledger rows).** Move `encodeList_eq_flatMap` (and
  `length_le_length_encodeList`) from `Asymptotic/BlockEncryptor.lean` to `Encryption/PrivateKey/EnsembleSecurity.lean`,
  next to `PrivateKeyScheme.encodeList` and its readers `encodeList_nil`/`encodeList_cons` (both modules are in
  the closure of every current user). Then the private copy in `FromPRF.lean` and `MultiMsg.encodeList_eq_flatMap`
  can be deleted in favour of it, at landing (this unit may not delete the frozen private copy, and cannot
  promote outside its scope). No other promotion or reader request.

## Patches and reproduction

`patches/0001…0004-*.patch` (the whole `git format-patch` series from the issue base) and `patches/COMMITS.tsv`
(hash, author name/email/date, committer name/email/date). Before pushing, a scratch clone at the issue base
applied the series with `git am`, the committer set from `COMMITS.tsv`, and reproduced every hash and the final
tree (`evidence/amcheck/amcheck-final.log`; the checkpoint logs are kept).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, seal/control/probe/scan sources under
`scratch-src/`, tools under `tools/`); the top-level `SHA256SUMS` covers every delivered file except itself; both
were checked against the delivered paths (nothing missing, nothing extra) before the push. Tool notes: `seals.py`
and `rwids_run.py` were adapted from my prf-mac tools; their docstrings now say so, and the base census sources
in `scratch-src/seal/base/` still carry the old "prf-mac" label in a comment (the code is the same).
