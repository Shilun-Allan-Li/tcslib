# Claude fill · PRF machinery at ℓ-bit outputs (`prf-long`, ruling B3)

**Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` on `cryptography/pass-shelat-ch2-4` (the records tip after #303 and #305–#309;
records-only commits since the #307 merge `25fe1c05`). **Unit** `prf-long`. **Worker** Claude (standing ruling,
2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's `lake-manifest.json`.

Generalize the PRF machinery of [PS10, Theorem 99.2] (`Encryption/PrivateKey/FromPRF*`, `PRF.negligible_prfAdv`)
from `n`-bit to `ℓ(n)`-bit outputs, **additively**, in frozen files under a pre-approved scope. Seyoon ruled on
2026-11-14 (B3) that this machinery is generalized first, in this separate job, instead of being duplicated in the
secure-computation units. This job proves **no admitted target** and removes no `sorry`. Its consumer is the
garbling unit `sc-garble` (not yet issued): the B1 statement `sliceMultiMessageSecure_of_prfOut` (draft PR #311) and
`spDecStr_wrongKey`.

## Why (need analysis)

From the secure-computation plan (`briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`, §2.3,
§2.5 and B3):

- `SecureComputation.PRFOut ℓ G` (`SecureComputation/SpecialEncryptionSecurity.lean:56`) is a PRF with
  `ℓ(n)`-bit outputs. Its clause (2) is an `OracleEnsemble.Indist` at a general `ℓ₂`, so it applies directly to
  `D.toOracleAdversary n n ℓ₂ q`.
- **Missing piece 1:** a one-query next-query machine for an `ℓ₂`-output oracle. The existing
  `MultiMsg.exists_queryChain_nuppt` is specific to `n`-bit outputs.
- **Missing piece 2:** an `ℓ₂` analogue of `PRF.negligible_prfAdv`.
- **The hybrid.** The proof of `prfScheme_multiMessageSecure` (Theorem 99.2) is typed throughout for
  `F : … → (Fin n → Bool) → (Fin n → Bool)`: `prfEncReal`, `multiMsgAdv`, `distAdv_prfEncReal_le`,
  `exists_queryChain_nuppt`, `PRF.negligible_prfAdv`. The B1 proof needs the same three steps at a general output
  length: the PRF step, the random function plus the collision bound, and the total.

## Feasibility (maintainer's assessment)

Feasible. Every `n`-bit proof generalizes without a new idea:

- the concrete hybrids are already generic in the key type `K`; only the answer type is fixed to `Fin n → Bool`;
- `chainTree`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` and `MultiMsg.prfAdv_congr_equiv`
  are generic;
- the collision bound `uprob_not_injective_le` concerns the `n`-bit **points**, which do not change;
- the machine's string layer depends on the answer width only through its block lengths: a history block
  `⟨⟨x, y⟩, []⟩` of an `n`-bit query and an `ℓ(n)`-bit answer has `4n + 2ℓ(n) + 6` bits (now `6n + 6`).

No admitted declaration is on the route: the closure's admissions are the machine-library stubs and the open fill
targets, and none of them is used.

**Estimated size:** 700–1,200 lines added (net growth 400–900 after the re-derivations), in the six owned files and
one or two new modules. For calibration, the `n`-bit originals are `Hybrid.lean` 349 lines, `ReductionMachine.lean`
572, `HybridLemmas.lean` 182 and `FromPRF.lean` 424.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/prf-long` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/prf-long/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/prf-long/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill prf-long: checkpoint N` and `fill prf-long: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is merged** in the issue base.
- **#311 (B1 statement) and #312 (derand host statement) are not merged.** Do not import or depend on either:
  `SecureComputation/SpecialEncryptionMulti.lean` and `Complexity/Randomized/SeedMajority.lean` are absent at the
  issue base. Read the B1 statement and its 3-step sketch at the PR head `46b780dc1b286f59da18e2d10f188b0faaab8088` (branch
  `stmt/pass-shelat-b1-multimsg`), only to write the consumer map below.
- **Parallel fills.** `prf-mac` and `learning` are dispatched; `seq-zk`, `canonizer`, `sc-ot` and `sc-compose` are
  staged; `derand` is held. They were issued at `107f1e8c`. None edits a file you own. `prf-mac`, `learning`,
  `ccaScheme_cca2` and `prfFixedScheme_cpa` consume `PRF.negligible_prfAdv`; a proof-only change keeps their
  statements. `sc-ot` and `sc-compose` are told not to build any ℓ-output PRF.

## Scope (pre-approved by ruling B3)

**Owned frozen files.** You may edit these, under the frozen-statement rule below:

| File | Lines at base | What changes |
|---|---|---|
| `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` | 447 | `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` (re-derived from D1) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean` | 349 | `prfEncReal`, `otpEnc`, `multiMsgAdv` and the six-hybrid lemmas (re-derived from D2) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 572 | `MultiMsg.exists_queryChain_nuppt` and its string layer (re-derived from D3) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean` | 182 | already generic (`abs_uexp_sub_le_uprob`, `negligible_choose_div_two_pow`, `prfAdv_congr_equiv`); edit only to add a generic fact the route needs |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean` | 424 | facade of `FromPRF/`; `encodeTuple_eq_flatten` and `prfScheme_multiMessageSecure` (re-derived from D4); `## Contents` |
| `TCSlib/Cryptography/Pseudorandom/Functions.lean` | 52 | facade of `Functions/`; an import and a `## Contents` bullet only, if you add a module there |

**New modules** are permitted in `Encryption/PrivateKey/FromPRF/` (facade `FromPRF.lean`) and in
`Pseudorandom/Functions/Asymptotic/` (facade `Pseudorandom/Functions.lean`). The facade imports each one. The
`Encryption/PrivateKey.lean` facade, which lists the `FromPRF/` helpers one by one, may get one import line and one
`## Contents` bullet per new module, and nothing else.

**Read-only.** Every other file is frozen, in particular:

- `SecureComputation/SpecialEncryptionSecurity.lean` (the definition site of `PRFOut`, owned by `sc-garble`);
- `Pseudorandom/Functions/Defs.lean` (`prfAdv`), `OracleAdversary.lean`, `LazySampling.lean`, `SubHybrids.lean` and
  the GGM files;
- `Encryption/PrivateKey/OracleFromPRF*`, `EncryptThenTag*`, `Games/*`.

`Games/Efficiency.lean` is at 982 lines; do not add to it.

**`PRFOut` stays where it is.** It is defined in `SecureComputation`, downstream of every owned file. So state the
generic lemmas on its clause (2), the hypothesis
`(OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ)`; the consumer passes
`hG.pseudorandom`. Do not import `SecureComputation`, and do not move or restate `PRFOut`.

## The frozen-statement rule (binding; checked)

- **Headers.** Every declaration present at the issue base in an owned file stays in the same file and the same
  order, with its header byte-identical. The header is the attributes and modifiers, the keyword, the name, the
  binders and the type, up to the `:=`, `by`, `where` or first `|` that begins the proof.
- **Definitions are statements.** For a `def`, `abbrev`, `structure`, `inductive`, `class` or `instance`, the
  whole declaration, body included, is byte-identical. So `prfEncReal`, `otpEnc`, `multiMsgAdv`, `histBlock`,
  `postFun`, `encodeTuple` and the rest keep their bodies; relate them to the generic forms by `rfl` bridges.
- **What may change.** Only the proofs of theorems; their `**Proof sketch.**` paragraphs (rewritten to say "the
  case `ℓ = n` of …"); module docstrings (`## Main results`, `## Contents`); and added imports and declarations.
  Statement prose, `set_option`s and attributes do not change. Delete nothing, private lemmas included.
- **Check.** Write a `python3 -I` script that extracts every declaration of each owned file at the base and at the
  final, and compares headers (and whole definitions) byte for byte. Also check that the base declarations appear
  in the same order. Deliver it and its output under `evidence/headers/`, with zero differences. Add a control: a
  copy with one header altered by one character must report exactly one difference.

## Deliverables (draft signatures)

The names are binding unless one clashes. Disclose any rename and any change of binder style. Each new public
declaration needs a formula docstring.

### D1 · the ℓ-analogue of `PRF.negligible_prfAdv` (`Pseudorandom/Functions/Asymptotic/Defs.lean`)

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

Re-derive `prfAdv_toOracleAdversary` as the case `ℓ₂ = .var` of the first, and `PRF.negligible_prfAdv` as
`hF.pseudorandom.negligible_prfAdv D q`. Both differ only by `PolyExpr.var.eval n` against `n`, which is notation
(Q1).

### D2 · the concrete hybrids at output width `l` (`FromPRF/Hybrid.lean`)

```lean
-- section variables as in `section Concrete`: {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ],
-- plus {l : ℕ}, the output width
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))
theorem prfEncRealOut_apply … : prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))

def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)
theorem otpEncOut_apply … : otpEncOut m z j = (z.1 j, m j + z.2 j)

def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2
theorem eval_multiMsgAdvOut … (g : (Fin n → Bool) → Fin l → Bool) … :
    (multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2
theorem multiMsgAdvOut_boundedBy … : (multiMsgAdvOut m D).BoundedBy (q + 1)
theorem acceptProb_oracleDist_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool)) m D :
    acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D
theorem prfAdv_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool)) m D :
    prfAdv F (multiMsgAdvOut m D) =
      distAdv (prfEncRealOut F m)
        (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D
theorem distAdv_prfEncRealOut_random_otp_le (m : Fin (q + 1) → Fin l → Bool) D :
    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n
theorem acceptProb_otpEncOut (m m' : Fin (q + 1) → Fin l → Bool) D :
    acceptProb (otpEncOut (n := n) m) D = acceptProb (otpEncOut m') D
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n)

-- the rfl bridges used by the re-derivations
theorem prfEncReal_eq_prfEncRealOut … : prfEncReal F m = prfEncRealOut F m
theorem otpEnc_eq_otpEncOut … : otpEnc (n := n) m = otpEncOut m
theorem multiMsgAdv_eq_multiMsgAdvOut … : multiMsgAdv m D = multiMsgAdvOut m D
```

Re-derive from D2, as the case `l = n`: `prfEncReal_apply`, `eval_multiMsgAdv`, `multiMsgAdv_boundedBy`,
`acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`, `distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`
and `distAdv_prfEncReal_le`. `chainTree`, `uprob_not_injective_le` and `pushesUniform_comp_injective` are reused
as they are.

### D3 · the next-query machine at answer width `ℓ(n)` (`FromPRF/ReductionMachine.lean`)

```lean
namespace TCSlib.Cryptography.MultiMsg

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

`exists_queryChainOut_nuppt` is `exists_queryChain_nuppt` with `ℓ(n)`-bit answers and masks.
`exists_oneQuery_nuppt` is missing piece 1: `q = 0`, the zero mask, and `D` precomposed with `pairFstD`. It is a
corollary of the first; do not build a second machine.

- **String layer.** Generalize only what depends on the answer width: `histBlock`, `length_histBlock`,
  `encodeHist_eq_flatMap`, `histBlockLen`, `pairFstD_pairFstD_histBlock`, `maskBlock`, `length_maskBlock`,
  `zipWith_xor_histBlock_maskBlock`, `postCount`, `postOffset`, `postFun` with `polyTimeComputable_postFun`,
  `maskOf`, `length_maskOf`, `adviceBound`, `postFun_layout` and `preFun_encodeHist`. Use the suffix `Out` and give
  every new `def` its reader.
- **Reuse** the width-free helpers as they are: `length_flatMap_of_length`, `flatMap_range_blocks`,
  `flatMap_const_*`, `dbl_append`, `zipWith_xor_*`, `take_drop_ofFn_blocks`, `blockMapFun`, `takePolyFun`,
  `dropPolyFun`, `preFun`, `postHist`, `postPoints`, `postBudget`, `postAns`, `postQuery`, `postVerdict`,
  `length_flatten_of_length`, `decodeOracleMove_query`/`_ret` and `flatMap_ofFn`.
- **Re-derive** `exists_queryChain_nuppt` as the case `ℓ = .var`. Where it is cheap, also re-derive the `n`-bit
  helpers whose statements are cases of the generic ones.
- **Size.** Keep `ReductionMachine.lean` at most 1000 lines.

### D4 · the total at output length `ℓ` (new module `FromPRF/MultiMsgOut.lean`)

```lean
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList
    (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))
theorem encodeTupleOut_eq … (the defining equation)
theorem encodeTupleOut_eq_flatten … : encodeTupleOut v =
    (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten

theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n
```

This module imports `Hybrid`, `HybridLemmas`, `ReductionMachine` and `Asymptotic/Defs`, and `FromPRF.lean` imports
it. The proof is the present proof of `prfScheme_multiMessageSecure` at width `ℓ(n)`, without the scheme:

1. maximize over the finite pairs `(w, w')`;
2. build two machines with `exists_queryChainOut_nuppt`;
3. bound with `distAdv_prfEncRealOut_le` and `prfAdv_congr_equiv`;
4. conclude with `hF.negligible_prfAdv` (budget `q + 1`) and `negligible_choose_div_two_pow`.

Then re-derive, in `FromPRF.lean`, `encodeTuple_eq_flatten` from `encodeTupleOut_eq_flatten` (by `rfl` between
`encodeTuple` and `encodeTupleOut`). Also re-derive `prfScheme_multiMessageSecure` from
`exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q`, through `prfScheme_multiEncDist` and
`acceptProb_comp_equiv`. `encodeTuple_eq_flatten` rests on the private `encodeList_eq_flatMap`; publish its general
form in the new module, and leave the private copy in place.

### Re-derivation and its fallback

Re-derive every `n`-bit declaration listed above. If a re-derivation is too invasive, keep the `n`-bit
declaration's proof as it is. Examples: an elaboration blow-up at `PolyExpr.var.eval n`, or a file that would pass
1000 lines. For each one kept, add a row to `REPORT.md` § *Overlap and reuse*, marked **ledger**, with the exact
obstacle. The maintainer opens the duplication-ledger row at landing.

**Machine fallback.** If D3 cannot stay in `ReductionMachine.lean` within 1000 lines, put it in a new module
`FromPRF/QueryChainOut.lean` that imports `ReductionMachine`. Then keep `exists_queryChain_nuppt` as it is, since a
re-derivation would be a cycle, and record that as a ledger row.

## Proof route and checkpoints

1. **Checkpoint 1 · D1 and D2.** Deliver the asymptotic analogue and the concrete hybrids at width `l`, with their
   re-derivations, the header check and the sweep. Send this checkpoint.
2. **Checkpoint 2 · D3.** Deliver the string layer at width `ℓ(n)`, `exists_queryChainOut_nuppt`,
   `exists_oneQuery_nuppt` and the re-derivation of `exists_queryChain_nuppt`. Send this checkpoint.
3. **Final · D4 and the consumer map.** Deliver `MultiMsgOut.lean`, the re-derivations in `FromPRF.lean`,
   `## B1 consumer map` and the full evidence.

Check the edge cases:
- `ℓ(n) = 0`: the answers are empty, the random-function table is a singleton, and the history block has
  `4n + 6` bits;
- `n = 0`: the points are `Fin 0 → Bool`, and the collision bound is at most `C(q+1, 2)`;
- `q(n) = 0`: one point, so `C(1, 2) = 0`;
- the one-query budget `1` against `(PolyExpr.const 0).eval n + 1`;
- malformed machine outputs and the budget timeout (`decodeOracleMove`, the forced verdict `false`);
- block lengths `4n + 2ℓ(n) + 6 > 0`;
- the `rfl` bridges at `l = n` and `ℓ = .var`.

If a generic statement is false as drafted, stop and escalate with the exact obligation: a checkpoint with the
counterexample or the missing fact. Do not weaken it silently.

## B1 consumer map (required section of `REPORT.md`)

This job does **not** prove the B1 statement; that belongs to `sc-garble`. `REPORT.md` must still state, with the
final names, how each step of the B1 sketch (PR #311, `sliceMultiMessageSecure_of_prfOut`) uses the delivered
lemmas. The maintainer's draft:

0. **Reduction to tuples (`sc-garble`).** The mask of a slice `(o_i, ℓ_i)` and a message `m_i` is
   `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i}`, an `ℓ(n)`-bit string. Up to the coin relabelling,
   the slice sampler is `P_{o,ℓ} ∘ encodeTupleOut ∘ prfEncRealOut (G n) w`. Here `P_{o,ℓ}` maps each
   `⟨r_i, u_i⟩` to `⟨r_i, (u_i.drop o_i).take (n + ℓ_i)⟩`, inside `encodeList`.
   - The consumer builds `D' = D ∘ P` with the maximizing slices as advice: `NUPPT.exists_comp`,
     `NUPPT.exists_withAdvice`, and a block parser (`NMSim.polyTimeComputable_chunkMap` or
     `polyTimeComputable_blockMap`).
   - This post-processing is SecureComputation-specific and is **not** part of `prf-long`.
1. **PRF step.**
   - `distAdv_prfEncRealOut_le` and `prfAdv_multiMsgAdvOut`;
   - the machines from `exists_queryChainOut_nuppt`, with `MultiMsg.prfAdv_congr_equiv`;
   - negligibility from `OracleEnsemble.Indist.negligible_prfAdv hG.pseudorandom` at budget `q + 1`.
2. **Random function and collision.** `distAdv_prfEncRealOut_random_otp_le` (with `uprob_not_injective_le`) and
   `acceptProb_otpEncOut`: the full `ℓ(n)`-bit pads are uniform, so the windows are too.
3. **Total.**
   - `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q`, uniform in the masks `w, w'`;
   - with step 0 and the maximization over the slices and messages, this gives `ε`;
   - `MultiMsg.negligible_choose_div_two_pow` is inside the total.

`spDecStr_wrongKey` uses `exists_oneQuery_nuppt` and `OracleEnsemble.Indist.negligible_prfAdv` (budget 1).
`specialScheme_multiMessageSecure` follows from B1 (`specialScheme_multiMessageSecure_of_joint`, PR #311).

## Scope and proof discipline

- **Owned files.** As in *Scope*. Update each changed file's module docstring (`## Main results`, `## Contents`).
  Add no admission.
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any file outside the scope.
  - **Scope requests.** If the route needs a change outside the scope, or a frozen-statement exception, stop
    that line of work. Examples: a reader beside a foreign definition, a change to a definition body, a promotion.
    Ask Seyoon in your session, giving the exact file, the diff and the reason, and go ahead only on his approval.
    Record the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope
    requests*. Seyoon prefers a route with no such exception where one exists.
- **Parallel fills.** See *Base and parallel work*. Edit only the scope above.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran. Every
    `Out` declaration's relative is its `n`-bit original; say whether the original is re-derived or kept
    (**ledger**).
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:**
    - the generic next-query machinery of `Games/Efficiency.lean`: T2 `exists_interactiveHandlerMachine` and T4
      `exists_toOracleAdversary_of_bitCodec` (any `ℓ₁`, `ℓ₂`). Say why the chain machine is or is not built
      from them;
    - `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) and
      `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`);
    - `prfOut_var_iff` (DL-8);
    - `NMSim.chunkMap` and `polyTimeComputable_blockMap`;
    - `EnsembleLemmas.take_drop_ofFn_blocks` (DL-9, a twin of `MultiMsg.take_drop_ofFn_blocks`);
    - `HardcoreBit.pushesUniform_restrict`, `distAdv_comp`, `zipWith_xor_ofFn_add` (DL-2);
    - the private `zipWith_xor_xor_self` copies (DL-40).
- **Statements.** See *The frozen-statement rule*.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source (here Definition 96.2 and
    Theorem 99.2, "with ℓ-bit outputs");
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Each owned file and each new module counts as foreign to the others. A new module reads `prfEncRealOut` only
    through `prfEncRealOut_apply`, and so on.
  - Inside one owned file, the `rfl` bridges between a frozen definition and its `Out` form are allowed.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (434 modules) and the narrow `roots.txt` (111), following the addendum.
  - The order is large because `Asymptotic/Defs.lean` has 80 downstream modules, among them most top-level
    facades.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert new modules before their consumers.
- **Sweep.**
  - Recheck every owned and new module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (40 declarations in 19 modules). They must be
    **unchanged**: this job removes no admission and adds none.
- **Axioms.**
  - Print the axioms of every new declaration and of every re-derived one. Expect only `propext`,
    `Classical.choice` and `Quot.sound`.
  - Also print them for the downstream consumers `prfScheme_multiMessageSecure`,
    `exists_multiMessageSecure_of_exists_prg`, `Composability.prfFixedScheme_cpa` (`OracleFromPRF.lean`),
    `Composability.ccaScheme_cca2` (`EncryptThenTag.lean`) and `exists_prf_of_exists_prg`, at base and final. They
    must be identical.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (re-run at `7b307d62`).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
  - The owned files carry three check-8 WARN lines at base: `Hybrid.lean` (`chainTree`, `otpEnc`),
    `ReductionMachine.lean` (16 defs) and `FromPRF.lean` (`prfDecFun`, `prfDecWF`, `prfEncFun`). A bridge named
    after a listed def covers it and shortens its line. Disclose every such change.
- **Report.** `REPORT.md` gives:
  - the base;
  - the changed and new files, with lines at base and final;
  - the new declarations with their final signatures;
  - **Re-derivations**: each `n`-bit declaration listed above, re-derived or kept (**ledger**, with the obstacle);
  - **B1 consumer map**;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing. The unit then
goes to its own gate (decision log, 2026-11-14), before `sc-garble` is issued.

**Ready to dispatch**
