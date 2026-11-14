/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Complexity.Randomized.Repetition
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Machines: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Machines: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine constructions for the encrypt-then-tag proof

Two generic constructions on machines used by the proof of [PS10, Theorem 170.4]
(`Composability.ccaScheme_cca2`); both are candidates for promotion.

* **A budget cap** (`exists_capMachine`): for a machine `A` and a polynomial `q` there is a machine
  `A'` that behaves as `A` with budget `q(n)` at every budget `K ≥ q(n)`: once its log holds `q(n)`
  entries, a query of `A` is replaced by the empty word, which every bit codec reads as the
  all-`false` output, the timeout of the bit codec. The PRF reduction of the encrypt-then-tag proof
  runs at parameter `2n` with budget `q(2n)` an adversary whose budget is `q(n)`.
* **Halving the parameter** (`exists_halfMachine`): for a next-query machine `B` there is a machine
  `D` whose oracle adversary at parameter `2n` accepts any oracle with the probability that `B`'s
  accepts it at parameter `n` (`NUPPT.exists_reparam_advice` with `φ m = m / 2`; the coins `D` does
  not read are an independent uniform factor).

## Main definitions

* `ETTGame.logCount`: the number of entries of a nested-pair log, in unary.

## Main results

* `ETTGame.length_logCount_encodeLog`: `logCount` counts the entries of an encoded log.
* `ETTGame.buildComp_cap`: a next-move function capped after `q` entries computes, at every budget
  `K ≥ q`, what the original computes with budget `q`.
* `ETTGame.exists_capMachine`, `ETTGame.exists_halfMachine`, `ETTGame.eval_toOracleAdversary_len`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform machines) and Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Counting the entries of a log -/

/-- **The number of entries of a nested-pair log `⟨e₁, ⟨e₂, …⟩⟩`, in unary:** one `true` for every
nonempty suffix `pairSndD^[i] L`, `i ≤ |L|` (`cntRead`). -/
def logCount (L : List Bool) : List Bool :=
  (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L)

/-- `logCount L = ⋃_{i ≤ |L|} cntRead (pairSndD^[i] L)`. -/
theorem logCount_eq (L : List Bool) :
    logCount L =
      (List.range (PolyExpr.var.eval L.length + 1)).flatMap fun i => cntRead (pairSndD^[i] L) :=
  rfl

/-- The entry count is polynomial-time: an iterated emission (`polyTimeComputable_iterateEmit`)
along `pairSndD`, which does not lengthen its argument (`length_pairSndD_le`). -/
theorem polyTimeComputable_logCount : PolyTimeComputable logCount := by
  have horb : ∀ (x : List Bool) (i : ℕ), (pairSndD^[i] x).length ≤ x.length := by
    intro x i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact (length_pairSndD_le _).trans ih
  exact polyTimeComputable_iterateEmit polyTimeComputable_pairSndD polyTimeComputable_cntRead
    .var .var fun x i _ => by rw [PolyExpr.eval_var]; exact horb x i

/-- `#{i < N : i < L} = min N L`, as the length of an emission of `[true]` below `L`. -/
private theorem length_flatMap_range_lt (N L : ℕ) :
    ((List.range N).flatMap fun i => if i < L then [true] else []).length = min N L := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    by_cases h : N < L
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos h,
        List.length_singleton]
      omega
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, if_neg h, List.length_nil]
      omega

/-- An encoded log has at least as many bits as entries. -/
private theorem length_le_length_encodeLog {ι α : Type} {spec : OracleSpec ι}
    (codec : MachineCodec spec α) (h : QueryLog spec) : h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => simp
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **`logCount` counts the entries of an encoded log:** `|logCount (codec.encodeLog h)| = |h|`.

**Proof sketch.** The `i`-th suffix of `encodeLog h` is `encodeLog (h.drop i)`
(`MachineCodec.encodeLog_cons`, `pairSndD_pairEncode`), nonempty exactly for `i < |h|`
(`pairEncode_ne_nil`); every entry adds at least two bits (`length_pairEncode`), so the range
`i ≤ |encodeLog h|` covers all of them (`length_flatMap_range_lt`). -/
theorem length_logCount_encodeLog {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (h : QueryLog spec) : (logCount (codec.encodeLog h)).length = h.length := by
  have hsuf : ∀ (i : ℕ) (h : QueryLog spec),
      pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ih =>
      intro h
      cases h with
      | nil =>
        rw [List.drop_nil, Function.iterate_succ_apply, MachineCodec.encodeLog_nil]
        have : pairSndD ([] : List Bool) = [] := by
          have h1 := Complexity.BinArith.iterate_pairSndD_nil 1
          rwa [Function.iterate_one] at h1
        rw [this]
        have hn := ih []
        rwa [List.drop_nil, MachineCodec.encodeLog_nil] at hn
      | cons e h =>
        rw [Function.iterate_succ_apply, MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih,
          List.drop_succ_cons]
  have hcnt : ∀ i : ℕ, cntRead (pairSndD^[i] (codec.encodeLog h)) =
      if i < h.length then [true] else [] := by
    intro i
    rw [hsuf, cntRead_eq]
    by_cases hi : i < h.length
    · rw [if_pos hi]
      obtain ⟨e, t, ht⟩ : ∃ e t, h.drop i = e :: t := by
        cases hd : h.drop i with
        | nil => rw [List.drop_eq_nil_iff] at hd; omega
        | cons e t => exact ⟨e, t, rfl⟩
      rw [ht, MachineCodec.encodeLog_cons, decide_eq_false (pairEncode_ne_nil _ _)]
      rfl
    · rw [if_neg hi, List.drop_eq_nil_of_le (by omega), MachineCodec.encodeLog_nil]
      rfl
  have hlen := length_le_length_encodeLog codec h
  rw [logCount_eq]
  simp only [hcnt]
  rw [length_flatMap_range_lt, PolyExpr.eval_var]
  omega

/-! ### Capping a next-move function -/

/-- **Budget cap for `buildComp`.** Let `next'` agree with `next` on logs shorter than `q`, and on
logs of length `q` return `next`'s output, or the timeout `t` in place of a query. Then from a log
of length `|hist| = q - j`, at every budget `K ≥ j`, the computation of `next'` is the computation
of `next` at budget `j`: `buildComp next' t K hist = buildComp next t j hist`.

**Proof sketch.** Induction on `j`. At `j = 0` the log has length `q`, and `next'` returns
(`buildComp_of_ret`) what `buildComp next t 0` returns: the output, or `t` for a query. Below `q`
the moves agree; a query is asked at budgets `K = K' + 1` and `j' + 1` and both continue from the
log extended by the answer. -/
theorem buildComp_cap {ι α : Type} {spec : OracleSpec ι} (next next' : QueryLog spec → Move spec α)
    (t : α) (q : ℕ) (h₁ : ∀ hist : QueryLog spec, hist.length < q → next' hist = next hist)
    (h₂ : ∀ hist : QueryLog spec, hist.length = q →
      (∀ a, next hist = .ret a → next' hist = .ret a) ∧
        (∀ i x, next hist = .query i x → next' hist = .ret t)) :
    ∀ (j K : ℕ) (hist : QueryLog spec), hist.length + j = q → j ≤ K →
      buildComp next' t K hist = buildComp next t j hist := by
  intro j
  induction j with
  | zero =>
    intro K hist hq _
    obtain ⟨hr, hqy⟩ := h₂ hist (by omega)
    cases h : next hist with
    | ret a => rw [buildComp_of_ret (hr a h), buildComp_zero_of_ret h]
    | query i x => rw [buildComp_of_ret (hqy i x h), buildComp_zero_of_query h]
  | succ j ih =>
    intro K hist hq hK
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hn := h₁ hist (by omega)
    cases h : next hist with
    | ret a =>
      rw [buildComp_succ_of_ret (hn.trans h), buildComp_succ_of_ret h]
    | query i x =>
      rw [buildComp_succ_of_query (hn.trans h), buildComp_succ_of_query h]
      congr 1
      funext y
      exact ih K _ (by rw [List.length_append, List.length_singleton]; omega) (by omega)

/-- A word with first component `[false]` decodes as a query or as the default output:
`pairFstD w = [false] → decodeBitMove din dout dα w = ret a → a = zeroBits dα`.

**Proof sketch.** Such a word is not a canonical output word, whose first component is `[true]`
(`pairFstD_pairEncode`); if it is not a canonical query word either, it decodes to the default
(`decodeBitMove_of_not_canonical`); a canonical query word decodes as a query
(`decodeBitMove_query`). -/
private theorem eq_zeroBits_of_pairFstD_false {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}
    {w : List Bool} (hw : pairFstD w = [false]) {a : Fin dα → Bool}
    (ha : decodeBitMove din dout dα w = .ret a) : a = zeroBits dα := by
  by_cases hq : ∃ (i : Fin k) (x : Fin (din i) → Bool),
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  · obtain ⟨i, x, rfl⟩ := hq
    rw [decodeBitMove_query] at ha
    cases ha
  · push_neg at hq
    have hr : ∀ a' : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a') := by
      intro a' h
      rw [h, pairFstD_pairEncode] at hw
      cases hw
    rw [decodeBitMove_of_not_canonical hq hr] at ha
    cases ha
    rfl

/-- The empty word decodes to the default output: `decodeBitMove din dout dα [] = ret 0^{dα}`. -/
private theorem decodeBitMove_nil {k : ℕ} (din dout : Fin k → ℕ) (dα : ℕ) :
    decodeBitMove din dout dα [] = .ret (zeroBits dα) :=
  decodeBitMove_of_not_canonical (fun _ _ h => pairEncode_ne_nil _ _ h.symm)
    (fun _ h => pairEncode_ne_nil _ _ h.symm)

/-- A query word has first component `[false]`:
`decodeBitMove din dout dα w = query i x → pairFstD w = [false]`. -/
private theorem pairFstD_of_query {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    {i : Fin k} {x : Fin (din i) → Bool} (h : decodeBitMove din dout dα w = .query i x) :
    pairFstD w = [false] := by
  rw [decodeBitMove_eq_query_iff.1 h, pairFstD_pairEncode]

/-- The raw function of the capped machine: `A`'s output, except that once the argument (the
encoded log) has `q(n)` entries, an output with first component `[false]` (a query word) becomes
the empty word. -/
noncomputable def capRaw (A : NUPPT) (q : PolyExpr) (z : List Bool) : List Bool :=
  if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
      decide (pairFstD (A.output z) = [false]) then [] else A.output z

/-- `capRaw A q z = if |logCount (inArg z)| = q(|inParam z|) ∧ pairFstD (A.output z) = [false]
then [] else A.output z`. -/
theorem capRaw_eq (A : NUPPT) (q : PolyExpr) (z : List Bool) :
    capRaw A q z =
      if decide ((logCount (NUPPT.inArg z)).length = q.eval (NUPPT.inParam z).length) &&
          decide (pairFstD (A.output z) = [false]) then [] else A.output z :=
  rfl

/-- The capped raw function is polynomial-time: the entry count (`polyTimeComputable_logCount`),
a length comparison with `1^{q(n)}` (`EffFill.lenEq_poly`, `polyTimeComputable_unaryPoly`), a
word comparison (`polyTimeComputable_pairEq`) and `A`'s output. -/
theorem polyTimeComputable_capRaw (A : NUPPT) (q : PolyExpr) :
    PolyTimeComputable (capRaw A q) := by
  have hc := EffFill.lenEq_poly (polyTimeComputable_logCount.comp NUPPT.polyTimeComputable_inArg)
    ((polyTimeComputable_unaryPoly q).comp NUPPT.polyTimeComputable_inParam)
  have he : PolyTimeComputable fun z => [decide (pairFstD (A.output z) = [false])] :=
    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairFstD.comp
      A.polyTimeComputable_output).pairEncode (polyTimeComputable_const [false]))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  refine (polyTimeComputable_ite (polyTimeComputable_and hc he) (polyTimeComputable_const [])
    A.polyTimeComputable_output).congr fun z => ?_
  simp only [Function.comp_apply, List.length_replicate, capRaw_eq]

/-- **A budget cap** (generic; candidate for promotion). For a machine `A` and a polynomial `q`
there is a machine `A'` with `A`'s coins whose computation through any bit codec, at any budget
`K ≥ q(n)`, is `A`'s computation at budget `q(n)`:
`A'.toComp (bitCodec ins outs dα) n K (coinsCongr h n r) = A.toComp (bitCodec ins outs dα) n (q n) r`.

**Proof sketch.** `A' := NUPPT.ofPolyTime` of `capRaw A q` with `A`'s coins and advice
(`runAtL_ofPolyTime`). On the encoded log of `hist` the entry count is `|hist|`
(`length_logCount_encodeLog`). Below `q(n)` entries the move is `A`'s; at `q(n)` entries a query
word becomes the empty word, which decodes to the all-`false` output (`decodeBitMove_nil`, the
codec's timeout), and an output word with first component `[false]` already decoded to it
(`eq_zeroBits_of_pairFstD_false`); `buildComp_cap` concludes. -/
theorem exists_capMachine (A : NUPPT) (q : PolyExpr) :
    ∃ (A' : NUPPT) (h : A.coins = A'.coins), ∀ (n : ℕ) {k : ℕ} (ins outs : Fin k → ℕ)
      (dα K : ℕ) (r : A.Coins n), q.eval n ≤ K →
      A'.toComp (bitCodec ins outs dα) n K (NUPPT.coinsCongr h n r) =
        A.toComp (bitCodec ins outs dα) n (q.eval n) r := by
  refine ⟨NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
    A.advice_length, (NUPPT.coins_ofPolyTime _ _ _ _ _).symm, fun n k ins outs dα K r hK => ?_⟩
  have hrun : ∀ y, (NUPPT.ofPolyTime (polyTimeComputable_capRaw A q) A.coins A.adv A.advice
      A.advice_length).runAt n y (NUPPT.coinsCongr (NUPPT.coins_ofPolyTime _ _ _ _ _).symm n r) =
      if decide ((logCount y).length = q.eval n) && decide (pairFstD (A.runAt n y r) = [false])
      then [] else A.runAt n y r := by
    intro y
    rw [NUPPT.runAt_coinsCongr, NUPPT.runAtL_ofPolyTime, capRaw_eq, NUPPT.runAt_eq A,
      NUPPT.runAtL_eq A, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  rw [NUPPT.toComp_eq, NUPPT.toComp_eq, bitCodec_timeout]
  refine buildComp_cap _ _ _ (q.eval n) (fun hist hl => ?_) (fun hist hl => ⟨?_, ?_⟩) (q.eval n)
    K [] (by simp) hK
  · rw [bitCodec_decodeMove, bitCodec_decodeMove, hrun, length_logCount_encodeLog,
      decide_eq_false (Nat.ne_of_lt hl), Bool.false_and, if_neg Bool.false_ne_true]
  · intro a ha
    rw [bitCodec_decodeMove] at ha ⊢
    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and]
    by_cases hw : pairFstD (A.runAt n ((bitCodec ins outs dα).encodeLog hist) r) = [false]
    · rw [decide_eq_true hw, if_pos rfl, decodeBitMove_nil, eq_zeroBits_of_pairFstD_false hw ha]
    · rw [decide_eq_false hw, if_neg Bool.false_ne_true, ha]
  · intro i x hx
    rw [bitCodec_decodeMove] at hx ⊢
    rw [hrun, length_logCount_encodeLog, decide_eq_true hl, Bool.true_and,
      decide_eq_true (pairFstD_of_query hx), if_pos rfl, decodeBitMove_nil]

/-! ### Halving the parameter of a next-query machine -/

/-- **Halving the parameter** (generic; candidate for promotion). For a next-query machine `B`
there is a machine `D` whose oracle adversary at parameter `2n` accepts every oracle `h` with the
probability that `B`'s accepts it at parameter `n`, for all oracle lengths and budgets:
`𝔼_c [D^h(2n; c)] = 𝔼_c [B^h(n; c)]`.

**Proof sketch.** `D := NUPPT.exists_reparam_advice B (· / 2) var`: at parameter `2n` it runs
`B` at `2n / 2 = n` on the first `B.coinLen n` of its `B.coinLen (2n)` coins
(`PolyExpr.eval_subst`, `PolyExpr.eval_mono`). Split `D`'s coins as `B`'s coins and the rest
(`EnsembleLemmas.coinsEquiv`, `take_ofFn_coinsEquiv`); the trees agree (`toOracleAdversary_eq`)
and the unread coins average out (`expect_sample_prod`, `expect_const`). -/
theorem exists_halfMachine (B : NUPPT) :
    ∃ D : NUPPT, ∀ (n ℓ₁ ℓ₂ K : ℕ) (h : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)),
      expect (sample (D.Coins (2 * n)))
          (fun c => if (D.toOracleAdversary (2 * n) ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) =
        expect (sample (B.Coins n))
          (fun c => if (B.toOracleAdversary n ℓ₁ ℓ₂ K c).eval h = true then (1 : ℝ) else 0) := by
  obtain ⟨D, hDc, hD⟩ := B.exists_reparam_advice (fun m => m / 2) .var
    (fun m => by rw [PolyExpr.eval_var]; exact Nat.div_le_self m 2)
  refine ⟨D, fun n ℓ₁ ℓ₂ K h => ?_⟩
  have h2 : 2 * n / 2 = n := by omega
  have hle : B.coinLen n ≤ B.coinLen (2 * n) := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq]
    exact B.coins.eval_mono (by omega)
  have hlen : D.coinLen (2 * n) = B.coinLen n + (B.coinLen (2 * n) - B.coinLen n) := by
    rw [NUPPT.coinLen_eq, hDc, PolyExpr.eval_subst, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
    omega
  rw [← expect_sample_equiv (EnsembleLemmas.coinsEquiv hlen), ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun c₁ => ?_)
  refine (congrArg _ (funext fun c₂ => ?_)).trans (expect_const _ _)
  have hrun : ∀ y, D.runAt (2 * n) y (EnsembleLemmas.coinsEquiv hlen (c₁, c₂)) = B.runAt n y c₁ := by
    intro y
    rw [NUPPT.runAt_eq D, hD, NUPPT.runAt_eq B]
    simp only [h2]
    rw [EnsembleLemmas.take_ofFn_coinsEquiv]
  rw [NUPPT.toOracleAdversary_eq, NUPPT.toOracleAdversary_eq]
  simp only [hrun]

/-- **An oracle adversary read at equal widths** (generic; the width-changing form of
`PRFGame.eval_toOracleAdversary_width`, which fixes the widths to the parameter): for `ℓ = ℓ'`,
running `D.toOracleAdversary n ℓ ℓ K c` against `f` is running `D.toOracleAdversary n ℓ' ℓ' K c`
against `f` with its inputs and outputs read at width `ℓ'`.

**Proof sketch.** Substitute `ℓ' = ℓ`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_len (D : NUPPT) (n K : ℕ) (c : D.Coins n) {ℓ ℓ' : ℕ}
    (h : ℓ' = ℓ) (f : (Fin ℓ → Bool) → (Fin ℓ → Bool)) :
    (D.toOracleAdversary n ℓ ℓ K c).eval f =
      (D.toOracleAdversary n ℓ' ℓ' K c).eval
        (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ (List.ofFn x))))) := by
  subst h
  have e : (fun x => padFin ℓ' (List.ofFn (f (padFin ℓ' (List.ofFn x))))) = f := by
    funext x
    rw [padFin_ofFn, padFin_ofFn]
  rw [e]

end TCSlib.Cryptography.Composability.ETTGame
