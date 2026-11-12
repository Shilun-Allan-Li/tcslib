/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Lean
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
/- DLC-SEAL Encryption_PublicKey_HybridMachine: whole-file closure seal of `TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean` (PolyExpr.eval open). -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
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
  Lean.logInfo m!"DLC-SEAL Encryption_PublicKey_HybridMachine: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The public-key hybrid machine

The machine encrypts the messages outside the challenge position, inserts the
challenge ciphertext, then runs the tuple distinguisher. Its advice supplies the
hybrid index, the messages and the coin offsets.

## Main definitions

* `TCSlib.Cryptography.coinBlocks` identifies typed coin blocks with one coin string.
* `TCSlib.Cryptography.hybridPre` prepares the encoded tuple for the distinguisher.
* `TCSlib.Cryptography.hybridCoins` splits the hybrid machine's coins into encryptor
  blocks and distinguisher coins.

## Main results

* `TCSlib.Cryptography.blockEncFun_flatten` describes block encryption on a concatenation
  of messages. `TCSlib.Cryptography.encodeList_ofFn_split` splits an encoded tuple.
* `TCSlib.Cryptography.exists_hybridMachine` constructs the reduction with its coin count
  and run equation.
* `TCSlib.Cryptography.ofFn_hybridCoins` and
  `TCSlib.Cryptography.acceptProb_distinguisherL_coins` relate the machine to typed coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## Coin blocks -/

/-- The blockwise coin bijection `({0,1}^B)^k ≃ {0,1}^{k·B}`: block `i` occupies the positions
`i·B, …, i·B + B − 1` (`finProdFinEquiv`, `Equiv.curry`). -/
def coinBlocks (k B : ℕ) : (Fin k → Fin B → Bool) ≃ (Fin (k * B) → Bool) :=
  (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Unfolding of `coinBlocks`: bit `x` is bit `x mod B` of block `x / B`. -/
theorem coinBlocks_apply (k B : ℕ) (v : Fin k → Fin B → Bool) (x : Fin (k * B)) :
    coinBlocks k B v x = v (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := rfl

/-- The `i`-th coin segment (`coinBlock`) of the flattening of `v` is the block `v i`.

**Proof sketch.** `List.ext_getElem`: both sides have length `B` (`i < k`), and position `t` of
the segment is bit `i·B + t` of the flat string, which is `finProdFinEquiv (i, t)`
(`finProdFinEquiv_apply_val`), so `coinBlocks_apply` and `Equiv.symm_apply_apply` give
`v i t`. -/
theorem coinBlock_ofFn_coinBlocks (k B : ℕ) (v : Fin k → Fin B → Bool) (i : Fin k) :
    coinBlock B i (List.ofFn (coinBlocks k B v)) = List.ofFn (v i) := by
  have hle : (i : ℕ) * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B i.isLt
    rw [Nat.succ_mul] at this
    exact this
  have key : ∀ (x : Fin (k * B)) (t : ℕ) (ht : t < B), (x : ℕ) = (i : ℕ) * B + t →
      coinBlocks k B v x = v i ⟨t, ht⟩ := by
    intro x t ht hx
    have hx' : x = finProdFinEquiv (i, ⟨t, ht⟩) := by
      apply Fin.ext
      rw [hx, finProdFinEquiv_apply_val]
      ring
    rw [hx', coinBlocks_apply, Equiv.symm_apply_apply]
  apply List.ext_getElem
  · simp only [coinBlock_eq, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro t h1 h2
    simp only [coinBlock_eq, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    rw [List.length_ofFn] at h2
    exact key _ t h2 (by simp)

/-- A segment below the cut of a truncated coin string is the segment of the string. -/
theorem coinBlock_take (B i k : ℕ) (r : List Bool) (h : i < k) :
    coinBlock B i (r.take (k * B)) = coinBlock B i r := by
  have hle : i * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B h
    rw [Nat.succ_mul] at this
    exact this
  simp only [coinBlock_eq, List.drop_take, List.take_take]
  congr 1
  omega

/-- A segment of a coin string shifted by `k` blocks is the segment `k + i` of the string. -/
theorem coinBlock_drop (B i k : ℕ) (r : List Bool) :
    coinBlock B i (r.drop (k * B)) = coinBlock B (k + i) r := by
  simp only [coinBlock_eq, List.drop_drop]
  congr 2
  ring

/-- The length of the concatenation of `j` strings of `L` bits. -/
theorem length_flatten_ofFn {L : ℕ} : ∀ (j : ℕ) (f : Fin j → Fin L → Bool),
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L
  | 0, _ => by simp
  | j + 1, f => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      length_flatten_ofFn j (fun i => f i.succ)]
    ring

/-! ## The block encryptor on a tuple of messages -/

/-- `blockList` with `L`-bit blocks (`0 < L`) and enough fuel on the concatenation of `j`
strings of `L` bits is the list of their `j` encryptions with the consecutive coin segments
(the `L`-bit analogue of `blockList_ofFn`).

**Proof sketch.** Induction on `j`; `List.ofFn_succ` and `List.flatten_cons` split off the
first string, which is nonempty (`0 < L`) so the step fires, `List.take_left'`/`drop_left'`
cut it off exactly, and the segments of `r.drop B` are the shifted segments of `r`
(`List.drop_drop`). -/
theorem blockList_flatten (E : List Bool → List Bool) (L B : ℕ) (hL : 0 < L) (u pk : List Bool) :
    ∀ (j : ℕ) (msg : Fin j → Fin L → Bool) (r : List Bool) (k : ℕ), j ≤ k →
      blockList E L B u pk k (List.ofFn fun i => List.ofFn (msg i)).flatten r =
        List.ofFn fun i : Fin j =>
          E (NUPPT.layout u (pairEncode pk (List.ofFn (msg i))) [] (coinBlock B i r)) := by
  intro j
  induction j with
  | zero =>
    intro msg r k _
    cases k <;> simp [blockList_zero, blockList_succ]
  | succ j ih =>
    intro msg r k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons]
    have hne : List.ofFn (msg 0) ++ (List.ofFn fun i => List.ofFn (msg i.succ)).flatten ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_append, List.length_ofFn, List.length_nil] at this
      omega
    simp only [blockList_zero, blockList_succ, hne, if_false, List.cons.injEq]
    rw [List.take_left' (by simp), List.drop_left' (by simp)]
    refine ⟨?_, ?_⟩
    · simp [coinBlock_eq]
    · rw [ih (fun i => msg i.succ) (r.drop B) k (by omega)]
      congr 1
      funext i
      simp only [coinBlock_eq, Fin.val_succ, List.drop_drop]
      rw [show (B + ↑i * B) = (↑i + 1) * B by ring]

/-- **The block encryptor of a uniform machine on a tuple of messages**: on the state
`⟨1^n, ⟨pk, ⟨m_0 ‖ ⋯ ‖ m_{k-1}, r⟩⟩⟩` with `L(n)`-bit messages (`0 < L(n)`) it returns the tuple
of the activations `Enc(1^n, ⟨pk, m_i⟩; r_i)` with the consecutive `B(n)`-coin segments `r_i`
of `r`.

**Proof sketch.** The state word has at least `k` symbols (`0 < L(n)`), so `blockEncFun_spec`
applies with the word length as fuel; `blockList_flatten` lists the `k` block evaluations and
`Uniform.runAtL_eq` identifies each with an activation of `Enc`. -/
theorem blockEncFun_flatten (Enc : NUPPT) (hEnc : Enc.Uniform) (L : PolyExpr) (n : ℕ)
    (hL : 0 < L.eval n) (pk : List Bool) (k : ℕ) (msg : Fin k → Fin (L.eval n) → Bool)
    (r : List Bool) :
    blockEncFun Enc.output L Enc.coins
        (blockState (List.replicate n true) pk (List.ofFn fun i => List.ofFn (msg i)).flatten r) =
      encodeList (List.ofFn fun i : Fin k =>
        Enc.runAtL n (pairEncode pk (List.ofFn (msg i))) (coinBlock (Enc.coinLen n) i r)) := by
  have hk : k ≤ (blockState (List.replicate n true) pk
      (List.ofFn fun i => List.ofFn (msg i)).flatten r).length := by
    simp only [blockState_eq, length_pairEncode, length_flatten_ofFn]
    have := Nat.le_mul_of_pos_right k hL
    omega
  simp only [blockEncFun_eq]
  rw [blockEncFun_spec Enc.output L Enc.coins (List.replicate n true) pk _ _ r (by
    rw [length_flatten_ofFn, List.length_replicate]
    exact Nat.mul_le_mul_right _ hk)]
  simp only [List.length_replicate]
  rw [blockList_flatten Enc.output (L.eval n) (Enc.coins.eval n) hL (List.replicate n true) pk k
    msg r _ (Nat.le_succ_of_le hk)]
  refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [hEnc.runAtL_eq]
  rfl

/-! ## Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- The tuple encoding of `List.ofFn F` split at position `j`: the encoding of the first `j`
entries, then the block `⟨F j, ·⟩` around the encoding of the rest
(`encodeList_eq_flatMap`, `pairEncode_nil_append`). -/
theorem encodeList_ofFn_split {N : ℕ} (F : Fin N → List Bool) (j : Fin N) :
    encodeList (List.ofFn F) =
      encodeList (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
        pairEncode (F j)
          (encodeList (List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩)) := by
  rw [ofFn_eq_append_cons F j, encodeList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
    pairEncode_nil_append, ← encodeList_eq_flatMap, ← encodeList_eq_flatMap]

/-! ## The hybrid machine -/

/-- The pre-processing of the hybrid machine on the argument
`y = ⟨⟨⟨pk, c⟩, w⟩, ⟨u, ⟨⟨u₁, u₂⟩, ⟨M₁, M₂⟩⟩⟩⟩` (sample `⟨pk, c⟩`, own coins `w`, advice
`⟨u, …⟩` with `u = 1^n`, `u₁ = 1^{j·B(n)}`, `u₂ = 1^{(j+1)·B(n)}`, `M₁` the first `j` messages and
`M₂` the last `K(n) − j − 1` messages concatenated): encrypt the blocks of `M₁` with the first
`|u₁|` coins of `w` and those of `M₂` with the coins of `w` after the first `|u₂|`
(`blockEncFun`), and return `⟨pk, T₁ ++ ⟨c, T₂⟩⟩`, the tuple with `c` planted at position `j`. -/
def hybridPre (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) : List Bool :=
  pairEncode (pairFstD (pairFstD (pairFstD y)))
    (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
        (pairFstD (pairSndD (pairSndD (pairSndD y))))
        ((pairSndD (pairFstD y)).take (pairFstD (pairFstD (pairSndD (pairSndD y)))).length)) ++
      pairEncode (pairSndD (pairFstD (pairFstD y)))
        (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
          (pairSndD (pairSndD (pairSndD (pairSndD y))))
          ((pairSndD (pairFstD y)).drop (pairSndD (pairFstD (pairSndD (pairSndD y)))).length))))

/-- The pre-processing of the hybrid machine is polynomial-time.

**Proof sketch.** Pair projections for the eleven slots, the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` (`p := var`) on `⟨u₁, w⟩` and `⟨u₂, w⟩` for the
coin segments, `blockEncFun_poly` for the two block encryptors, `PolyTimeComputable.append` and
`pairEncode` for the assembly; the composite equals `hybridPre` by the projection identities. -/
theorem hybridPre_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (hybridPre E L B) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hpk := hF.comp (hF.comp hF)
  have hc := hS.comp (hF.comp hF)
  have hw := hS.comp hF
  have hu := hF.comp hS
  have hrest := hS.comp hS
  have hu₁ := hF.comp (hF.comp hrest)
  have hu₂ := hS.comp (hF.comp hrest)
  have hM₁ := hF.comp (hS.comp hrest)
  have hM₂ := hS.comp (hS.comp hrest)
  have hw₁ := (polyTimeComputable_pairTakePoly .var).comp (hu₁.pairEncode hw)
  have hw₂ := (polyTimeComputable_pairDropPoly .var).comp (hu₂.pairEncode hw)
  have hT₁ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₁.pairEncode hw₁)))
  have hT₂ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₂.pairEncode hw₂)))
  have h := hpk.pairEncode (hT₁.append (hc.pairEncode hT₂))
  convert h using 1
  funext y
  simp only [hybridPre, blockState_eq, Function.comp_apply, pairFstD_pairEncode,
      pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- **The hybrid machine** of the single ⇒ multi-message and bitwise theorems
[PS10, p. 103]: for a uniform encryptor `Enc`, a distinguisher `D`, a number of positions `K`,
a block length `L`, hybrid indices `j n` and message vectors `m n, m' n`, there is a
non-uniform PPT `B` with coins `K · Enc.coins + D.coins` such that at every parameter `n` with
`j n < K(n)` and `0 < L(n)`, on the sample `⟨pk, c⟩` with coins `v ‖ ρ` (`v` the `K(n)` coin blocks of `Enc`,
`ρ` the coins of `D`), `B` runs `D` on `⟨pk, ⟨c_0, …, c_{K(n)-1}⟩⟩` with coins `ρ`, where
`c_i = Enc(1^n, ⟨pk, m'_i⟩; v_i)` for `i < j`, `c_j = c`, and `c_i = Enc(1^n, ⟨pk, m_i⟩; v_i)`
for `i > j`.

**Proof sketch.** `B` is `D` pre-processed by `hybridPre` (`NUPPT.exists_comp`), with the
advice `⟨1^n, ⟨⟨1^{j·B}, 1^{(j+1)·B}⟩, ⟨M₁, M₂⟩⟩⟩` hard-wired at the parameters with
`j n < K(n)` and empty elsewhere (`NUPPT.exists_withAdvice`; length
at most `2n + 10 + 6·K·B + 3·K·L` by `length_pairEncode` and `length_flatten_ofFn`) and the first
`K · B` coins passed as data (`NUPPT.exists_split`). On the hybrid layout the two block
encryptors unfold by `blockEncFun_flatten`, their coin segments are the blocks of `v`
(`coinBlock_take`, `coinBlock_drop`, `coinBlock_ofFn_coinBlocks`), and the planted tuple is the
split `encodeList_ofFn_split` of the hybrid tuple at `j`. -/
theorem exists_hybridMachine (Enc D : NUPPT) (hEnc : Enc.Uniform) (K L : PolyExpr)
    (j : ℕ → ℕ) (m m' : ∀ n, Fin (K.eval n) → Fin (L.eval n) → Bool) :
    ∃ B : NUPPT, B.coins = .add (.mul K Enc.coins) D.coins ∧
      ∀ n, j n < K.eval n → 0 < L.eval n →
        ∀ (pk c : List Bool) (v : Fin (K.eval n) → Enc.Coins n) (ρ : D.Coins n),
        B.runAtL n (pairEncode pk c)
            (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ) =
          D.runAtL n (pairEncode pk (encodeList (List.ofFn fun i : Fin (K.eval n) =>
            if (i : ℕ) < j n then Enc.runAt n (pairEncode pk (List.ofFn (m' n i))) (v i)
            else if (i : ℕ) = j n then c
            else Enc.runAt n (pairEncode pk (List.ofFn (m n i))) (v i)))) (List.ofFn ρ) := by
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
    D.exists_comp (hybridPre_poly Enc.polyTimeComputable_output L Enc.coins) polyTimeComputable_id
  let β : ℕ → List Bool := fun n => if hj : j n < K.eval n then pairEncode (List.replicate n true)
    (pairEncode
      (pairEncode (List.replicate (j n * Enc.coinLen n) true)
        (List.replicate ((j n + 1) * Enc.coinLen n) true))
      (pairEncode (List.ofFn fun i : Fin (j n) => List.ofFn (m' n (Fin.castLE hj.le i))).flatten
        (List.ofFn fun i : Fin (K.eval n - j n - 1) =>
          List.ofFn (m n ⟨j n + 1 + i, by omega⟩)).flatten)) else []
  have hβ : ∀ n, (β n).length ≤ (PolyExpr.add (.add (.mul (.const 2) .var) (.const 10))
      (.add (.mul (.const 6) (.mul K Enc.coins)) (.mul (.const 3) (.mul K L)))).eval n := by
    intro n
    by_cases hj : j n < K.eval n
    · simp only [β, dif_pos hj, length_pairEncode, List.length_replicate, length_flatten_ofFn,
        PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, NUPPT.coinLen_eq]
      have h2 : j n * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj.le
      have h3 : (j n + 1) * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj
      have h4 : j n * L.eval n ≤ K.eval n * L.eval n := Nat.mul_le_mul_right _ hj.le
      have h5 : (K.eval n - j n - 1) * L.eval n ≤ K.eval n * L.eval n :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · simp [β, dif_neg hj]
  obtain ⟨D₂, hD₂c, hD₂⟩ := D₁.exists_withAdvice β _ hβ
  obtain ⟨B, hBc, -, hB⟩ := D₂.exists_split (.mul K Enc.coins)
  refine ⟨B, by rw [hBc, hD₂c, hD₁c], fun n hj hL pk c v ρ => ?_⟩
  rw [hB, hD₂, hD₁, id_eq]
  have hlen : (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)).length =
      (PolyExpr.mul K Enc.coins).eval n := by
    simp [NUPPT.coinLen_eq]
  rw [List.take_left' hlen, List.drop_left' hlen]
  congr 1
  -- the pre-processing on the hybrid layout
  simp only [hybridPre, β, dif_pos hj, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [blockEncFun_flatten Enc hEnc L n hL pk, blockEncFun_flatten Enc hEnc L n hL pk,
    encodeList_ofFn_split _ ⟨j n, hj⟩]
  congr 1
  congr 1
  · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
    have hi : (i : ℕ) < j n := i.isLt
    rw [coinBlock_take _ _ _ _ hi, ← Fin.coe_castLE hj.le i, coinBlock_ofFn_coinBlocks,
      ← NUPPT.runAt_eq]
    simp only [Fin.coe_castLE, hi, if_true]
  · congr 1
    · simp
    · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
      have hidx : coinBlock (Enc.coinLen n) (j n + 1 + i)
          (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)) =
          List.ofFn (v ⟨j n + 1 + i, by have := i.isLt; omega⟩) :=
        coinBlock_ofFn_coinBlocks (K.eval n) (Enc.coinLen n) v ⟨j n + 1 + i, by have := i.isLt; omega⟩
      rw [coinBlock_drop, hidx, ← NUPPT.runAt_eq]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega)]

/-- The coin length of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`. -/
theorem hybridCoins_len (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    K.eval n * Enc.coinLen n + D.coinLen n = B.coinLen n := by
  simp [NUPPT.coinLen_eq, hBc]

/-- The coins of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`: the `K(n)`
coin blocks of `Enc` followed by the coins of `D` (`coinBlocks`, `Fin.appendEquiv`). -/
def hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    (Fin (K.eval n) → Enc.Coins n) × D.Coins n ≃ B.Coins n :=
  ((coinBlocks (K.eval n) (Enc.coinLen n)).prodCongr (Equiv.refl _)).trans
    ((Fin.appendEquiv _ _).trans
      (Equiv.arrowCongr (finCongr (hybridCoins_len B Enc D K n hBc)) (Equiv.refl Bool)))

/-- The coin string of `hybridCoins (v, ρ)` is the flattening of `v` followed by `ρ`
(`List.ofFn_fin_append`, `List.ofFn_congr`). -/
theorem ofFn_hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) (v : Fin (K.eval n) → Enc.Coins n)
    (ρ : D.Coins n) :
    List.ofFn (hybridCoins B Enc D K n hBc (v, ρ)) =
      List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr (hybridCoins_len B Enc D K n hBc)
    (Fin.append (coinBlocks (K.eval n) (Enc.coinLen n) v) ρ)).symm

/-- **A machine's acceptance probability with its coins read through a bijection** `e`: if the
verdict of `B` on `X s` with coins `e t` is `A (X s) t`, the acceptance probabilities of `B`
and `A` on `X` agree (`uprob_comp_equiv` on the coin factor). -/
theorem acceptProb_distinguisherL_coins {σ τ : Type*} [Fintype σ] [Fintype τ] (B : NUPPT)
    (n : ℕ) (X : σ → List Bool) (e : τ ≃ B.Coins n) (A : List Bool → τ → Bool)
    (h : ∀ s t, B.distinguisherL n (X s) (e t) = A (X s) t) :
    acceptProb X (B.distinguisherL n) = acceptProb X A := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  congr 1
  funext z
  simp [h]

/-- `List.ofFn` of a constant on `Fin 1` is the one-letter string. -/
theorem ofFn_fin_one (b : Bool) : List.ofFn (fun _ : Fin 1 => b) = [b] := by
  simp [List.ofFn_succ]

end TCSlib.Cryptography
