/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_CPAHandler: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean`. -/
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
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_CPAHandler: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the CPA reduction

Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries is
simulated by a CPA adversary against the §3.9 scheme. This file builds that adversary's handler
(`bHandler`): a `Games.InteractiveHandler` from the CCA2 oracles of the encrypt-then-tag scheme
(lengths `ettDin`, `ettDout`) to the CPA oracles of the §3.9 scheme (lengths `PRFGame.pkDin`,
`PRFGame.pkDout`).

The handler's seed is `q(n)` tag tapes of `2n` bits; its state is the table of its `Enc′` answers
(`GGMRed.tblEnc` of the entries `(r ‖ c₁, t ‖ m)`, newest first), the query count and the
challenge record (`bState`).
- `Enc′` on `m`: ask the CPA encryption oracle, read its answer `⟨r, c₁⟩`, take the tag of
  `r ‖ c₁` from the table, else from the record, else from the query's tape, answer
  `⟨r, ⟨c₁, t⟩⟩` and add the entry.
- `Dec′` on `w`: refuse the record; if `w` is well formed and the table holds its pair with its tag,
  answer `⟨1, m⟩` with the table's message, else `⊥` (`lazyDec`). No outer query.
- `Challenge`: the first time, ask the CPA challenge oracle on `⟨m₀, m₁⟩`, tag its answer as `Enc′`
  does (without an entry) and record it; later repeat the record.
Words read from the outer answer are padded to their lengths (`EnsembleLemmas.padL`), so every
call is well formed for every outer answer. Lookups use GGM's table lookup (`GGMRed.lookup`,
`GGMRed.lookup_tblOf`).

## Main definitions

* `ETTGame.encE`, `tblW`, `bStLen`, `bSeedLen`, `bState`, `bSeed`, `bTapeOf`.
* `ETTGame.bHandler q hq b`: the handler.

## Main results

* `ETTGame.lookup_tblW`: the lookup on the table word is `lookL`.
* `ETTGame.bHandler_impl_enc`, `_impl_dec`, `_impl_challenge_some`, `_impl_challenge_none`: its
  answers on encoded states.
* `ETTGame.bHandler_finish`, `bHandler_init_hstate`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rAns)
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP)

/-! ### The table word -/

section Table

variable {n : ℕ}

/-- The string entry of a lazy-table entry `(p, t, m)`: `(⟦p⟧, ⟦t⟧ ++ m)`. -/
def encE (e : LEntry n) : List Bool × List Bool := (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2)

/-- `encE e = (⟦e.1⟧, ⟦e.2.1⟧ ++ e.2.2)`. -/
theorem encE_eq (e : LEntry n) : encE e = (List.ofFn e.1, List.ofFn e.2.1 ++ e.2.2) := rfl

/-- **The table word** of a lazy table: the nested pairs of its string entries (`GGMRed.tblEnc`). -/
def tblW (L : List (LEntry n)) : List Bool := GGMRed.tblEnc (L.map encE)

/-- `tblW L = GGMRed.tblEnc (L.map encE)`. -/
theorem tblW_eq (L : List (LEntry n)) : tblW L = GGMRed.tblEnc (L.map encE) := rfl

/-- The table word of the empty table is empty. -/
theorem tblW_nil : tblW ([] : List (LEntry n)) = [] := by
  rw [tblW_eq, List.map_nil, GGMRed.tblEnc_nil]

/-- A new entry is the first pair of the table word:
`tblW (e :: L) = ⟨⟨⟦p⟧, ⟦t⟧ ++ m⟩, tblW L⟩`. -/
theorem tblW_cons (e : LEntry n) (L : List (LEntry n)) :
    tblW (e :: L) = pairEncode (pairEncode (List.ofFn e.1) (List.ofFn e.2.1 ++ e.2.2)) (tblW L) := by
  rw [tblW_eq, tblW_eq, List.map_cons, GGMRed.tblEnc_cons, encE_eq]

/-- With `n`-bit messages, each entry adds `14n + 6` bits:
`|tblW L| = |L| · (14n + 6)`. -/
theorem length_tblW (L : List (LEntry n)) (hL : ∀ e ∈ L, e.2.2.length = n) :
    (tblW L).length = L.length * (14 * n + 6) := by
  induction L with
  | nil => rw [tblW_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | cons e L ih =>
    rw [tblW_cons, length_pairEncode, length_pairEncode, List.length_append, List.length_ofFn,
      List.length_ofFn, hL e (List.mem_cons_self ..), ih fun e' he' => hL e' (List.mem_cons_of_mem _ he'),
      List.length_cons]
    ring

/-- The table of string entries is `GGMRed.tblOf` of the pairs, with the entries' values. -/
private theorem map_encE_eq_tblOf (L : List (LEntry n)) :
    L.map encE = GGMRed.tblOf (fun k => (encE (L.getD k default)).2) (keysL L) 0 := by
  refine List.ext_getElem (by rw [List.length_map, GGMRed.length_tblOf, keysL_eq, List.length_map])
    fun k h₁ h₂ => ?_
  have hk : k < L.length := by rwa [List.length_map] at h₁
  refine Prod.ext ?_ ?_
  · rw [GGMRed.tblOf_getElem_fst, List.getElem_map, encE_eq]
    simp only [keysL_eq, List.getElem_map]
  · rw [GGMRed.tblOf_getElem_snd, List.getElem_map, Nat.zero_add, List.getD_eq_getElem _ _ hk]

/-- **The lookup on the table word is `lookL`:**
`lookup ⟨⟦p⟧, tblW L⟩ = ⟨[], ⟦t⟧ ++ m⟩` for the newest entry `(p, t, m)` at `p`, and `[]` if there is
none (`GGMRed.lookup_tblOf`). -/
theorem lookup_tblW (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
    GGMRed.lookup (pairEncode (List.ofFn p) (tblW L)) =
      match lookL L p with
      | some e => pairEncode [] (List.ofFn e.2.1 ++ e.2.2)
      | none => [] := by
  rw [tblW_eq, map_encE_eq_tblOf, GGMRed.lookup_tblOf, lookL_eq]
  by_cases hp : p ∈ keysL L
  · rw [if_pos hp, if_pos hp, encE_eq]
  · rw [if_neg hp, if_neg hp]

end Table

/-! ### Lengths, state and seed -/

variable (q : PolyExpr)

/-- The state length `2q(14n + 6) + 2q + 6n + 9`. -/
def bStLen : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul q (.add (.mul (.const 14) .var) (.const 6)))) (.mul (.const 2) q))
    (.add (.mul (.const 6) .var) (.const 9))

/-- `(bStLen q).eval n = 2 q(n) (14n + 6) + 2 q(n) + 6n + 9`. -/
theorem bStLen_eval (n : ℕ) :
    (bStLen q).eval n = 2 * (q.eval n * (14 * n + 6)) + 2 * q.eval n + (6 * n + 9) := by
  simp only [bStLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- The seed length `q(n) · 2n`: one tag tape per query. -/
def bSeedLen : PolyExpr := .mul q tagLen

/-- `(bSeedLen q).eval n = q(n) · 2n`. -/
theorem bSeedLen_eval (n : ℕ) : (bSeedLen q).eval n = q.eval n * (2 * n) := by
  rw [bSeedLen, PolyExpr.eval_mul, tagLen_eval]

/-- **The encoded state** with the table `L`, the query count `j` and the record `o`:
`⟨tblW L, ⟨1^j, recBits o⟩⟩`, padded with `false` to the state length. -/
def bState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((bStLen q).eval n) → Bool :=
  padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o)))

/-- `bState q n j L o = padFin _ ⟨tblW L, ⟨1^j, recBits n o⟩⟩`. -/
theorem bState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    bState q n j L o = padFin _ (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))) :=
  rfl

/-- **The seed** from the tape word: `⟦bSeed q n W⟧ = ⟦W⟧`. -/
def bSeed (n : ℕ) : (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bSeedLen q).eval n) → Bool) :=
  Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool)

/-- `bSeed q n = arrowCongr (finCongr _) (refl Bool)`. -/
theorem bSeed_eq (n : ℕ) :
    bSeed q n = Equiv.arrowCongr (finCongr (bSeedLen_eval q n).symm) (Equiv.refl Bool) := rfl

/-- `⟦bSeed q n W⟧ = ⟦W⟧`. -/
theorem ofFn_bSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
    List.ofFn (bSeed q n W) = List.ofFn W := by
  rw [bSeed, ofFn_arrowCongr_finCongr]

/-- The tag tape `j` of the tape word: block `j` of `W`. -/
def bTapeOf (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
    Fin (2 * n) → Bool :=
  EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩

/-- `bTapeOf q n W j hj = blocks (q n) (2n) W ⟨j, hj⟩`. -/
theorem bTapeOf_eq (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) (j : ℕ) (hj : j < q.eval n) :
    bTapeOf q n W j hj = EnsembleLemmas.blocks (q.eval n) (2 * n) W ⟨j, hj⟩ := rfl

/-- The fields of an encoded state that fits: the table word, the count `1^j`, the flag and the
record. -/
private theorem fields_bState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool))
    (hj : j ≤ q.eval n) (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
    pairFstD (List.ofFn (bState q n j L o)) = tblW L ∧
      pairFstD (pairSndD (List.ofFn (bState q n j L o))) = List.replicate j true ∧
      (pairSndD (pairSndD (List.ofFn (bState q n j L o)))).headD false = o.isSome ∧
      ((pairSndD (pairSndD (List.ofFn (bState q n j L o)))).drop 1).take (ettCt.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (tblW L) (pairEncode (List.replicate j true) (recBits n o))).length ≤
      (bStLen q).eval n := by
    rw [length_pairEncode, length_pairEncode, List.length_replicate, length_recBits,
      length_tblW L hm, bStLen_eval, ettCt_eval]
    have : L.length * (14 * n + 6) ≤ q.eval n * (14 * n + 6) := Nat.mul_le_mul_right _ hL
    omega
  rw [bState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right,
    pairFstD_pairEncode, pairSndD_pairEncode, ← GGMRed.pairEncode_append_right,
    pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases o with
    | none => rw [recBits_none, List.cons_append, List.headD_cons, Option.isSome_none]
    | some c => rw [recBits_some, List.cons_append, List.headD_cons, Option.isSome_some]
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The table word of the state. -/
private def bTbl (w : List Bool) : List Bool := pairFstD (rS w)
/-- The query count of the state. -/
private def bJ (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The challenge flag of the state. -/
private def bFlag (w : List Bool) : Bool := (pairSndD (pairSndD (rS w))).headD false
/-- The recorded challenge of the state. -/
private def bRec (w : List Bool) : List Bool :=
  ((pairSndD (pairSndD (rS w))).drop 1).take (ettCt.eval (rU w).length)
/-- A word read at `2n` bits. -/
private def bPad2 (w v : List Bool) : List Bool := EnsembleLemmas.padL (tagLen.eval (rU w).length) v
/-- The tape of the query count. -/
private def bTape (w : List Bool) : List Bool :=
  ((rW w).drop ((bJ w).length * tagLen.eval (rU w).length)).take (tagLen.eval (rU w).length)
/-- The pair `r ‖ c₁` of the outer answer `⟨r, c₁⟩`, at `2n` bits. -/
private def bKey (w : List Bool) : List Bool := bPad2 w (pairFstD (rAns w) ++ pairSndD (rAns w))
/-- The table lookup at a pair. -/
private def bLook (w key : List Bool) : List Bool := GGMRed.lookup (pairEncode key (bTbl w))
/-- The pair of the record, at `2n` bits. -/
private def bChalKey (w : List Bool) : List Bool :=
  bPad2 w (pairFstD (bRec w) ++ pairFstD (pairSndD (bRec w)))
/-- The tag of the record, at `2n` bits. -/
private def bChalTag (w : List Bool) : List Bool := bPad2 w (pairSndD (pairSndD (bRec w)))
/-- The tag of the outer answer's pair: the table's, else the record's, else the tape. -/
private def bTag (w : List Bool) : List Bool :=
  if decide (bLook w (bKey w) = []) then
    (if bFlag w && decide (bChalKey w = bKey w) then bChalTag w else bTape w)
  else (pairSndD (bLook w (bKey w))).take (tagLen.eval (rU w).length)
/-- The ciphertext `⟨r, ⟨c₁, t⟩⟩` of the outer answer and its tag, at `6n + 4` bits. -/
private def bCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (ettCt.eval (rU w).length)
    (pairEncode (pairFstD (rAns w)) (pairEncode (pairSndD (rAns w)) (bTag w)))
/-- The new state: the table word `tbl`, count `j + 1`, record `t`. -/
private def bNew (w tbl t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((bStLen q).eval (rU w).length) (pairEncode tbl (pairEncode (true :: bJ w) t))
/-- The pair of the decryption query, at `2n` bits. -/
private def bDKey (w : List Bool) : List Bool :=
  bPad2 w (pairFstD (rX w) ++ pairFstD (pairSndD (rX w)))
/-- Whether the decryption query is well formed. -/
private def bWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
/-- Whether the decryption query is the recorded challenge. -/
private def bRef (w : List Bool) : Bool := bFlag w && decide (rX w = bRec w)
/-- The lazy decryption answer (`lazyDec`) of the query, from the table. -/
private def bDecL (w : List Bool) : List Bool :=
  if (!bRef w && bWF w) = true then
    if decide (bLook w (bDKey w) = []) then []
    else if decide ((pairSndD (bLook w (bDKey w))).take (tagLen.eval (rU w).length) =
        pairSndD (pairSndD (rX w))) then
      true :: (pairSndD (bLook w (bDKey w))).drop (tagLen.eval (rU w).length)
    else []
  else []
/-- The decryption answer at `n + 1` bits. -/
private def bDecAns (w : List Bool) : List Bool :=
  EnsembleLemmas.padL ((PolyExpr.add .var (.const 1)).eval (rU w).length) (bDecL w)

/-- **One round of the handler** (see the module docstring). A first round of `Enc′` or of a first
challenge asks the CPA oracle; the second round, with the answer in the log, returns the answer and
the new state. Decryption and a repeated challenge answer at once. -/
private def bRun (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if bFlag w then
        pairEncode [true] (EnsembleLemmas.padL (ettCt.eval (rU w).length) (bRec w) ++
          bNew q w (bTbl w) (true :: bRec w))
      else if decide (rL w = []) then pairEncode [false] (pairEncode [true, true] (rX w))
      else pairEncode [true] (bCt w ++ bNew q w (bTbl w) (true :: bCt w))
    else pairEncode [true] (bDecAns w ++ bNew q w (bTbl w) (bFlag w :: bRec w))
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rX w))
    else pairEncode [true] (bCt w ++
      bNew q w (pairEncode (pairEncode (bKey w) (bTag w ++ rX w)) (bTbl w)) (bFlag w :: bRec w))

/-- The round function is polynomial-time: pair projections, the table lookup
(`GGMRed.lookup_poly`), padding (`EnsembleLemmas.polyTimeComputable_padL`), the tape by
`unaryMulPair`, `dropPrefixByLength` and `pairTakePoly`, word tests (`pairEq`, `lenEq_poly`) and
`polyTimeComputable_ite`. -/
private theorem polyTimeComputable_bRun : PolyTimeComputable (bRun q) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
  have hTbl : PolyTimeComputable bTbl := hF.comp hS
  have hJ : PolyTimeComputable bJ := (hF.comp hD).comp hS
  have hT : PolyTimeComputable fun w => pairSndD (pairSndD (rS w)) := (hD.comp hD).comp hS
  have hFlag : PolyTimeComputable fun w => [bFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable bRec :=
    ((polyTimeComputable_pairTakePoly ettCt).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hPad2 : ∀ {v : List Bool → List Bool}, PolyTimeComputable v →
      PolyTimeComputable fun w => bPad2 w (v w) := fun hv =>
    EnsembleLemmas.polyTimeComputable_padL tagLen hU hv
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((bJ w).length * tagLen.eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp (hJ.pairEncode
      ((polyTimeComputable_unaryPoly tagLen).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((bJ w).length * tagLen.eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hTape : PolyTimeComputable bTape :=
    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hKey : PolyTimeComputable bKey := hPad2 ((hF.comp hY).append (hD.comp hY))
  have hLook : ∀ {k : List Bool → List Bool}, PolyTimeComputable k →
      PolyTimeComputable fun w => bLook w (k w) := fun hk =>
    GGMRed.lookup_poly.comp (hk.pairEncode hTbl)
  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hNil : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => [decide (u w = [])] := fun hu => polyTimeComputable_isNil.comp hu
  have hTake2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => (u w).take (tagLen.eval (rU w).length) := fun hu =>
    ((polyTimeComputable_pairTakePoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hDrop2 : ∀ {u : List Bool → List Bool}, PolyTimeComputable u →
      PolyTimeComputable fun w => (u w).drop (tagLen.eval (rU w).length) := fun hu =>
    ((polyTimeComputable_pairDropPoly tagLen).comp (hU.pairEncode hu)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hChalKey : PolyTimeComputable bChalKey := hPad2 ((hF.comp hRec).append ((hF.comp hD).comp hRec))
  have hChalTag : PolyTimeComputable bChalTag := hPad2 ((hD.comp hD).comp hRec)
  have hTag : PolyTimeComputable bTag :=
    polyTimeComputable_ite (hNil (hLook hKey))
      (polyTimeComputable_ite (polyTimeComputable_and hFlag (hEq hChalKey hKey)) hChalTag hTape)
      (hTake2 (hD.comp (hLook hKey)))
  have hCt : PolyTimeComputable bCt :=
    EnsembleLemmas.polyTimeComputable_padL ettCt hU
      ((hF.comp hY).pairEncode ((hD.comp hY).pairEncode hTag))
  have hNew : ∀ {tb t : List Bool → List Bool}, PolyTimeComputable tb → PolyTimeComputable t →
      PolyTimeComputable fun w => bNew q w (tb w) (t w) := fun htb ht =>
    EnsembleLemmas.polyTimeComputable_padL (bStLen q) hU
      (htb.pairEncode (((polyTimeComputable_const [true]).append hJ).pairEncode ht))
  have hDKey : PolyTimeComputable bDKey := hPad2 ((hF.comp hX).append ((hF.comp hD).comp hX))
  have hWF : PolyTimeComputable fun w => [bWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
      (EffFill.lenEq_poly ((hF.comp hD).comp hX) hU)
  have hRef : PolyTimeComputable fun w => [bRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
  have hDecL : PolyTimeComputable bDecL :=
    polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_not hRef) hWF)
      (polyTimeComputable_ite (hNil (hLook hDKey)) (polyTimeComputable_const [])
        (polyTimeComputable_ite (hEq (hTake2 (hD.comp (hLook hDKey))) ((hD.comp hD).comp hX))
          ((polyTimeComputable_const [true]).append (hDrop2 (hD.comp (hLook hDKey))))
          (polyTimeComputable_const [])))
      (polyTimeComputable_const [])
  have hDecAns : PolyTimeComputable bDecAns :=
    EnsembleLemmas.polyTimeComputable_padL (.add .var (.const 1)) hU hDecL
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hKeep : PolyTimeComputable fun w => bFlag w :: bRec w := (hFlag.append hRec).congr fun _ => rfl
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hChal := polyTimeComputable_ite hFlag
    (hRet ((EnsembleLemmas.polyTimeComputable_padL ettCt hU hRec).append
      (hNew hTbl ((polyTimeComputable_const [true]).append hRec))))
    (polyTimeComputable_ite cNil
      ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const [true, true]).pairEncode hX))
      (hRet (hCt.append (hNew hTbl ((polyTimeComputable_const [true]).append hCt)))))
  have hDec := hRet (hDecAns.append (hNew hTbl hKeep))
  have hEnc := polyTimeComputable_ite cNil
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hX))
    (hRet (hCt.append (hNew ((hKey.pairEncode (hTag.append hX)).pairEncode hTbl) hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDec) hEnc

/-- The finalization's round: output `A`'s bit. -/
private def bFin (w : List Bool) : List Bool := pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_bFin : PolyTimeComputable bFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the CPA reduction** for the budget `q`: state `bState` (initially the empty
table, count `0`, no record), seed `q(n)` tag tapes, one outer call per inner query, the adversary
run on the empty input, and the finalization outputting the adversary's bit. -/
noncomputable def bHandler : InteractiveHandler 3 ettDin ettDout 3 pkDin pkDout where
  stateLen := bStLen q
  seedLen := bSeedLen q
  perCall := .const 1
  init n := bState q n 0 [] none
  run := bRun q
  poly := polyTimeComputable_bRun q
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 0
  finRun := bFin
  finRun_poly := polyTimeComputable_bFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall] bHandler

/-- The encoded state at the handler's state type: `bHState q n j L o = bState q n j L o`. -/
def bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((bHandler q).stateLen.eval n) → Bool :=
  bState q n j L o

/-- `bHState q n j L o = bState q n j L o`. -/
theorem bHState_eq (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    bHState q n j L o = bState q n j L o := rfl

/-- `⟦bHState q n j L o⟧ = ⟦bState q n j L o⟧`. -/
theorem ofFn_bHState (n j : ℕ) (L : List (LEntry n)) (o : Option (Fin (ettCt.eval n) → Bool)) :
    List.ofFn (bHState q n j L o) = List.ofFn (bState q n j L o) := rfl

/-- The seed at the handler's seed type: `bHSeed q n = bSeed q n`. -/
def bHSeed (n : ℕ) :
    (Fin (q.eval n * (2 * n)) → Bool) ≃ (Fin ((bHandler q).seedLen.eval n) → Bool) :=
  bSeed q n

/-- `bHSeed q n = bSeed q n`. -/
theorem bHSeed_eq (n : ℕ) : bHSeed q n = bSeed q n := rfl

/-- `⟦bHSeed q n W⟧ = ⟦W⟧`. -/
theorem ofFn_bHSeed (n : ℕ) (W : Fin (q.eval n * (2 * n)) → Bool) :
    List.ofFn (bHSeed q n W) = List.ofFn W :=
  ofFn_bSeed q n W

/-- The initial state is the empty table, count `0` and no record. -/
theorem bHandler_init_hstate (n : ℕ) : (bHandler q).init n = bHState q n 0 [] none := rfl

/-- The adversary's input is empty. -/
theorem bHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((bHandler q).seedLen.eval n) → Bool) : (bHandler q).advInput n z ω = [] := by
  rw [InteractiveHandler.advInput_eq]
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(bHandler q).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem bHandler_finish (n : ℕ) (z : List Bool) (ω : Fin ((bHandler q).seedLen.eval n) → Bool)
    (s : Fin ((bHandler q).stateLen.eval n) → Bool) (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (bHandler q).finish n z ω s a =
      .pure (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (bHandler q).finCall.eval n = 0 := by rw [bHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (bFin _) = _
  rw [bFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((bHandler q).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

/-- The pair of an outer answer `y = ⟨r, c₁⟩`, read at `2n` bits:
`bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
def bKeyOf (n : ℕ) {m : ℕ} (y : Fin m → Bool) : Fin (2 * n) → Bool :=
  padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y))

/-- `bKeyOf n y = padFin (2n) (pairFstD ⟦y⟧ ++ pairSndD ⟦y⟧)`. -/
theorem bKeyOf_eq (n : ℕ) {m : ℕ} (y : Fin m → Bool) :
    bKeyOf n y = padFin (2 * n) (pairFstD (List.ofFn y) ++ pairSndD (List.ofFn y)) := rfl

section Answers

variable (n : ℕ) (z : List Bool) (W : Fin (q.eval n * (2 * n)) → Bool)

/-- The round input of a call, field by field, on an encoded state that fits, with `j < q(n)`
and the seed `bHSeed W`. -/
private theorem fields_input {i : Fin 3} (x Lg : List Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    let w := InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg
    rU w = List.replicate n true ∧ rI w = List.replicate i true ∧ rX w = x ∧ rL w = Lg ∧
      bTbl w = tblW L ∧ bJ w = List.replicate j true ∧ bFlag w = o.isSome ∧
      bRec w = (recBits n o).drop 1 ∧ bTape w = List.ofFn (bTapeOf q n W j hj) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := fields_bState q n j L o hj.le hL hm
  have hS : rS (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg) = List.ofFn (bState q n j L o) :=
    (InteractiveHandler.rS_input ..).trans (ofFn_bHState q n j L o)
  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (bHSeed q n W))
    (List.ofFn (bHState q n j L o)) i x Lg
  have hJ : bJ (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
      (List.ofFn (bHState q n j L o)) i x Lg) = List.replicate j true := by rw [bJ, hS, h₂]
  refine ⟨hU, InteractiveHandler.rI_input .., InteractiveHandler.rX_input ..,
    InteractiveHandler.rL_input .., by rw [bTbl, hS, h₁], hJ, by rw [bFlag, hS, h₃],
    by rw [bRec, hS, hU, List.length_replicate, h₄], ?_⟩
  rw [bTape, hJ, hU, InteractiveHandler.rW_input, ofFn_bHSeed, List.length_replicate,
    List.length_replicate, tagLen_eval, bTapeOf_eq]
  exact EnsembleLemmas.take_drop_ofFn_blocks W j hj

/-- The outer answer recorded in a one-entry log. -/
private theorem rAns_one (w : List Bool) (u x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode u (pairEncode x' y)) []) : rAns w = y := by
  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (u x' y : List Bool) :
    decide (pairEncode (pairEncode u (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

/-- A word read at `2n` bits is a `2n`-bit word. -/
private theorem bPad2_fields (w v : List Bool) (hU : rU w = List.replicate n true) :
    bPad2 w v = List.ofFn (padFin (2 * n) v) := by
  rw [bPad2, hU, List.length_replicate, tagLen_eval, EnsembleLemmas.ofFn_padFin_eq_padL]

/-- The new state with table word `tblW L'`, count `j + 1` and record `recBits o'`. -/
private theorem bNew_fields (w : List Bool) (j : ℕ) (L' : List (LEntry n))
    (o' : Option (Fin (ettCt.eval n) → Bool)) (hU : rU w = List.replicate n true)
    (hJ : bJ w = List.replicate j true) :
    bNew q w (tblW L') (recBits n o') = List.ofFn (bHState q n (j + 1) L' o') := by
  rw [bNew, hU, hJ, List.length_replicate, ofFn_bHState, bState_eq,
    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]

/-- **The tag of a pair `p`:** the table's, else the record's, else the tape `t`. -/
private theorem bTag_fields (w : List Bool) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (p t : Fin (2 * n) → Bool)
    (hU : rU w = List.replicate n true) (hT : bTbl w = tblW L) (hF : bFlag w = o.isSome)
    (hR : bRec w = (recBits n o).drop 1) (hTp : bTape w = List.ofFn t)
    (hK : bKey w = List.ofFn p) :
    bTag w = List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) p).getD t) := by
  rw [bTag, bLook, hK, hT, lookup_tblW, tagOf_eq]
  cases h : lookL L p with
  | some e =>
    simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
      pairSndD_pairEncode, Option.getD_some]
    rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn])]
  | none =>
    simp only [decide_true, if_true]
    cases o with
    | none => simp only [hF, Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false,
        hTp, Option.getD_none]
    | some c =>
      have hRc : bRec w = List.ofFn c := by
        rw [hR, recBits_some, List.drop_succ_cons, List.drop_zero]
      have hCK : bChalKey w = List.ofFn (pairW n (List.ofFn c)) := by
        rw [bChalKey, hRc, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
      have hCT : bChalTag w = List.ofFn (padFin (2 * n) (wT (List.ofFn c))) := by
        rw [bChalTag, hRc, bPad2_fields n w _ hU, wT_eq]
      simp only [hF, Option.isSome_some, Bool.true_and, hCK, List.ofFn_inj]
      by_cases hc : pairW n (List.ofFn c) = p
      · simp only [hc, decide_true, if_true, hCT, Option.getD_some]
      · simp only [hc, decide_false, Bool.false_eq_true, if_false, hTp, Option.getD_none]

/-- **The lazy decryption answer of the query `⟦x⟧`:** `bDecL w = lazyDec (o, L) ⟦x⟧`. -/
private theorem bDecL_fields (w x : List Bool) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool))
    (hU : rU w = List.replicate n true) (hX : rX w = x) (hT : bTbl w = tblW L)
    (hF : bFlag w = o.isSome) (hR : bRec w = (recBits n o).drop 1) :
    bDecL w = lazyDec ((o, L) : LSt n (ettCt.eval n)) x := by
  have hRef : bRef w = refW o x := by
    rw [bRef, hF, hR, hX]
    cases o with
    | none => rw [Option.isSome_none, Bool.false_and, refW_none]
    | some c =>
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        refW_some]
      exact decide_eq_decide.2 eq_comm
  have hWF : bWF w = wfW n x := by
    rw [bWF, hU, hX, List.length_replicate, wfW_eq, wR_eq, wC_eq]
  have hDK : bDKey w = List.ofFn (pairW n x) := by
    rw [bDKey, hX, bPad2_fields n w _ hU, pairW_eq, pairV_eq, wR_eq, wC_eq]
  rw [bDecL, lazyDec_eq, hRef, hWF]
  simp only
  by_cases hc : (!refW o x && wfW n x) = true
  · rw [if_pos hc, if_pos hc, bLook, hDK, hT, lookup_tblW]
    cases h : lookL L (pairW n x) with
    | none => simp only [decide_true, if_true]
    | some e =>
      simp only [decide_eq_false (pairEncode_ne_nil _ _), Bool.false_eq_true, if_false,
        pairSndD_pairEncode]
      rw [hU, List.length_replicate, tagLen_eval, List.take_left' (by rw [List.length_ofFn]),
        List.drop_left' (by rw [List.length_ofFn]), hX, wT_eq]
      by_cases ht : List.ofFn e.2.1 = pairSndD (pairSndD x)
      · rw [if_pos (decide_eq_true ht), if_pos ht]
      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht]
  · rw [if_neg hc, if_neg hc]

/-- The flag and the record rebuild the record bits: `o.isSome :: (recBits o).drop 1 = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o with
  | none => rw [recBits_none, List.drop_succ_cons, List.drop_zero, Option.isSome_none]
  | some c => rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some]

/-- The inner query word read at the outer length: `⟦padFin _ ⟦x⟧⟧ = ⟦x⟧` for an `n`-bit `x`. -/
private theorem ofFn_padFin_msg {m : ℕ} (x : Fin m → Bool) (hm : m = n) :
    List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
  ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_zero, PolyExpr.eval_var, hm])

/-- **Encryption:** from `bState j L o` with `j < q(n)`, the query `m = ⟦x⟧` asks the CPA
encryption oracle at `m`; its answer `y` gives the ciphertext `⟨pairFstD y, ⟨pairSndD y, t⟩⟩`
with the tag `t` of the pair `bKeyOf n y` (`tagOf`, else the tape `j`), and the state
`bState (j + 1) ((bKeyOf n y, t, m) :: L) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks `m`; the second, with the answer in the log (`rAns_one`), computes the tag
(`bTag_fields`, from `lookup_tblW`), the ciphertext and the new state (`bNew_fields`, `tblW_cons`);
`InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem bHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 0 x (bHState q n j L o) =
      .query 0 (padFin _ (List.ofFn x)) fun y =>
        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
            (List.ofFn ((tagOf ((o, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
              (bTapeOf q n W j hj)))),
          bHState q n (j + 1) ((bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
            (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) :: L) o) := by
  have hx := ofFn_padFin_msg n x (by rw [ettDin_zero, PolyExpr.eval_var])
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show bRun q _ = _
    obtain ⟨-, hI, hX, hL', -⟩ := fields_input q n z W (i := 0) (List.ofFn x) [] j L o hj hL hm
    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL', if_pos (decide_eq_true rfl), hX, hx]
  · intro y
    show bRun q _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 0) (List.ofFn x)
      (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
        (List.ofFn x))) (List.ofFn y))) []) j L o hj hL hm
    have hY := rAns_one _ _ _ _ hL'
    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L o)) (0 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkDin 0).eval n)
          (List.ofFn x))) (List.ofFn y))) [])) = List.ofFn (bKeyOf n y) := by
      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
    have hTag := bTag_fields n _ L o (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
    rw [bRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL', log_ne_nil, if_neg Bool.false_ne_true, bCt, hY, hTag, hU, List.length_replicate, hK,
      hX, hT, hF, hR, recBits_fields, ← tblW_cons (bKeyOf n y, (tagOf ((o, L) : LSt n (ettCt.eval n))
        (bKeyOf n y)).getD (bTapeOf q n W j hj), List.ofFn x) L, bNew_fields q n _ j _ o hU hJ, ← ctW_eq]
    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_zero]

/-- **Decryption:** from `bState j L o` with `j < q(n)`, the query `⟦x⟧` is answered by
`lazyDec (o, L) ⟦x⟧` without an outer query, and the state is `bState (j + 1) L o`
(`bDecL_fields`). -/
theorem bHandler_impl_dec (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ) (L : List (LEntry n))
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 1 x (bHState q n j L o) =
      .pure (padFin _ (lazyDec ((o, L) : LSt n (ettCt.eval n)) (List.ofFn x)),
        bHState q n (j + 1) L o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show bRun q _ = _
  obtain ⟨hU, hI, hX, -, hT, hJ, hF, hR, -⟩ :=
    fields_input q n z W (i := 1) (List.ofFn x) [] j L o hj hL hm
  rw [bRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, bDecAns,
    bDecL_fields n _ _ L o hU hX hT hF hR, hU, List.length_replicate, hT, hF, hR, recBits_fields,
    bNew_fields q n _ j L o hU hJ]
  beta_reduce
  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_one]

/-- **A recorded challenge is repeated:** from `bState j L (some c)`, a challenge is answered `c`
and the state is `bState (j + 1) L (some c)`. -/
theorem bHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (L : List (LEntry n)) (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n)
    (hL : L.length ≤ q.eval n) (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L (some c)) =
      .pure (padFin _ (List.ofFn c), bHState q n (j + 1) L (some c)) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show bRun q _ = _
  obtain ⟨hU, hI, -, -, hT, hJ, hF, hR, -⟩ :=
    fields_input q n z W (i := 2) (List.ofFn x) [] j L (some c) hj hL hm
  have hRc : (recBits n (some c)).drop 1 = List.ofFn c := by
    rw [recBits_some, List.drop_succ_cons, List.drop_zero]
  have hrec : true :: List.ofFn c = recBits n (some c) := (recBits_some n c).symm
  rw [bRun, hI, hF, hR, hRc]
  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
  rw [hT, hrec, bNew_fields q n _ j L (some c) hU hJ, hU, List.length_replicate]
  rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]

/-- **The first challenge:** from `bState j L none` with `j < q(n)`, the challenge `⟦x⟧` asks the
CPA challenge oracle at `⟦x⟧`; its answer `y` gives the ciphertext `c = ⟨pairFstD y, ⟨pairSndD y, t⟩⟩`
with the tag `t` of `bKeyOf n y` (`tagOf (none, L)`, else the tape `j`), recorded in the state
`bState (j + 1) L (some c)`. -/
theorem bHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (L : List (LEntry n)) (hj : j < q.eval n) (hL : L.length ≤ q.eval n)
    (hm : ∀ e ∈ L, e.2.2.length = n) :
    (bHandler q).impl n z (bHSeed q n W) 2 x (bHState q n j L none) =
      .query 2 (padFin _ (List.ofFn x)) fun y =>
        .pure (padFin _ (ctW (pairFstD (List.ofFn y)) (pairSndD (List.ofFn y))
            (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (bKeyOf n y)).getD
              (bTapeOf q n W j hj)))),
          bHState q n (j + 1) L (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
              (bKeyOf n y)).getD (bTapeOf q n W j hj))))))) := by
  have hx : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, PRFGame.pkDin_two, ettDin_two])
  refine InteractiveHandler.impl_of_query _ n z _ x _ 2 _ _ _
    (by rw [bHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show bRun q _ = _
    obtain ⟨-, hI, hX, hL', -, -, hF, -⟩ :=
      fields_input q n z W (i := 2) (List.ofFn x) [] j L none hj hL hm
    rw [bRun, hI, hF, hL']
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false, decide_true]
    rw [hX, hx]
  · intro y
    show bRun q _ = _
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl]
    obtain ⟨hU, hI, hX, hL', hT, hJ, hF, hR, hTp⟩ := fields_input q n z W (i := 2) (List.ofFn x)
      (pairEncode (pairEncode [true, true]
        (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])
      j L none hj hL hm
    have hY := rAns_one _ _ _ _ hL'
    have hK : bKey (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [true, true]
          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
        List.ofFn (bKeyOf n y) := by
      rw [bKey, hY, bPad2_fields n _ _ hU, bKeyOf_eq]
    have hTag := bTag_fields n _ L none (bKeyOf n y) (bTapeOf q n W j hj) hU hT hF hR hTp hK
    have hrec : true :: bCt (InteractiveHandler.input n z (List.ofFn (bHSeed q n W))
        (List.ofFn (bHState q n j L none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [true, true]
          (pairEncode (List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x))) (List.ofFn y))) [])) =
        recBits n (some (padFin (ettCt.eval n) (ctW (pairFstD (List.ofFn y))
            (pairSndD (List.ofFn y)) (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n))
              (bKeyOf n y)).getD (bTapeOf q n W j hj)))))) := by
      rw [recBits_some, bCt, hY, hTag, hU, List.length_replicate, ← ctW_eq,
        EnsembleLemmas.ofFn_padFin_eq_padL]
    rw [bRun, hI, hF, hL']
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false]
    rw [log_ne_nil, if_neg Bool.false_ne_true, hrec, hT, bNew_fields q n _ j L _ hU hJ, bCt, hY,
      hTag, hU, List.length_replicate, ← ctW_eq]
    rw [EnsembleLemmas.ofFn_padFin_eq_padL, ettDout_two]

end Answers

end TCSlib.Cryptography.Composability.ETTGame
