/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Parties
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: shadow strategies and proof infrastructure

Proof infrastructure for `ThreeColoring/Protocol.lean` ([PS10, Protocol 127.5, Proposition
127.6]). That file is at the file-size limit, so the identification of its strategies with the
polynomial-time string functions of `ThreeColoring/Parties.lean` lives here. An imported file
cannot refer to the main file's definitions, so this file restates them **verbatim** in the
inner namespace `TCSlib.Cryptography.ColProofs` (the *shadow* definitions, the device of
`GraphIsomorphism/Proofs.lean`): every shadow is definitionally equal to its original, and the
main file closes each efficiency theorem by `ColProofs.…`, which type-checks by `rfl`. The
shadows are proof devices, not public API; any divergence from the frozen definitions of the
main file makes the main file fail to type-check, so it cannot go unnoticed.

## Main results

* `TCSlib.Cryptography.ColProofs.colProver_next_eq`, `ColProofs.colVerifier_next_eq`,
  `ColProofs.colProverRep_next_eq`, `ColProofs.colVerifierRep_next_eq` — the next-message
  functions of the (shadow) parties are the string functions of `Parties.lean` on the layout.
* `TCSlib.Cryptography.ColProofs.colVerify_eq_checkStr` — the verifier's check is `checkStr`
  when the graph has an edge.
* `TCSlib.Cryptography.ColProofs.colProver_efficient`, `ColProofs.colVerifier_efficient`,
  `ColProofs.colProverRep_efficient`, `ColProofs.colVerifierRep_efficient` — the (shadow)
  parties are PPT strategies (Inf-4.2).
* `TCSlib.Cryptography.ColProofs.pushesUniform_castLE`, `ColProofs.sampleEdgeIdx_ofFn_castLE`,
  `ColProofs.finOneEquiv`, `ColProofs.two_le_of_edge` — helpers of the soundness proof of
  Proposition 127.6.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.ColProofs

open Complexity Turing ColMachines TCSlib.Cryptography.EncodingMachines

/-! ### Shadow definitions -/

/-- Shadow of `TCSlib.Cryptography.msgAt` (verbatim copy; see the module docstring). -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- Shadow of `TCSlib.Cryptography.colCommit` (verbatim copy; see the module docstring). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- Shadow of `TCSlib.Cryptography.colOpen` (verbatim copy; see the module docstring). -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- Shadow of `TCSlib.Cryptography.colVerify` (verbatim copy; see the module docstring). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- Shadow of `TCSlib.Cryptography.colWellFormed` (verbatim copy; see the module docstring). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- Shadow of `TCSlib.Cryptography.colProver` (verbatim copy; see the module docstring). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- Shadow of `TCSlib.Cryptography.colVerifier` (verbatim copy; see the module docstring). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.colProtocol` (verbatim copy; see the module docstring). -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-- Shadow of `TCSlib.Cryptography.colCoinSlice` (verbatim copy; see the module docstring). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- Shadow of `TCSlib.Cryptography.colIterations` (verbatim copy; see the module docstring). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- Shadow of `TCSlib.Cryptography.colProverRep` (verbatim copy; see the module docstring). -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- Shadow of `TCSlib.Cryptography.colVerifierRep` (verbatim copy; see the module docstring). -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- Shadow of `TCSlib.Cryptography.colProtocolRep` (verbatim copy; see the module docstring). -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### The parties as string functions of the layout -/

/-- The honest prover's message of one iteration is `proverStr` of the layout. -/
theorem colProver_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x y r : List Bool)
    (hist : List (List Bool)) :
    (colProver Com ℓ).next x y r hist = proverStr Com ℓ (ilayout x y hist r) := by
  cases hist with
  | nil =>
    rw [proverStr, if_pos (by rw [argM_ilayout]; rfl), commitStr_ilayout]
    rfl
  | cons w hist' =>
    rw [proverStr, if_neg (by rw [argM_ilayout, Strategy.encodeMsgs_cons]; exact pairEncode_ne_nil _ _),
      mOf_ilayout]
    by_cases hm : edgeCount (decGraph x).2 = 0
    · rw [if_pos hm]
      simp only [colProver]
      rw [(edgeAt_eq_none_iff _ _).2 hm]
    · rw [if_neg hm, openStr_ilayout ℓ x y r hist' w (Nat.pos_of_ne_zero hm)]
      simp only [colProver]
      rw [edgeAt_eq_some_of_pos _ (Nat.pos_of_ne_zero hm)]
      simp only [edgeIdxOfMsg, Nat.mod_mod]
      rfl

/-- When the graph has an edge, the verifier's check is `checkStr`. -/
theorem colVerify_eq_checkStr (Com : List Bool → List Bool) (L : ℕ) (x com opn : List Bool)
    (e : ℕ) (hm : 0 < edgeCount (decGraph x).2) :
    colVerify Com L (decGraph x).2 e com opn =
      checkStr Com L (decGraph x).1 (edgeCount (decGraph x).2) x com opn e := by
  obtain ⟨h1, h2⟩ := edgeOf_val (decGraph x).2 x (decGraph_apply x)
    ⟨e % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
  unfold colVerify
  rw [edgeAt_eq_some_of_pos _ hm]
  unfold checkStr
  show decide _ = decide _
  rw [decide_eq_decide]
  simp only [msgAt, padColor, ofFn_padFin, encColor_eq_ofVal, decColor_val, h1, h2, ne_eq,
    Fin.ext_iff]

/-- The verifier's message of one iteration is `verifierStr` of the layout. -/
theorem colVerifier_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x z r : List Bool)
    (hist : List (List Bool)) :
    (colVerifier Com ℓ).next x z r hist = verifierStr Com ℓ (ilayout x z hist r) := by
  rcases hist with _ | ⟨com, _ | ⟨opn, _ | ⟨m3, t⟩⟩⟩
  · rw [verifierStr, if_pos (by rw [argM_ilayout]; rfl)]
    rfl
  · have c1 : argM (ilayout x z [com] r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z [com] r)) = [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode]
      rfl
    rw [verifierStr, if_neg c1, if_pos c2, eOf_ilayout]
    rfl
  · have c1 : argM (ilayout x z [com, opn] r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z [com, opn] r)) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    have c3 : pairSndD (pairSndD (argM (ilayout x z [com, opn] r))) = [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons,
        pairSndD_pairEncode]
      rfl
    rw [verifierStr, if_neg c1, if_neg c2, if_pos c3]
    show [decide _] = [verdictStr Com ℓ (ilayout x z [com, opn] r)]
    refine congrArg (fun b => [b]) ?_
    rw [verdictStr, nOf_ilayout, mOf_ilayout, LOf_ilayout, eOf_ilayout, argX_ilayout, argM_ilayout,
      Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairFstD_pairEncode,
      pairSndD_pairEncode, pairFstD_pairEncode, Bool.decide_and, Bool.decide_or, Bool.decide_and,
      Bool.decide_eq_true, Bool.decide_eq_true, colWellFormed, encGraph_decGraph_eq_take]
    by_cases hm : edgeCount (decGraph x).2 = 0
    · simp [hm]
    · rw [colVerify_eq_checkStr Com _ x com opn _ (Nat.pos_of_ne_zero hm)]
  · have c1 : argM (ilayout x z (com :: opn :: m3 :: t) r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z (com :: opn :: m3 :: t) r)) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    have c3 : pairSndD (pairSndD (argM (ilayout x z (com :: opn :: m3 :: t) r))) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons,
        pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact pairEncode_ne_nil _ _
    rw [verifierStr, if_neg c1, if_neg c2, if_neg c3]
    rfl

/-- The repeated prover's message is `proverRepStr` of the layout. -/
theorem colProverRep_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x y r : List Bool)
    (hist : List (List Bool)) :
    (colProverRep Com ℓ).next x y r hist = proverRepStr Com ℓ (ilayout x y hist r) := by
  have hlast : hist.getLastD [] =
      pairFstD (pairSndD^[hist.length - 1] (Strategy.encodeMsgs hist)) := by
    rw [getLastD_eq_getD, getD_eq_pairFstD_iterate]
  have hcoin : (colProver Com ℓ).coinLen x.length = proverCoinsOf ℓ x.length := by
    simp [Strategy.coinLen, colProver, proverCoinsOf]
  show (if hist.length / 2 < colIterations x then
      (colProver Com ℓ).next x y (colCoinSlice ((colProver Com ℓ).coinLen x.length) (hist.length / 2) r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []) = _
  rw [proverRepStr]
  simp only [argM_ilayout, histLen_encodeMsgs, nOf_ilayout, mOf_ilayout, argX_ilayout, argZ_ilayout,
    inCoins_ilayout]
  rw [hcoin]
  unfold colIterations colCoinSlice
  by_cases h1 : hist.length / 2 < (decGraph x).1 * edgeCount (decGraph x).2
  · rw [if_pos h1, if_pos h1, colProver_next_eq]
    unfold ilayout
    by_cases h2 : hist.length % 2 = 0
    · rw [if_pos h2, if_pos h2]
      rfl
    · rw [if_neg h2, if_neg h2, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, hlast]
  · rw [if_neg h1, if_neg h1]

/-- The repeated verifier's message is `verifierRepStr` of the layout. -/
theorem colVerifierRep_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x z r : List Bool)
    (hist : List (List Bool)) :
    (colVerifierRep Com ℓ).next x z r hist = verifierRepStr Com ℓ (ilayout x z hist r) := by
  show (if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then
        edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length
          (colCoinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
        ∀ t : Fin (colIterations x), colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
          (sampleEdgeIdx (edgeCount (decGraph x).2) x.length (colCoinSlice ((x.length + 1) ^ 2) t r))
          (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []) = _
  rw [verifierRepStr]
  simp only [argM_ilayout, histLen_encodeMsgs, nOf_ilayout, mOf_ilayout, argX_ilayout]
  unfold colIterations colCoinSlice
  by_cases h1 : hist.length % 2 = 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : hist.length / 2 < (decGraph x).1 * edgeCount (decGraph x).2
    · rw [if_pos h2, if_pos h2, eRep_ilayout]
      rfl
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : hist.length = 2 * (x.length * x.length)
    · rw [if_pos h3, if_pos h3]
      refine congrArg (fun b => [b]) ?_
      rw [verdictRepStr, nOf_ilayout, mOf_ilayout, argX_ilayout, Bool.decide_and, Bool.decide_or,
        Bool.decide_and, Bool.decide_eq_true, colWellFormed, encGraph_decGraph_eq_take]
      by_cases hm : edgeCount (decGraph x).2 = 0
      · simp [hm]
      · refine congrArg (fun b => _ && (_ || (_ && b))) ?_
        rw [decide_eq_decide, firstIdx_eq_iff, Fin.forall_iff]
        refine forall_congr' fun t => forall_congr' fun ht => ?_
        rw [checkRep, eRep_ilayout, Bool.not_eq_false', LOf_ilayout, nOf_ilayout, mOf_ilayout,
          argX_ilayout, argM_ilayout, ← getD_eq_pairFstD_iterate, ← getD_eq_pairFstD_iterate,
          colVerify_eq_checkStr Com _ x _ _ _ (Nat.pos_of_ne_zero hm)]
    · rw [if_neg h3, if_neg h3]

/-! ### Efficiency of the (shadow) parties -/

/-- The honest prover of one iteration is a PPT strategy when `Com` is (shadow form). -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  efficient_of_polyTime _ (proverStr_poly Com ℓ hCom) (colProver_next_eq Com ℓ)

/-- The verifier of one iteration is a PPT strategy when `Com` is (shadow form). -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  efficient_of_polyTime _ (verifierStr_poly Com ℓ hCom) (colVerifier_next_eq Com ℓ)

/-- The prover of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  efficient_of_polyTime _ (proverRepStr_poly Com ℓ hCom) (colProverRep_next_eq Com ℓ)

/-- The verifier of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  efficient_of_polyTime _ (verifierRepStr_poly Com ℓ hCom) (colVerifierRep_next_eq Com ℓ)

/-! ### Helpers of the soundness proof -/

/-- A graph with an edge and a proper colouring has at least two vertices. -/
theorem two_le_of_edge {n : ℕ} {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (hm : 0 < edgeCount G) : 2 ≤ n := by
  have hne : (edgeOf G ⟨0, hm⟩).1 ≠ (edgeOf G ⟨0, hm⟩).2 :=
    fun h => hc _ _ (edgeOf_adj G ⟨0, hm⟩) (by rw [h])
  have h1 := (edgeOf G ⟨0, hm⟩).1.isLt
  have h2 := (edgeOf G ⟨0, hm⟩).2.isLt
  by_contra hlt
  exact hne (Fin.ext (by omega))

/-- A prefix of a uniform tape is uniform (private copy of `GI.pushesUniform_castLE`). -/
theorem pushesUniform_castLE {m c : ℕ} (h : m ≤ c) :
    HardcoreBit.PushesUniform (fun t : Fin c → Bool => fun i : Fin m => t (Fin.castLE h i)) := by
  let e : (Fin c → Bool) ≃ (Fin m → Bool) × (Fin (c - m) → Bool) :=
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he : ∀ t : Fin c → Bool, (e t).1 = fun i : Fin m => t (Fin.castLE h i) := by
    intro t
    funext i
    simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, finCongr_symm,
      finCongr_apply, finSumFinEquiv_apply_left]
    congr 1
  have := (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
  simpa only [he] using this

/-- The bit `i < n` of `List.ofFn f` read with a default. -/
theorem ofFn_getD_lt {n : ℕ} (f : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]

/-- The edge sampler reads only the first `T · size m` bits of its tape. -/
theorem sampleEdgeIdx_ofFn_castLE {m T c : ℕ} (h : T * Nat.size m ≤ c) (t : Fin c → Bool) :
    sampleEdgeIdx m T (List.ofFn t) =
      sampleEdgeIdx m T (List.ofFn fun i : Fin (T * Nat.size m) => t (Fin.castLE h i)) := by
  unfold sampleEdgeIdx sampleIdx
  congr 3
  funext tr j
  have hlt : (tr : ℕ) * Nat.size m + j < T * Nat.size m := by
    have h1 := tr.isLt
    have h2 := j.isLt
    calc (tr : ℕ) * Nat.size m + j < (tr : ℕ) * Nat.size m + Nat.size m := by omega
      _ = ((tr : ℕ) + 1) * Nat.size m := by ring
      _ ≤ T * Nat.size m := Nat.mul_le_mul_right _ h1
  rw [ofFn_getD_lt t (lt_of_lt_of_le hlt h), ofFn_getD_lt _ hlt]
  rfl

/-- `Fin m` as single-round challenge tuples with trivial prover data. -/
def finOneEquiv (m : ℕ) : Fin m ≃ (Fin 1 → Fin m) × Unit where
  toFun e := (fun _ => e, ())
  invFun z := z.1 0
  left_inv _ := rfl
  right_inv z := by
    refine Prod.ext (funext fun i => ?_) rfl
    rw [Fin.fin_one_eq_zero i]

end TCSlib.Cryptography.ColProofs
