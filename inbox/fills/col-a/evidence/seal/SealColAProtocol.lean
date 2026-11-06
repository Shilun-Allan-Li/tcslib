import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option maxHeartbeats 0
set_option autoImplicit false

/-! Rule-10 seal of col-a's new code in `Protocol.lean`: verbatim copies of the new private
`colRep_*` lemmas and of the two filled proofs (namespace `SealA`), with every foreign TCSlib
definition their elaborated terms mention sealed, including the helper definitions
`ColRep.chView`, `ColRep.blockRead` (foreign to `Protocol.lean`). Definitions of `Protocol.lean`
itself (`colProverRep`, `colVerifierRep`, `colProtocolRep`, `colIterations`, `colCoinSlice`,
`colWellFormed`, `colVerify`, `colProver`, `challengesBefore`, `challengesUpTo`) are the owned
file's and stay unsealed. -/

namespace TCSlib.Cryptography.SealA

open Complexity Turing

attribute [local irreducible] _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.ColMachines.colorVal _root_.TCSlib.Cryptography.ColMachines.countTrue _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.L3COL _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.ProperColoring _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.R3COL _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.ThreeColorable _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decGraphAt _root_.TCSlib.Cryptography.edgeIdxOfMsg _root_.TCSlib.Cryptography.edgeMsg _root_.TCSlib.Cryptography.edgeOf _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.instDecidableProperColoring _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.sampleEdgeIdx _root_.TCSlib.Cryptography.samplePerm3 _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode _root_.TCSlib.Cryptography.ColRep.chView _root_.TCSlib.Cryptography.ColRep.blockRead

/-! ### The `n|E|`-fold protocol: the parties unfolded -/

/-- The `n|E|`-fold verdict in the published form (`Protocol.outV_withV`, `Protocol.withV_self`):
the verifier's activation on its view after the `4|x|²` moves. -/
private theorem colRep_outV (Com : List Bool → List Bool) (ℓ : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (colProtocolRep Com ℓ).ExecCoins P' x) :
    (colProtocolRep Com ℓ).outV P' x y z r = (colVerifierRep Com ℓ).next x z (List.ofFn r.2)
      (exec P' (colVerifierRep Com ℓ) false x y z (List.ofFn r.1) (List.ofFn r.2)
        (4 * (x.length * x.length))).2 := by
  have h := Protocol.outV_withV (colProtocolRep Com ℓ) (colProtocolRep Com ℓ).V P' x y z
  rw [Protocol.withV_self] at h
  rw [h r]
  show (colVerifierRep Com ℓ).next x z (List.ofFn r.2) (exec P' (colVerifierRep Com ℓ) false x y z
    (List.ofFn r.1) (List.ofFn r.2) ((PolyExpr.mul (.const 4) (.mul .var .var)).eval x.length)).2 = _
  rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- The challenge of iteration `t` of the `n|E|`-fold verifier with tape `rV`: the edge sampled
from coin block `t` for `t < n|E|`, and `[]` afterwards. -/
private def colRep_challenge (x : List Bool) (n m : ℕ) (rV : List Bool) (t : ℕ) : List Bool :=
  if t < n * m then edgeMsg (sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t rV))
  else []

/-- The `n|E|`-fold verifier on an odd history of `2t + 1` messages sends challenge `t`. -/
private theorem colRep_verifierRep_next_odd (Com : List Bool → List Bool) (ℓ : PolyExpr)
    {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r : List Bool)
    (hist : List (List Bool)) (h : hist.length % 2 = 1) :
    (colVerifierRep Com ℓ).next x z r hist =
      colRep_challenge x n (edgeCount G) r (hist.length / 2) := by
  have hK : colIterations x = n * edgeCount G := by rw [colIterations_eq, hx]
  show (if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2)
        x.length (colCoinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)) else []) else _) = _
  rw [if_pos h, hK, hx]
  rfl

/-- The `n|E|`-fold verifier sends `[]` on an even history that is not complete. -/
private theorem colRep_verifierRep_next_even (Com : List Bool → List Bool) (ℓ : PolyExpr)
    (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 = 0)
    (h2 : hist.length ≠ 2 * (x.length * x.length)) : (colVerifierRep Com ℓ).next x z r hist = [] := by
  show (if hist.length % 2 = 1 then _ else
    if hist.length = 2 * (x.length * x.length) then _ else []) = _
  rw [if_neg (by omega), if_neg h2]

/-- The `n|E|`-fold verifier's verdict on a complete history, on an input decoding to `⟨n, G⟩`. -/
private theorem colRep_verifierRep_next_end (Com : List Bool → List Bool) (ℓ : PolyExpr)
    {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r : List Bool)
    (hist : List (List Bool)) (h : hist.length = 2 * (x.length * x.length)) :
    (colVerifierRep Com ℓ).next x z r hist =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (n * edgeCount G),
        colVerify Com (ℓ.eval n) G
          (sampleEdgeIdx (edgeCount G) x.length (colCoinSlice ((x.length + 1) ^ 2) t r))
          (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))] := by
  have h1 : ¬ hist.length % 2 = 1 := by omega
  show (if hist.length % 2 = 1 then _ else if hist.length = 2 * (x.length * x.length) then
    [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
      ∀ t : Fin (colIterations x), colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
        (sampleEdgeIdx (edgeCount (decGraph x).2) x.length (colCoinSlice ((x.length + 1) ^ 2) t r))
        (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))] else []) = _
  rw [if_neg h1, if_pos h, colIterations_eq, hx]

/-- The `n|E|`-fold prover in iteration `t = |hist| / 2 < n|E|` runs `colProver` on coin block `t`,
on the empty history (even `|hist|`) or on the last message received (odd `|hist|`). -/
private theorem colRep_proverRep_next (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) (hist : List (List Bool))
    (ht : hist.length / 2 < n * edgeCount G) :
    (colProverRep Com ℓ).next x y r hist = (colProver Com ℓ).next x y
      (colCoinSlice ((colProver Com ℓ).coinLen x.length) (hist.length / 2) r)
      (if hist.length % 2 = 0 then [] else [hist.getLastD []]) := by
  have hK : colIterations x = n * edgeCount G := by rw [colIterations_eq, hx]
  show (if hist.length / 2 < colIterations x then _ else []) = _
  rw [hK, if_pos ht]

/-- The views of the `n|E|`-fold execution after its `4|x|²` moves (`ColRep.exec_four_mul` with the
challenges `colRep_challenge`): the verifier has received `2|x|²` messages, message `2j` being
the prover's message on `chView ch j` and message `2j + 1` its message on `chView ch j ++ [ch j]`. -/
private theorem colRep_views (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ}
    {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (P' : Strategy) (y z rP rV : List Bool) :
    (exec P' (colVerifierRep Com ℓ) false x y z rP rV (4 * (x.length * x.length))).2.length =
        2 * (x.length * x.length) ∧
      ∀ j < x.length * x.length,
        (exec P' (colVerifierRep Com ℓ) false x y z rP rV (4 * (x.length * x.length))).2.getD
            (2 * j) [] = P'.next x y rP (ColRep.chView (colRep_challenge x n (edgeCount G) rV) j) ∧
          (exec P' (colVerifierRep Com ℓ) false x y z rP rV (4 * (x.length * x.length))).2.getD
            (2 * j + 1) [] = P'.next x y rP (ColRep.chView (colRep_challenge x n (edgeCount G) rV) j ++
              [colRep_challenge x n (edgeCount G) rV j]) := by
  obtain ⟨h1, h2, -⟩ := ColRep.exec_four_mul P' (colVerifierRep Com ℓ) x y z rP rV
    (colRep_challenge x n (edgeCount G) rV) (x.length * x.length)
    (fun hist h => colRep_verifierRep_next_odd Com ℓ hx z rV hist h)
    (fun hist h1 h2 => colRep_verifierRep_next_even Com ℓ x z rV hist h1 (by omega))
    (x.length * x.length) le_rfl
  exact ⟨h1, h2⟩

/-! ### The `n|E|`-fold protocol: completeness -/

/-- **The honest `n|E|`-fold execution accepts** on every pair of tapes [PS10, proof of
Proposition 127.6, "completeness follows by inspection"] (Claim-127.e, repeated).

**Proof sketch.** The verdict is the verifier's activation on its view after `4|x|²` moves
(`colRep_outV`, `colRep_views`, `colRep_verifierRep_next_end`): `x` is well formed
(`colWellFormed_encGraph`); if `E = ∅` it accepts outright, and otherwise `n ≥ 2`
(`ColProofs.two_le_of_edge`) and in every iteration `t < n|E|` the prover, on its view of `2t`
or `2t + 1` messages, runs `colProver` on coin block `t` (`colRep_proverRep_next`): it commits
(`colProver_next_nil`) and opens the challenged edge (`colProver_next_cons`,
`edgeIdxOfMsg_edgeMsg`), which passes `colVerify` (`colVerify_honest`,
`ColMachines.edgeAt_eq_some_of_pos`). -/
private theorem colRep_outV_honest {Com : List Bool → List Bool} {ℓ : PolyExpr} {n : ℕ}
    {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c) (z : List Bool)
    (r : (colProtocolRep Com ℓ).ExecCoins (colProtocolRep Com ℓ).P (encGraph G)) :
    (colProtocolRep Com ℓ).outV (colProtocolRep Com ℓ).P (encGraph G) (encColoring c) z r =
      [true] := by
  have hx : decGraph (encGraph G) = ⟨n, G⟩ := decGraph_encGraph G
  have hKN := ColRep.mul_edgeCount_le G
  obtain ⟨hlen, hget⟩ := colRep_views Com ℓ hx (colProverRep Com ℓ) (encColoring c) z
    (List.ofFn r.1) (List.ofFn r.2)
  rw [colRep_outV]
  show (colVerifierRep Com ℓ).next _ z _ (exec (colProverRep Com ℓ) _ false _ _ z _ _ _).2 = _
  rw [colRep_verifierRep_next_end Com ℓ hx z _ _ hlen, colWellFormed_encGraph]
  by_cases hm : edgeCount G = 0
  · simp [hm]
  · have hpos := Nat.pos_of_ne_zero hm
    simp only [List.cons.injEq, and_true, decide_eq_true_eq, true_and]
    refine Or.inr ⟨ColProofs.two_le_of_edge hc hpos, fun t => ?_⟩
    obtain ⟨hcom, hopn⟩ := hget t (lt_of_lt_of_le t.isLt hKN)
    have hlv := ColRep.length_chView (colRep_challenge (encGraph G) n (edgeCount G) (List.ofFn r.2)) t
    have hch : colRep_challenge (encGraph G) n (edgeCount G) (List.ofFn r.2) t =
        edgeMsg (sampleEdgeIdx (edgeCount G) (encGraph G).length
          (colCoinSlice (((encGraph G).length + 1) ^ 2) t (List.ofFn r.2))) := if_pos t.isLt
    rw [hcom, hopn, colRep_proverRep_next Com ℓ hx _ _ _ (by rw [hlv]; omega),
      colRep_proverRep_next Com ℓ hx _ _ _
        (by rw [List.length_append, hlv, List.length_singleton]; omega),
      List.length_append, hlv, List.length_singleton, List.getLastD_concat,
      if_pos (by omega : 2 * (t : ℕ) % 2 = 0), if_neg (by omega : ¬ (2 * (t : ℕ) + 1) % 2 = 0),
      show 2 * (t : ℕ) / 2 = t by omega, show (2 * (t : ℕ) + 1) / 2 = t by omega, hch,
      colProver_next_nil Com ℓ hx, colProver_next_cons Com ℓ hx hpos, decColoring_encColoring]
    have he := sampleEdgeIdx_lt hpos (encGraph G).length
      (colCoinSlice (((encGraph G).length + 1) ^ 2) t (List.ofFn r.2))
    simp only [edgeIdxOfMsg_edgeMsg he]
    exact colVerify_honest Com hc _ _ (ColMachines.edgeAt_eq_some_of_pos G hpos _)

/-! ### The `n|E|`-fold protocol: soundness -/

/-- **The acceptance bound of the `n|E|`-fold protocol** [PS10, proof of Proposition 127.6]
(Claim-127.h): on a well-formed `x` decoding to a non-colourable `G` on `n ≥ 2` vertices, every
prover is accepted with probability at most `(1 - 1/|E|)^{n|E|} + n|E| (1/2)^{|x|}`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`). By `colRep_views`
and `colRep_verifierRep_next_end`, acceptance is the event that every iteration `t < n|E|`
passes `colVerify` on the edge sampled from coin block `t`, the prover's commitment on its view
`chView ch t` and its opening on `chView ch t ++ [ch t]`; through `ColRep.blockRead`
(`ColRep.drop_take_ofFn_blockRead`) this is a test `T` of the `n|E|` sampled edges `Φ rV`. The
sampled edges are `n|E| (1/2)^{|x|}`-close to uniform (`ColRep.statClose_edgeBlocks`,
`StatClose.abs_uprob_sub_le_prod`), and under uniform edges `T` has probability at most
`(1 - 1/|E|)^{n|E|}` (`uprob_col_cheat_le`, the prover's view rebuilt from the earlier
challenges by `ColRep.chView_congr`). -/
private theorem colRep_accept_le {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩)
    (hwf : colWellFormed x = true) (hKN : n * edgeCount G ≤ x.length * x.length)
    (hmx : edgeCount G ≤ x.length) (hn : 2 ≤ n) (hG : ¬ ThreeColorable G) (P' : Strategy)
    (z : List Bool) :
    uprob (fun r : (colProtocolRep Com ℓ).ExecCoins P' x =>
        ¬ (colProtocolRep Com ℓ).outV P' x [] z r = [false]) ≤
      (1 - 1 / (edgeCount G : ℝ)) ^ (n * edgeCount G) +
        ((n * edgeCount G : ℕ) : ℝ) * (1 / 2 : ℝ) ^ x.length := by
  have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hG
  have hcoin : (colVerifierRep Com ℓ).coinLen x.length =
      x.length * x.length * (1 * (x.length + 1) ^ 2) := by
    rw [Strategy.coinLen_eq]
    show (PolyExpr.mul (.mul .var .var) (.normal 1 2)).eval x.length = _
    rw [PolyExpr.eval_mul, PolyExpr.eval_mul, PolyExpr.eval_var, PolyExpr.eval_normal]
  have hKb : n * edgeCount G * (x.length + 1) ^ 2 ≤ (colVerifierRep Com ℓ).coinLen x.length := by
    rw [hcoin, one_mul]
    exact Nat.mul_le_mul_right _ hKN
  have hsz : x.length * Nat.size (edgeCount G) ≤ (x.length + 1) ^ 2 := by
    have h1 : Nat.size (edgeCount G) ≤ x.length :=
      (Nat.size_le_size hmx).trans (Nat.size_le.2 Nat.lt_two_pow_self)
    calc x.length * Nat.size (edgeCount G) ≤ x.length * x.length := Nat.mul_le_mul_left _ h1
      _ ≤ (x.length + 1) ^ 2 := by nlinarith
  obtain ⟨rP, hrP⟩ :=
    (colProtocolRep Com ℓ).exists_proverCoins_le P' x [] z fun o => ¬ o = [false]
  refine hrP.trans ?_
  -- the sampled edges as a function of the verifier's tape
  let Φ : (colVerifierRep Com ℓ).Coins x.length → Fin (n * edgeCount G) → Fin (edgeCount G) :=
    fun rV t => ⟨sampleEdgeIdx (edgeCount G) x.length
      (List.ofFn (ColRep.blockRead ((x.length + 1) ^ 2) (n * edgeCount G) _ hKb rV t)),
      sampleEdgeIdx_lt hm _ _⟩
  have hΦ : ∀ (rV : (colVerifierRep Com ℓ).Coins x.length) (k : ℕ) (hk : k < n * edgeCount G),
      ((Φ rV ⟨k, hk⟩ : Fin (edgeCount G)) : ℕ) =
        sampleEdgeIdx (edgeCount G) x.length
          (colCoinSlice ((x.length + 1) ^ 2) k (List.ofFn rV)) := by
    intro rV k hk
    show sampleEdgeIdx (edgeCount G) x.length (List.ofFn (ColRep.blockRead _ _ _ hKb rV ⟨k, hk⟩)) = _
    rw [colCoinSlice_eq, ← ColRep.drop_take_ofFn_blockRead _ _ _ hKb rV ⟨k, hk⟩]
  -- the prover's messages as functions of the earlier challenges
  let comF : (i : Fin (n * edgeCount G)) → (Fin i → Fin (edgeCount G)) → Unit → List Bool :=
    fun i h _ => P'.next x [] (List.ofFn rP)
      (ColRep.chView (fun j => if hj : j < i then edgeMsg (h ⟨j, hj⟩) else []) i)
  let opnF : (i : Fin (n * edgeCount G)) → (Fin (i + 1) → Fin (edgeCount G)) → Unit → List Bool :=
    fun i h _ => P'.next x [] (List.ofFn rP)
      (ColRep.chView (fun j => if hj : j < i then edgeMsg (h ⟨j, by omega⟩) else []) i ++
        [edgeMsg (h (Fin.last i))])
  let T : (Fin (n * edgeCount G) → Fin (edgeCount G)) → Unit → Prop := fun es w => ∀ i,
    colVerify Com (ℓ.eval n) G (es i) (comF i (challengesBefore es i) w)
      (opnF i (challengesUpTo es i) w) = true
  have hev : ∀ rV : (colProtocolRep Com ℓ).V.Coins x.length,
      (¬ (colProtocolRep Com ℓ).outV P' x [] z (rP, rV) = [false]) ↔ T (Φ rV) () := by
    intro rV
    obtain ⟨hlen, hget⟩ := colRep_views Com ℓ hx P' [] z (List.ofFn rP) (List.ofFn rV)
    rw [colRep_outV]
    show ¬ (colVerifierRep Com ℓ).next x z (List.ofFn rV)
      (exec P' (colVerifierRep Com ℓ) false x [] z (List.ofFn rP) (List.ofFn rV) _).2 = _ ↔ _
    rw [colRep_verifierRep_next_end Com ℓ hx z _ _ hlen, hwf]
    simp only [List.cons.injEq, and_true, decide_eq_false_iff_not, not_not, true_and,
      or_iff_right hm.ne', and_iff_right hn]
    refine forall_congr' fun t => ?_
    obtain ⟨hcom, hopn⟩ := hget t (lt_of_lt_of_le t.isLt hKN)
    have hpre : ∀ k (hk : k < (t : ℕ)), colRep_challenge x n (edgeCount G) (List.ofFn rV) k =
        edgeMsg (Φ rV ⟨k, lt_trans hk t.isLt⟩) := by
      intro k hk
      rw [hΦ rV k (lt_trans hk t.isLt)]
      exact if_pos (lt_trans hk t.isLt)
    have hcur : colRep_challenge x n (edgeCount G) (List.ofFn rV) t = edgeMsg (Φ rV t) := by
      rw [hΦ rV t t.isLt]
      exact if_pos t.isLt
    rw [hcom, hopn, ← hΦ rV t t.isLt]
    show colVerify Com (ℓ.eval n) G (Φ rV t) _ _ = true ↔ colVerify Com (ℓ.eval n) G (Φ rV t)
      (P'.next x [] (List.ofFn rP) (ColRep.chView (fun j => if hj : j < t then
        edgeMsg (Φ rV (Fin.castLE t.isLt.le ⟨j, hj⟩)) else []) t))
      (P'.next x [] (List.ofFn rP) (ColRep.chView (fun j => if hj : j < t then
        edgeMsg (Φ rV (Fin.castLE t.isLt ⟨j, by omega⟩)) else []) t ++
          [edgeMsg (Φ rV (Fin.castLE t.isLt (Fin.last t)))])) = true
    have hlast : Φ rV (Fin.castLE t.isLt (Fin.last t)) = Φ rV t := congrArg (Φ rV) (Fin.ext rfl)
    have h1 : ColRep.chView (fun j => if hj : j < (t : ℕ) then
        edgeMsg (Φ rV (Fin.castLE t.isLt.le ⟨j, hj⟩)) else []) t =
          ColRep.chView (colRep_challenge x n (edgeCount G) (List.ofFn rV)) t :=
      ColRep.chView_congr t fun k hk => by rw [dif_pos hk, hpre k hk]; rfl
    have h2 : ColRep.chView (fun j => if hj : j < (t : ℕ) then
        edgeMsg (Φ rV (Fin.castLE t.isLt ⟨j, by omega⟩)) else []) t =
          ColRep.chView (colRep_challenge x n (edgeCount G) (List.ofFn rV)) t :=
      ColRep.chView_congr t fun k hk => by rw [dif_pos hk, hpre k hk]; rfl
    rw [hlast, ← hcur, h1, h2]
  have hclose := ColRep.statClose_edgeBlocks hm x.length ((x.length + 1) ^ 2) (n * edgeCount G) _
    hsz hKb
  have hcheat := uprob_col_cheat_le hC hn hG (n * edgeCount G) (W := Unit) comF opnF
  calc uprob (fun rV : (colProtocolRep Com ℓ).V.Coins x.length =>
          ¬ (colProtocolRep Com ℓ).outV P' x [] z (rP, rV) = [false])
      = uprob (fun rV : (colVerifierRep Com ℓ).Coins x.length => T (Φ rV) ()) :=
        OneWay.uprob_congr hev
    _ = uprob (fun w : (colVerifierRep Com ℓ).Coins x.length × Unit => T (Φ w.1) w.2) :=
        (HardcoreBit.pushesUniform_fst.uprob_eq fun rV => T (Φ rV) ()).symm
    _ ≤ uprob (fun w : (Fin (n * edgeCount G) → Fin (edgeCount G)) × Unit => T (id w.1) w.2) +
          ((n * edgeCount G : ℕ) : ℝ) * (1 / 2 : ℝ) ^ x.length := by
        have := (abs_le.1 (hclose.abs_uprob_sub_le_prod T)).2
        linarith
    _ ≤ _ := by
        gcongr
        exact hcheat

/-- **Soundness of the `n|E|`-fold protocol** [PS10, Proposition 127.6]: for `x ∉ 3COL` and every
prover the verifier rejects with probability greater than
`1 - (e^{-√|x|} + |x|² 2^{-|x|} + 2^{-|x|})`.

**Proof sketch.** If `x` is ill formed, or `n < 2` (then `E ≠ ∅` since `G` is not colourable),
the verdict is `[false]` on every tape (`colRep_views`, `colRep_verifierRep_next_end`).
Otherwise `colRep_accept_le` with `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`),
`n = √|x|` (`length_encGraph`, `Nat.sqrt_eq`) and `n|E| ≤ |x|²` (`ColRep.mul_edgeCount_le`); the
last term `2^{-|x|} > 0` makes the inequality strict. -/
private theorem colRep_sound {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    (x : List Bool) (hx : x ∉ L3COL) (P' : Strategy) (z : List Bool) :
    1 - (Real.exp (-(Nat.sqrt x.length : ℝ)) + (x.length : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ x.length +
        (2 : ℝ)⁻¹ ^ x.length) <
      uprob (fun r : (colProtocolRep Com ℓ).ExecCoins P' x =>
        (colProtocolRep Com ℓ).outV P' x [] z r = [false]) := by
  have hpos2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
  have hexp : 0 < Real.exp (-(Nat.sqrt x.length : ℝ)) := Real.exp_pos _
  have hsq : (0 : ℝ) ≤ (x.length : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ x.length := by positivity
  suffices key : uprob (fun r : (colProtocolRep Com ℓ).ExecCoins P' x =>
      ¬ (colProtocolRep Com ℓ).outV P' x [] z r = [false]) ≤
        Real.exp (-(Nat.sqrt x.length : ℝ)) + (x.length : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ x.length by
    rw [uprob_not] at key
    linarith
  set n := (decGraph x).1 with hn_def
  set G := (decGraph x).2 with hG_def
  have hx' : decGraph x = ⟨n, G⟩ := rfl
  -- the outright rejections
  have hreject : ¬ (colWellFormed x = true ∧ (edgeCount G = 0 ∨ 2 ≤ n)) →
      uprob (fun r : (colProtocolRep Com ℓ).ExecCoins P' x =>
        ¬ (colProtocolRep Com ℓ).outV P' x [] z r = [false]) ≤
          Real.exp (-(Nat.sqrt x.length : ℝ)) + (x.length : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ x.length := by
    intro hno
    have hall : ∀ r : (colProtocolRep Com ℓ).ExecCoins P' x,
        ¬ ¬ (colProtocolRep Com ℓ).outV P' x [] z r = [false] := by
      intro r
      obtain ⟨hlen, -⟩ := colRep_views Com ℓ hx' P' [] z (List.ofFn r.1) (List.ofFn r.2)
      rw [not_not, colRep_outV, colRep_verifierRep_next_end Com ℓ hx' z _ _ hlen]
      simp only [List.cons.injEq, and_true, decide_eq_false_iff_not]
      exact fun h => hno ⟨h.1, h.2.imp id fun h' => h'.1⟩
    rw [OneWay.uprob_congr fun r => iff_of_false (hall r) not_false, uprob_false]
    positivity
  by_cases hwf : colWellFormed x = true
  · have hxG : x = encGraph G := of_decide_eq_true hwf
    have hnc : ¬ ThreeColorable G := fun h => hx (hxG ▸ (encGraph_mem_L3COL_iff G).2 h)
    have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hnc
    by_cases hn : 2 ≤ n
    · have hlen : x.length = n * n := by rw [hxG, length_encGraph]
      have hKN : n * edgeCount G ≤ x.length * x.length := by
        have h := ColRep.mul_edgeCount_le G
        rwa [← hxG] at h
      have hmx : edgeCount G ≤ x.length := by
        rw [ColMachines.edgeCount_eq G x (ColMachines.decGraph_apply x), hlen]
        exact ColMachines.countTrue_le _ _
      refine (colRep_accept_le hC hx' hwf hKN hmx hn hnc P' z).trans ?_
      have hsqrt : Nat.sqrt x.length = n := by rw [hlen, Nat.sqrt_eq]
      have h1 := one_sub_inv_pow_mul_le_exp (edgeCount G) n hm
      have h2 : ((n * edgeCount G : ℕ) : ℝ) ≤ (x.length : ℝ) ^ 2 := by
        rw [sq]
        exact_mod_cast hKN
      have h3 : ((n * edgeCount G : ℕ) : ℝ) * (1 / 2 : ℝ) ^ x.length ≤
          (x.length : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ x.length := by
        rw [one_div]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      rw [hsqrt]
      linarith
    · exact hreject fun h => hn (h.2.resolve_left hm.ne')
  · exact hreject fun h => hwf h.1

theorem colRep_efficientProverProof_sealed {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL where
  efficientV := colVerifierRep_efficient hC.easy ℓ
  complete := by
    obtain ⟨B, -, hB⟩ := colProtocol_proverBounded hC R3COL
    refine ⟨B, fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := (mem_L3COL_iff x).1 hx
    obtain ⟨n, G, c, rfl, rfl, hc⟩ := (R3COL_iff _ _).1 hy
    exact ⟨encColoring c, fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist hy,
      fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colRep_outV_honest hc z r⟩
  sound := by
    refine ⟨fun N => Real.exp (-(Nat.sqrt N : ℝ)) + (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ N + (2 : ℝ)⁻¹ ^ N,
      ?_, fun x hx P' z => colRep_sound hC x hx P' z⟩
    have h1 : Negligible fun N => Real.exp (-(Nat.sqrt N : ℝ)) := by
      simpa only [Nat.div_one] using negligible_exp_neg_sqrt_div (C := 1) one_pos
    exact (h1.add (negligible_two_pow_neg.mul_pow 2)).add negligible_two_pow_neg
  efficientP := colProverRep_efficient hC.easy ℓ
  boundedP := (colProtocol_proverBounded hC R3COL).imp fun _ h => h.2
  completeWitness := by
    intro x y hy z
    obtain ⟨n, G, c, rfl, rfl, hc⟩ := (R3COL_iff _ _).1 hy
    exact HardcoreBit.uprob_eq_one_of_forall fun r => colRep_outV_honest hc z r


/-- The decidable clause of `R3COL_witnessRelation`, as filled. -/
theorem R3COL_decidable_sealed : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R3COL x y :=
  ColRep.R3COL_decidable

end TCSlib.Cryptography.SealA
