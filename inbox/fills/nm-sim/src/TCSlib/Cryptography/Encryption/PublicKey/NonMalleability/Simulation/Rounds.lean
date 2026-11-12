/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rounds of interactive handlers

Generic facts about T2's interactive handlers (`Games.InteractiveHandler`), used by the two
machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the simulator and the NM adversary).

* **Readers of a round input** `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`rdU`, `rdZ`, `rdW`, `rdState`,
  `rdIdx`, `rdQuery`, `rdLog`, `rdAns`), with their values (`fields_input`) and their
  polynomial-time bounds.
* **One call** whose first round returns (`impl_of_ret`), or asks one outer query and returns in its
  second round (`impl_of_query`); a finalization whose first round returns (`finish_of_ret`).
* **Costs with a one-shot oracle** (`simulate_costBoundedBy_once`): if the calls are free except one
  call, of cost at most one, that marks the state as used, the whole simulation costs at most one.

## Main definitions

* `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns`.
* `NMSim.seedEquiv`, `NMSim.seedEquivPoly`: seeds made of coins.

## Main results

* `NMSim.fields_input`, `NMSim.rdAns_input`, `NMSim.polyTimeComputable_rd`.
* `NMSim.buildComp_of_ret`, `NMSim.impl_of_ret`, `NMSim.impl_of_query`, `NMSim.finish_of_ret`.
* `NMSim.seedEquiv_ofFn`, `NMSim.seedEquivPoly_ofFn`, `NMSim.ofFn_padFin_eq_padL`.
* `NMSim.costBoundedBy_bind_of_allOutputs`, `NMSim.simulate_costBoundedBy_once`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Readers of a round input -/

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
def rdU (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- `rdU w = pairFstD (pairFstD w)`. -/
theorem rdU_eq (w : List Bool) : rdU w = pairFstD (pairFstD w) := rfl

/-- The reduction input `z` of a round input. -/
def rdZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))

/-- `rdZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem rdZ_eq (w : List Bool) : rdZ w = pairFstD (pairSndD (pairFstD w)) := rfl

/-- The seed `ω` of a round input. -/
def rdW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))

/-- `rdW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem rdW_eq (w : List Bool) : rdW w = pairSndD (pairSndD (pairFstD w)) := rfl

/-- The state `s` of a round input. -/
def rdState (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- `rdState w = pairFstD (pairSndD w)`. -/
theorem rdState_eq (w : List Bool) : rdState w = pairFstD (pairSndD w) := rfl

/-- The oracle index `1^i` of a round input. -/
def rdIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))

/-- `rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
theorem rdIdx_eq (w : List Bool) : rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w))) := rfl

/-- The query `x` of a round input. -/
def rdQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))

/-- `rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
theorem rdQuery_eq (w : List Bool) : rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w))) :=
  rfl

/-- The outer log `L` of the call so far. -/
def rdLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- `rdLog w = pairSndD (pairSndD (pairSndD w))`. -/
theorem rdLog_eq (w : List Bool) : rdLog w = pairSndD (pairSndD (pairSndD w)) := rfl

/-- The outer answer `y` of the first entry `⟨1^j, ⟨x, y⟩⟩` of the outer log. -/
def rdAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rdLog w)))

/-- `rdAns w = pairSndD (pairSndD (pairFstD (rdLog w)))`. -/
theorem rdAns_eq (w : List Bool) : rdAns w = pairSndD (pairSndD (pairFstD (rdLog w))) := rfl

section Fields

variable {k : ℕ}

/-- **The fields of a round input** (DL-30–36 overlap: the round-input readers of
`Indistinguishability/Forward.lean`, here with the context): on
`input n z ω s i x L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` the readers return `1^n`, `z`, `ω`,
`s`, `1^i`, `x` and `L`. -/
theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rdU (InteractiveHandler.input n z ω s i x L) = List.replicate n true ∧
      rdZ (InteractiveHandler.input n z ω s i x L) = z ∧
      rdW (InteractiveHandler.input n z ω s i x L) = ω ∧
      rdState (InteractiveHandler.input n z ω s i x L) = s ∧
      rdIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
      rdQuery (InteractiveHandler.input n z ω s i x L) = x ∧
      rdLog (InteractiveHandler.input n z ω s i x L) = L := by
  simp only [InteractiveHandler.input_eq, rdU, rdZ, rdW, rdState, rdIdx, rdQuery, rdLog,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The answer of a one-entry outer log: `rdAns` of a round input with the log
`⟨⟨1^j, ⟨x', y⟩⟩, t⟩` is `y`. -/
theorem rdAns_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) (j : ℕ)
    (x' y t : List Bool) :
    rdAns (InteractiveHandler.input n z ω s i x
      (pairEncode (pairEncode (List.replicate j true) (pairEncode x' y)) t)) = y := by
  rw [rdAns, (fields_input n z ω s i x _).2.2.2.2.2.2, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

end Fields

/-- The round-input readers are polynomial-time: `rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`,
`rdQuery`, `rdLog` and `rdAns`. -/
theorem polyTimeComputable_rd :
    PolyTimeComputable rdU ∧ PolyTimeComputable rdZ ∧ PolyTimeComputable rdW ∧
      PolyTimeComputable rdState ∧ PolyTimeComputable rdIdx ∧ PolyTimeComputable rdQuery ∧
      PolyTimeComputable rdLog ∧ PolyTimeComputable rdAns := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hL : PolyTimeComputable rdLog := hD.comp (hD.comp hD)
  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp hD,
    hF.comp (hF.comp (hD.comp hD)), hD.comp (hF.comp (hD.comp hD)), hL,
    hD.comp (hD.comp (hF.comp hL))⟩

/-! ### Calls and finalizations -/

/-- A final output is the computation at every budget: if `next hist = ret a`, then
`buildComp next t q hist = pure a`. -/
theorem buildComp_of_ret {ι α : Type} {spec : OracleSpec ι} {next : QueryLog spec → Move spec α}
    {t : α} {q : ℕ} {hist : QueryLog spec} {a : α} (h : next hist = .ret a) :
    buildComp next t q hist = .pure a := by
  cases q with
  | zero => exact buildComp_zero_of_ret h
  | succ q => exact buildComp_succ_of_ret h

/-- The two parts of a padded concatenation: if `|u| = d₁`, the first `d₁` bits of
`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v`. -/
theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

section Calls

variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin (H.seedLen.eval n) → Bool)

/-- **A call that returns at once:** if the first round on the inner query `x` to oracle `i` in
state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call answers
`padFin _ u` with the new state `padFin _ v`, asking nothing. -/
theorem impl_of_ret (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
    (hv : v.length = H.stateLen.eval n)
    (hrun : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (u ++ v)) :
    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) := by
  have hw : u ++ v = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) :=
    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq,
    buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) (by
      rw [MachineCodec.encodeLog_nil, hrun]
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) u v hu
  rw [h₁, h₂]

/-- **A call with one outer query:** if the first round asks the outer query `x'` to oracle `j`,
and the second round, with the answer `y` in the outer log, returns `⟨[true], u y ‖ v y⟩`, then
(with `perCall ≥ 1`) the call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))`. -/
theorem impl_of_query (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
    (hpc : 1 ≤ H.perCall.eval n)
    (hrun₀ : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
        [])) = pairEncode [true] (u y ++ v y)) :
    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) := by
  obtain ⟨p, hp⟩ : ∃ p, H.perCall.eval n = p + 1 := ⟨H.perCall.eval n - 1, by omega⟩
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, hp,
    buildComp_succ_of_query (i := j) (x := x') (by
      rw [MachineCodec.encodeLog_nil, hrun₀]
      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x'),
    OracleComp.query_bind]
  congr 1
  funext y
  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      bitCodec_encodeEntry]
  have hw : u y ++ v y = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) :=
    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
  rw [buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) (by
      rw [hlog, hrun₁]
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) (u y) (v y) (hu y)
  rw [h₁, h₂]

/-- **A finalization that returns at once:** if its first round returns `⟨[true], b⟩` with
`|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing. -/
theorem finish_of_ret (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (b : List Bool) (hb : b.length = H.outLen.eval n)
    (hrun : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
      []) = pairEncode [true] b) :
    H.finish n z ω s a = .pure (padFin _ b) := by
  rw [InteractiveHandler.finish_eq]
  refine buildComp_of_ret ?_
  rw [MachineCodec.encodeLog_nil, hrun]
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w))
    (GGMRed.ofFn_padFin_of_length hb).symm).trans (decodeBitMove_ret _ _ _ _)

end Calls

/-! ### Seeds and padding -/

/-- **A seed of two machines' coins:** for `L = A.coins + B.coins`,
`A.Coins n × B.Coins n ≃ {0,1}^{L(n)}`, concatenating the two coin strings (`seedEquiv_ofFn`). -/
def seedEquiv {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ) :
    A.Coins n × B.Coins n ≃ (Fin (L.eval n) → Bool) :=
  ((NUPPT.coinsEquivPoly rfl n).prodCongr (NUPPT.coinsEquivPoly rfl n)).trans
    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))

/-- The seed is the concatenation of the coins: `⟦seedEquiv h n (r₁, r₂)⟧ = ⟦r₁⟧ ++ ⟦r₂⟧`. -/
theorem seedEquiv_ofFn {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ)
    (c : A.Coins n × B.Coins n) :
    List.ofFn (seedEquiv h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [seedEquiv, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, NUPPT.coinsEquivPoly_ofFn]

/-- **A seed of a machine's coins and a string:** for `L = A.coins + L₂`,
`A.Coins n × {0,1}^{L₂(n)} ≃ {0,1}^{L(n)}`, concatenating (`seedEquivPoly_ofFn`). -/
def seedEquivPoly {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ) :
    A.Coins n × (Fin (L₂.eval n) → Bool) ≃ (Fin (L.eval n) → Bool) :=
  ((NUPPT.coinsEquivPoly rfl n).prodCongr (Equiv.refl _)).trans
    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))

/-- The seed is the concatenation: `⟦seedEquivPoly h n (r, w)⟧ = ⟦r⟧ ++ ⟦w⟧`. -/
theorem seedEquivPoly_ofFn {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ)
    (c : A.Coins n × (Fin (L₂.eval n) → Bool)) :
    List.ofFn (seedEquivPoly h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [seedEquivPoly, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, Equiv.refl_apply]

/-- A machine's coins have `coins(n)` bits: `|⟦r⟧| = A.coins.eval n`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

/-- `⟦padFin k a⟧ = padL k a` (DL-30–36 overlap: the private `ofFn_padFin_eq_padL` of
`AdaptiveCPA/Handler.lean`, from the public `ofFn_padFin_eq_take`). -/
theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-! ### Costs with a one-shot oracle -/

section Cost

variable {ι ι' σ α β : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- **Costs add under sequencing, on the possible outputs:** if `c` fits in `q₁`, every possible
output of `c` satisfies `P`, and `f a` fits in `q₂` for every `a` with `P a`, then `c` followed by
`f` fits in `q₁ + q₂`. -/
theorem costBoundedBy_bind_of_allOutputs {cost : ι → ℕ} {c : OracleComp spec α}
    {f : α → OracleComp spec β} {P : α → Prop} {q₁ q₂ : ℕ} (hc : c.CostBoundedBy cost q₁)
    (hP : c.AllOutputs P) (hf : ∀ a, P a → (f a).CostBoundedBy cost q₂) :
    (c.bind f).CostBoundedBy cost (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a =>
    rw [OracleComp.pure_bind]
    exact (hf a (OracleComp.allOutputs_pure.1 hP)).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    rw [OracleComp.query_bind]
    refine (OracleComp.costBoundedBy_query _ _ _ _ _).2
      ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y) (OracleComp.allOutputs_query.1 hP y)

/-- **A one-shot oracle costs at most one query in total.** Let `good` be an invariant of the
states and `used` mark the states after the costly call. If from a good used state every call is
free and keeps the state good and used, and from a good unused state every call is either free and
keeps the state good and unused, or costs at most `1` and leaves it good and used, then the
simulation of any computation from a good state costs at most `0` (used) or `1` (unused).

**Proof sketch.** Induction on the computation; at a query, `costBoundedBy_bind_of_allOutputs`
with the call's cost and the continuation's (`0 + 0`, `0 + 1` or `1 + 0`). -/
theorem simulate_costBoundedBy_once (impl : QueryImpl spec σ spec') (cost : ι' → ℕ)
    (good used : σ → Prop) [DecidablePred used]
    (hused : ∀ i x s, good s → used s →
      (impl i x s).CostBoundedBy cost 0 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2)
    (hfresh : ∀ i x s, good s → ¬ used s →
      ((impl i x s).CostBoundedBy cost 0 ∧
          (impl i x s).AllOutputs fun p => good p.2 ∧ ¬ used p.2) ∨
        ((impl i x s).CostBoundedBy cost 1 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2))
    (c : OracleComp spec α) :
    ∀ s, good s → (simulate impl c s).CostBoundedBy cost (if used s then 0 else 1) := by
  induction c with
  | pure a =>
    intro s _
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    intro s hs
    rw [simulate_query]
    by_cases hu : used s
    · obtain ⟨h₀, hP⟩ := hused i x s hs hu
      have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
        have h := ih p.1 p.2 hp.1
        rwa [if_pos hp.2] at h
      rwa [if_pos hu]
    · rw [if_neg hu]
      rcases hfresh i x s hs hu with ⟨h₀, hP⟩ | ⟨h₁, hP⟩
      · have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_neg hp.2] at h
        rwa [Nat.zero_add] at this
      · exact costBoundedBy_bind_of_allOutputs h₁ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_pos hp.2] at h

end Cost

end TCSlib.Cryptography.Composability.NMSim
