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

* **Readers of a round input** `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`rdU`, `rdZ`, `rdW`,
  `rdState`,
  `rdIdx`, `rdQuery`, `rdLog`, `rdAns`), with their values (`fields_input`) and their
  polynomial-time bounds.
* **Seeds made of coins** (`seedEquiv`, `seedEquivPoly`) and padded concatenations.

The calls and finalizations whose rounds return at once or after one outer query are
`Games.InteractiveHandler.impl_of_ret_padFin`, `impl_of_query_padFin` and `finish_of_ret_padFin`;
the cost of a one-shot oracle is `Games.simulate_costBoundedBy_once`.

## Main definitions

* `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns`.
* `NMSim.seedEquiv`, `NMSim.seedEquivPoly`: seeds made of coins.

## Main results

* `NMSim.fields_input`, `NMSim.rdAns_input`, `NMSim.polyTimeComputable_rd`.
* `NMSim.padFin_append_split`.
* `NMSim.seedEquiv_ofFn`, `NMSim.seedEquivPoly_ofFn`, `NMSim.ofFn_padFin_eq_padL`.

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

end TCSlib.Cryptography.Composability.NMSim
