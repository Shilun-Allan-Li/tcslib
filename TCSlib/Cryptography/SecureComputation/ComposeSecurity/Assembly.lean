/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Assembling a view of the composed protocol from views of the runs

The post-processing of the simulators and reductions of the composition theorem
[Gol04, §7.3.1, proof of Theorem 7.3.3]: a party's view of `H.compose ρ` is its common input, its
input, its tape (the `main`-tape followed by one `ρ`-tape per run) and its received messages
(the other party's run messages at the pairs, with fillers, the leading fillers and the main
phase). Given a word `V j` per run that reads as an encoded view of `ρ`
(`⟨⟨x, z⟩, ⟨r, encodeMsgs received⟩⟩`, `View.encode`), `asmView` assembles such a view: the run
tapes are cut or padded to `ρ`'s coin length, and the received run messages are placed at the
pairs where the other party moves (the `k`-th message received at the `k`-th such pair, `p / 2`).

## Main definitions

* `ComposeSim.segW`: the pair chunks of one run, from the run's encoded received messages.
* `ComposeSim.asmView`: the assembled encoded view; `ComposeSim.asmW` its word form.

## Main results

* `ComposeSim.moverIsV_beq_iff`, `length_filter_mover`, `getD_filter_map_mover`: the parity of
  the pairs at which a party moves, and the position of a run message among them.
* `ComposeSim.polyTimeComputable_asmW`: the assembly is polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

/-! ### The pairs at which a party moves -/

/-- **The mover test is a parity**: `moverIsV vF q == b` iff `q % 2 = (if vF == b then 0 else 1)`
(`moverIsV_def`). -/
theorem moverIsV_beq_iff (vF b : Bool) (q : ℕ) :
    (moverIsV vF q == b) = true ↔ q % 2 = (if vF == b then 0 else 1) := by
  rw [moverIsV_def]
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> cases vF <;> cases b <;> simp [h]

/-- The number of `q < p` with `q % 2 = d` (for `d ≤ 1`) is `(p + 1 − d) / 2`. -/
theorem length_filter_mod_two {d : ℕ} (hd : d ≤ 1) :
    ∀ p, ((List.range p).filter fun q => q % 2 == d).length = (p + 1 - d) / 2
  | 0 => by
    rw [List.range_zero, List.filter_nil, List.length_nil]
    omega
  | p + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_mod_two hd p,
      List.filter_singleton]
    by_cases h : p % 2 = d
    · rw [show (p % 2 == d) = true from beq_iff_eq.2 h, cond_true, List.length_singleton]
      omega
    · rw [show (p % 2 == d) = false from beq_eq_false_iff_ne.2 h, cond_false, List.length_nil]
      omega

/-- **The number of moves of a party before its move `p`** is `p / 2`: if
`moverIsV vF p == b`, then `|{q < p : moverIsV vF q == b}| = p / 2` (`moverIsV_beq_iff`,
`length_filter_mod_two`). -/
theorem length_filter_mover (vF b : Bool) {p : ℕ} (hp : (moverIsV vF p == b) = true) :
    ((List.range p).filter fun q => moverIsV vF q == b).length = p / 2 := by
  have hd : (if vF == b then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hpar := (moverIsV_beq_iff vF b p).1 hp
  have hfilt : ((List.range p).filter fun q => moverIsV vF q == b) =
      (List.range p).filter fun q => q % 2 == (if vF == b then 0 else 1) := by
    refine List.filter_congr fun q _ => ?_
    rw [Bool.eq_iff_iff, moverIsV_beq_iff]
    exact beq_iff_eq.symm
  rw [hfilt, length_filter_mod_two hd]
  split_ifs at hpar ⊢ <;> omega

/-- **A run message at its position**: for `p < R` with `moverIsV vF p == b`, entry `p / 2` of
the messages `f q` at the `q < R` with `moverIsV vF q == b` is `f p`
(`length_filter_mover`). -/
theorem getD_filter_map_mover (vF b : Bool) (f : ℕ → List Bool) {R p : ℕ} (hpR : p < R)
    (hp : (moverIsV vF p == b) = true) :
    (((List.range R).filter fun q => moverIsV vF q == b).map f).getD (p / 2) [] = f p := by
  obtain ⟨d, rfl⟩ : ∃ d, R = p + 1 + d := ⟨R - (p + 1), by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append,
    List.filter_singleton, hp, cond_true, List.map_append, List.map_append, List.map_singleton,
    List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
      rw [List.length_map, length_filter_mover vF b hp]), List.length_map,
    length_filter_mover vF b hp, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
    Option.getD_some]

/-- Padding a word of the right length is the identity: `|w| = L → padTo L w = w`. -/
theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) : padTo L w = w := by
  rw [padTo_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- A concatenation over `range a` is one over `range b` when `a = b` (no rewriting inside the
chunks): `a = b → (range a).flatMap f = (range b).flatMap f`. -/
theorem flatMap_range_congr {a b : ℕ} (h : a = b) (f : ℕ → List Bool) :
    (List.range a).flatMap f = (List.range b).flatMap f := by
  subst h
  rfl

/-! ### One run's chunks -/

/-- **The pair chunks of one run**, from the encoded received messages `e` of the run's view:
for `p < R`, the chunk `⟨m_p, []⟩` with `m_p` the message received at the `p / 2`-th of the pairs
where the other party moves (`moverIsV vF p == b`) and `[]` (a filler) at the others:
`segW vF b R e = (range R).flatMap fun p =>
⟨if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else [], []⟩`. -/
def segW (vF b : Bool) (R : ℕ) (e : List Bool) : List Bool :=
  (List.range R).flatMap fun p =>
    pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) []

/-- The defining equation of `segW` (see `segW`).
`segW vF b R e = (List.range R).flatMap fun p => pairEncode (if moverIsV vF p == b then pairFstD
(pairSndD^[p / 2] e) else []) []`. -/
theorem segW_eq (vF b : Bool) (R : ℕ) (e : List Bool) :
    segW vF b R e = (List.range R).flatMap fun p =>
      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] := rfl

/-- **`segW` on a real run**: if the run's received messages are the messages `f q` at the
`q < R` with `moverIsV vF q == b`, the chunks are `⟨f p, []⟩` at those pairs and `⟨[], []⟩` at
the others:
`segW vF b R (encodeMsgs (filter … (range R)).map f) =
(range R).flatMap fun p => ⟨if moverIsV vF p == b then f p else [], []⟩`
(`msgAt_encodeMsgs`, `getD_filter_map_mover`). -/
theorem segW_encodeMsgs (vF b : Bool) (R : ℕ) (f : ℕ → List Bool) :
    segW vF b R (Strategy.encodeMsgs (((List.range R).filter fun q => moverIsV vF q == b).map f)) =
      (List.range R).flatMap fun p =>
        pairEncode (if moverIsV vF p == b then f p else []) [] := by
  rw [segW_eq]
  refine List.flatMap_congr fun p hp => ?_
  by_cases h : (moverIsV vF p == b) = true
  · rw [if_pos h, if_pos h, msgAt_encodeMsgs, getD_filter_map_mover vF b f (List.mem_range.1 hp) h]
  · rw [if_neg h, if_neg h]

/-! ### The assembled view -/

/-- **The assembled encoded view** of a party of `H.compose ρ` (`n = |x₁|`, `L = calls(n)`,
`R = rounds(n)`, `c = cρ(n)`), from its common input `x₁`, input `xin`, `main`-tape `mt`, encoded
main-phase messages `me`, the number `lead` of leading fillers it receives, and one word `V j`
per run read as an encoded `ρ`-view: the view `⟨⟨x₁, xin⟩, ⟨mt ++ τ, E⟩⟩` with the tape
`τ = (range L).flatMap fun j => padTo c (tape of V j)` and the messages
`E = (range L).flatMap (fun j => segW vF b R (messages of V j)) ++ encodeMsgs [[]]^lead ++ me`. -/
def asmView (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (x₁ xin mt me : List Bool)
    (V : ℕ → List Bool) : List Bool :=
  pairEncode (pairEncode x₁ xin)
    (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
      ((List.range (calls.eval x₁.length)).flatMap (fun j =>
          segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
        Strategy.encodeMsgs (List.replicate lead []) ++ me))

/-- The defining equation of `asmView` (see `asmView`).
`asmView calls rounds cρ vF b lead x₁ xin mt me V = pairEncode (pairEncode x₁ xin) (pairEncode (mt
++ (List.range (calls.eval x₁.length)).flatMap fun j => padTo (cρ.eval x₁.length) (pairFstD
(pairSndD (V j)))) ((List.range (calls.eval x₁.length)).flatMap (fun j => segW vF b (rounds.eval
x₁.length) (pairSndD (pairSndD (V j)))) ++ Strategy.encodeMsgs (List.replicate lead []) ++ me))`. -/
theorem asmView_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) (V : ℕ → List Bool) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      pairEncode (pairEncode x₁ xin)
        (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
            padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
          ((List.range (calls.eval x₁.length)).flatMap (fun j =>
              segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
            Strategy.encodeMsgs (List.replicate lead []) ++ me)) := rfl

/-- `asmView` depends on the run words only below `L`: if `V j = V' j` for `j < calls(|x₁|)`, the
assembled views agree. -/
theorem asmView_congr (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) {V V' : ℕ → List Bool}
    (h : ∀ j < calls.eval x₁.length, V j = V' j) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      asmView calls rounds cρ vF b lead x₁ xin mt me V' := by
  have h₁ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  have h₂ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  rw [asmView_eq, asmView_eq, h₁, h₂]

/-- **The assembly in word form**: on `w = ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩`, `asmView` with the run
words `V j = pairFstD (pairSndD^[j] VL)` (the entries of an encoded list,
`msgAt_encodeMsgs`). -/
def asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) : List Bool :=
  asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
    (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
    (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))

/-- The defining equation of `asmW` (see `asmW`).
`asmW calls rounds cρ vF b lead w = asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD
w))) (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w))) (pairSndD (pairSndD
(pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))`. -/
theorem asmW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) :
    asmW calls rounds cρ vF b lead w =
      asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
        (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
        (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w)) := rfl

/-- `asmW` on its word: `asmW … ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩ =
asmView … x₁ xin mt me (fun j => pairFstD (pairSndD^[j] VL))`. -/
theorem asmW_pairEncode (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me VL : List Bool) :
    asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode x₁ xin) (pairEncode mt me)) VL) =
      asmView calls rounds cρ vF b lead x₁ xin mt me fun j => pairFstD (pairSndD^[j] VL) := by
  rw [asmW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **`segW` is polynomial-time** on `⟨1^R, e⟩` words given by polynomial-time maps
(`polyTimeComputable_flatMap_range` over `p < R`, the mover test `polyTimeComputable_moverW`,
`p / 2` by `divNum_poly`, the message by `iterSnd_poly`). -/
theorem polyTimeComputable_segW (vF b : Bool) {R : List Bool → ℕ} {e : List Bool → List Bool}
    (hR : PolyTimeComputable fun z => List.replicate (R z) true) (he : PolyTimeComputable e) :
    PolyTimeComputable fun z => segW vF b (R z) (e z) := by
  have hhalf : PolyTimeComputable fun v => List.replicate ((pairFstD v).length / 2) true :=
    (divNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2)).congr
      fun v => by rw [divNum_eq]
  have hmsg := polyTimeComputable_pairFstD.comp'
    (iterSnd_poly (he.comp' polyTimeComputable_pairSndD) hhalf)
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (if moverIsV vF (pairFstD v).length == b then
        pairFstD (pairSndD^[(pairFstD v).length / 2] (e (pairSndD v))) else []) [] :=
    (polyTimeComputable_ite ((polyTimeComputable_moverW vF b).congr fun v => moverW_eq vF b v)
      hmsg (polyTimeComputable_const [])).pairEncode (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range hchunk hR).congr fun z => (segW_eq vF b (R z) (e z)).symm

/-- **The assembly is polynomial-time**: `PolyTimeComputable (asmW calls rounds cρ vF b lead)`.

**Proof sketch.** The components `x₁`, `xin`, `mt`, `me` are projections. The tape part and the
message part are concatenations over the unary count `calls(|x₁|)`
(`polyTimeComputable_flatMap_range`) of a padded tape (`padTo_poly`) and of `segW`
(`polyTimeComputable_segW`) of the run word `pairFstD (pairSndD^[j] VL)` (`iterSnd_poly`),
followed by constant fillers and `me`; the word is `asmView` of these (`asmW_eq`,
`asmView_eq`). -/
theorem polyTimeComputable_asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (asmW calls rounds cρ vF b lead) := by
  have hx₁ : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hxin : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hmt : PolyTimeComputable fun w => pairFstD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  have hme : PolyTimeComputable fun w => pairSndD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  -- the run word `V j` from `v = ⟨1^j, w⟩`
  have hV : PolyTimeComputable fun v =>
      pairFstD (pairSndD^[(pairFstD v).length] (pairSndD (pairSndD v))) :=
    polyTimeComputable_pairFstD.comp' (iterSnd_poly
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))
  have hn : PolyTimeComputable fun v =>
      List.replicate (pairFstD (pairFstD (pairFstD (pairSndD v)))).length true :=
    unaryLength_poly (hx₁.comp' polyTimeComputable_pairSndD)
  have htape : PolyTimeComputable fun v =>
      padTo (cρ.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairFstD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    padTo_poly ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).comp' hV)
      (unaryPolyOf_poly cρ hn)
  have hseg : PolyTimeComputable fun v =>
      segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairSndD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    polyTimeComputable_segW vF b (unaryPolyOf_poly rounds hn)
      ((polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD).comp' hV)
  have hL := unaryPolyOf_poly calls (unaryLength_poly hx₁)
  have hT := polyTimeComputable_flatMap_range (E := fun w j =>
    padTo (cρ.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairFstD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) htape hL
  have hS := polyTimeComputable_flatMap_range (E := fun w j =>
    segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairSndD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) hseg hL
  exact (((hx₁.pairEncode hxin).pairEncode ((hmt.append hT).pairEncode
    ((hS.append (polyTimeComputable_const _)).append hme)))).congr fun w => by
      rw [asmW_eq, asmView_eq]

end TCSlib.Cryptography.SecureComputation.ComposeSim
