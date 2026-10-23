/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ZeroPPIT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PIT reduces to ZEROP

[AB09, §7.2.3, p.129]: deciding whether two circuits `C, C′` compute the same polynomial
reduces to `ZEROP` through the circuit `D = C − C′`. The mathematical identity is
`Randomized.AlgCircuit.toMvPolynomial_subCircuit`; here the map `⟨C, C′⟩ ↦ code(C − C′)` is
computed on words in polynomial time, giving a Karp reduction `PITLang ≤ₚ ZEROP`. Since `coRP`
is closed under `≤ₚ`, `PITLang ∈ coRP` follows from `ZEROP ∈ coRP`.

## Main definitions

* `Randomized.PIT.shiftRun` — re-encode a node list with every node index shifted by `m`.
* `Randomized.PIT.subW` — the code of `C − C′` from the codes of `C` and `C′`.
* `Randomized.pitToZerop` — the reduction (`[]` off well-formed pairs).

## Main results

* `Randomized.PIT.subW_eq` — `subW` is the code of `C.subCircuit C′`.
* `Randomized.polyTimeComputable_pitToZerop`, `Randomized.mem_PITLang_iff_pitToZerop`,
  `Randomized.PITLang_le_ZEROP` — [AB09, §7.2.3]: `PIT ≤ₚ ZEROP`.
* `Randomized.coRP_PTM_of_polyTimeReducible` — `coRP` is closed under `≤ₚ` (PTM form, from
  `Randomized.InCoRP.of_polyTimeReducible`).
* `Randomized.PITLang_mem_coRP_PTM_of_reduction` — `PIT ∈ coRP` through the reduction.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing AlgCircuit BinArith

namespace PIT

variable {n : ℕ}

/-! ### Re-encoding a node list with shifted indices -/

/-- The concatenated node codes of a node list (its code without the final `0`). -/
def gatesBody (gs : List (AlgGate n)) : List Bool := gs.flatMap fun g => true :: g.encode

/-- A node-list code is its body followed by `0`. -/
theorem encodeGates_eq (gs : List (AlgGate n)) : encodeGates gs = gatesBody gs ++ [false] := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [encodeGates, gatesBody, ih]

/-- Shifting by `0` is the identity. -/
@[simp]
theorem _root_.Randomized.AlgGate.shift_zero :
    (AlgGate.shift 0 : AlgGate n → AlgGate n) = id := by
  funext g; cases g <;> rfl

/-- The node at the front of `w`, re-encoded with its node indices shifted by `|M|`. -/
def shiftGateW (M w : List Bool) : List Bool :=
  if isVarW w then [true, false, false, false] ++ arg1W w ++ [false]
  else if isOneW w then [true, false, false, true]
  else [true, tagBit 1 w, tagBit 2 w, tagBit 3 w] ++ M ++ arg1W w ++ [false] ++ M ++
    arg2W w ++ [false]

/-- One round of the shifting loop on `⟨M, ⟨w, out⟩⟩`: a stopped code is fixed; otherwise the
front node of `w` is consumed and its shifted code appended to `out`. -/
def shStep (D : List Bool) : List Bool :=
  if isDone (sW D) then D
  else pairEncode (pairFstD D) (pairEncode (restW (sW D))
    (pairSndD (pairSndD D) ++ shiftGateW (pairFstD D) (sW D)))

/-- **The shifting loop** on `⟨M, G⟩`: `|⟨M, G⟩| + 1` rounds from `⟨M, ⟨G, []⟩⟩`, returning
the output. -/
def shiftRun (z : List Bool) : List Bool :=
  pairSndD (pairSndD (shStep^[1 * (z.length + 1) ^ 1]
    (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))

/-- One round consumes a node and appends its shifted code. -/
theorem shStep_cons (m : ℕ) (g : AlgGate n) (gs : List (AlgGate n)) (out : List Bool) :
    shStep (pairEncode (List.replicate m true) (pairEncode (encodeGates (g :: gs)) out)) =
      pairEncode (List.replicate m true)
        (pairEncode (encodeGates gs) (out ++ true :: (g.shift m).encode)) := by
  have hr : ∀ j : ℕ, BoolCircuit.encodeNat (j + m) =
      List.replicate m true ++ BoolCircuit.encodeNat j := fun j => by
    rw [BoolCircuit.encodeNat, BoolCircuit.encodeNat, Nat.add_comm, List.replicate_add,
      List.append_assoc]
  cases g <;>
    simp [shStep, sW, encodeGates, AlgGate.encode, AlgGate.shift, isDone, isNilB, isVarW,
      isOneW, tagBit, restW, midW, rest2W, bodyW, arg1W, arg2W, shiftGateW, uHead_encodeNat,
      uRest_encodeNat, hr] <;>
    simp only [List.replicate_add, BoolCircuit.encodeNat, List.append_assoc, List.cons_append,
      List.nil_append]

/-- The rounds after the end of a node list are idle. -/
theorem shStep_nil (M out : List Bool) :
    shStep (pairEncode M (pairEncode (encodeGates ([] : List (AlgGate n))) out)) =
      pairEncode M (pairEncode (encodeGates ([] : List (AlgGate n))) out) := by
  simp [shStep, sW, encodeGates, isDone, isNilB]

/-- `|gs|` rounds and more re-encode a node list. -/
theorem iterate_shStep (m : ℕ) :
    ∀ (gs : List (AlgGate n)) (out : List Bool) (T : ℕ), gs.length ≤ T →
      shStep^[T] (pairEncode (List.replicate m true) (pairEncode (encodeGates gs) out)) =
        pairEncode (List.replicate m true) (pairEncode [false]
          (out ++ gatesBody (gs.map (AlgGate.shift m))))
  | [], out, T, _ => by
    rw [Function.iterate_fixed (shStep_nil _ _)]
    simp [encodeGates, gatesBody]
  | g :: gs, out, T, hT => by
    obtain ⟨T, rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by simp at hT; omega⟩
    rw [Function.iterate_succ_apply, shStep_cons,
      iterate_shStep m gs _ T (by simp at hT; omega)]
    simp [gatesBody]

/-- **The shifting loop re-encodes a node list** with every node index shifted by `m`. -/
theorem shiftRun_eq (m : ℕ) (gs : List (AlgGate n)) :
    shiftRun (pairEncode (List.replicate m true) (encodeGates gs)) =
      gatesBody (gs.map (AlgGate.shift m)) := by
  have h := length_encodeGates gs
  rw [shiftRun, pairFstD_pairEncode, pairSndD_pairEncode,
    iterate_shStep m gs [] _ (by simp [length_pairEncode]; omega)]
  simp

/-! ### Polynomial time -/

/-- The shifted node code is polynomial-time in `⟨M, w⟩`. -/
private theorem polyTimeComputable_shiftGateW {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun D => shiftGateW (f D) (g D)) := by
  have ha1 := polyTimeComputable_arg1W.comp hg
  have ha2 := (polyTimeComputable_uHead.comp polyTimeComputable_midW).comp hg
  have hhead : PolyTimeComputable (fun D => [true, tagBit 1 (g D), tagBit 2 (g D),
      tagBit 3 (g D)]) := by
    have t := fun i => (polyTimeComputable_tagBit i).comp hg
    have h := (polyTimeComputable_prepend [true]).comp (((t 1).append (t 2)).append (t 3))
    simpa [Function.comp_def] using h
  have hvar : PolyTimeComputable (fun D => [true, false, false, false] ++ arg1W (g D) ++
      [false]) := ((polyTimeComputable_const [true, false, false, false]).append ha1).append
    (polyTimeComputable_const [false])
  have hbin : PolyTimeComputable (fun D => [true, tagBit 1 (g D), tagBit 2 (g D),
      tagBit 3 (g D)] ++ f D ++ arg1W (g D) ++ [false] ++ f D ++ arg2W (g D) ++ [false]) :=
    (((((hhead.append hf).append ha1).append (polyTimeComputable_const [false])).append
      hf).append ha2).append (polyTimeComputable_const [false])
  exact polyTimeComputable_ite (polyTimeComputable_isVarW.comp hg) hvar
    (polyTimeComputable_ite (polyTimeComputable_isOneW.comp hg) (polyTimeComputable_const _) hbin)

/-- The round is polynomial-time. -/
theorem polyTimeComputable_shStep : PolyTimeComputable shStep := by
  have s2 := polyTimeComputable_slot2
  exact polyTimeComputable_ite (polyTimeComputable_isDone.comp s2) polyTimeComputable_id
    (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_restW.comp s2).pairEncode
      (polyTimeComputable_slot3.append
        (polyTimeComputable_shiftGateW polyTimeComputable_pairFstD s2))))

/-- The leading `1`s and the rest after the first `0` together are no longer than the word. -/
theorem length_uHead_add_uRest_le (w : List Bool) :
    (uHead w).length + (uRest w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> (simp; try omega)

/-- A round grows `|w| + |out|` by at most `2|M| + 8`. -/
theorem shStep_pair (M w out : List Bool) :
    shStep (pairEncode M (pairEncode w out)) = pairEncode M (pairEncode w out) ∨
      ∃ w' out', shStep (pairEncode M (pairEncode w out)) = pairEncode M (pairEncode w' out') ∧
        w'.length + out'.length ≤ w.length + out.length + 2 * M.length + 8 := by
  unfold shStep
  simp only [sW, pairFstD_pairEncode, pairSndD_pairEncode]
  split_ifs
  · exact Or.inl rfl
  · refine Or.inr ⟨_, _, rfl, ?_⟩
    have h1 := length_uHead_add_uRest_le (bodyW w)
    have h2 := length_uHead_add_uRest_le (midW w)
    have h3 : (bodyW w).length ≤ w.length := by simp [bodyW]
    simp only [restW, shiftGateW, midW, rest2W, arg1W, arg2W] at h1 h2 ⊢
    split_ifs <;> simp <;> omega

/-- Along the orbit of the shifting loop, `|w| + |out|` grows by at most `2|M| + 8` per round. -/
theorem iterate_shStep_le (M w : List Bool) (i : ℕ) :
    ∃ w' out', shStep^[i] (pairEncode M (pairEncode w [])) = pairEncode M (pairEncode w' out') ∧
      w'.length + out'.length ≤ w.length + i * (2 * M.length + 8) := by
  induction i with
  | zero => exact ⟨w, [], rfl, by simp⟩
  | succ i ih =>
    obtain ⟨w', out', he, hl⟩ := ih
    rw [Function.iterate_succ_apply', he]
    rcases shStep_pair M w' out' with h | ⟨w'', out'', h, hl'⟩
    · exact ⟨w', out', h, by rw [Nat.succ_mul]; omega⟩
    · exact ⟨w'', out'', h, by rw [Nat.succ_mul]; omega⟩

/-- The shifting loop is polynomial-time. -/
theorem polyTimeComputable_shiftRun : PolyTimeComputable shiftRun := by
  have hinit : PolyTimeComputable (fun z => pairEncode (pairFstD z) (pairEncode (pairSndD z) [])) :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))
  have hit := polyTimeComputable_iterate polyTimeComputable_shStep hinit 1 1 30 2 fun z i hi => by
    obtain ⟨w', out', he, hl⟩ := iterate_shStep_le (pairFstD z) (pairSndD z) i
    rw [he]
    have h1 := length_pairFstD_le z
    have h2 := length_pairSndD_le z
    have hi' : i ≤ z.length + 1 := by simpa using hi
    have h3 : i * (2 * (pairFstD z).length + 8) ≤ (z.length + 1) * (2 * (z.length + 1) + 6) :=
      Nat.mul_le_mul hi' (by omega)
    have e : (z.length + 1) * (2 * (z.length + 1) + 6) =
        2 * (z.length + 1) ^ 2 + 6 * (z.length + 1) := by ring
    have h4 : z.length + 1 ≤ (z.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [length_pairEncode]
    generalize (z.length + 1) ^ 2 = Q at e h4 ⊢
    omega
  exact polyTimeComputable_slot3.comp hit

/-! ### The code of `C − C′` -/

/-- **The code of `C − C′`** from `x = ⟨code C, code C′⟩`: the number of inputs, the nodes of
`C`, the nodes of `C′` shifted by `|C|`, and the node `−(|C| − 1, |C| + |C′| − 1)`. -/
def subW (x : List Bool) : List Bool :=
  uHead (pairFstD x) ++ [false] ++ shiftRun (pairEncode [] (uRest (pairFstD x))) ++
    shiftRun (pairEncode (sI (scanRun (pairFstD x))) (uRest (pairSndD x))) ++
    [true, false, true, true] ++ (sI (scanRun (pairFstD x))).drop 1 ++ [false] ++
    (sI (scanRun (pairFstD x)) ++ sI (scanRun (pairSndD x))).drop 1 ++ [false, false]

/-- **`subW` computes the code of `C − C′`** on codes of well-formed circuits over the same
inputs. [AB09, §7.2.3] -/
theorem subW_eq {x : List Bool} {n : ℕ} {C C' : AlgCircuit n}
    (h₁ : decode (pairFstD x) = some ⟨n, C⟩) (h₂ : decode (pairSndD x) = some ⟨n, C'⟩)
    (hw : C.WellFormed) (hw' : C'.WellFormed) :
    subW x = AlgCircuit.encode ⟨n, C.subCircuit C'⟩ := by
  have hx₁ := encode_of_decode h₁
  have hx₂ := encode_of_decode h₂
  simp only [AlgCircuit.encode] at hx₁ hx₂
  have hs₁ := sI_scanRun h₁ hw
  have hs₂ := sI_scanRun h₂ hw'
  have e0 : shiftRun (pairEncode [] (uRest (pairFstD x))) = gatesBody C.gates := by
    rw [← hx₁, uRest_encodeNat, show ([] : List Bool) = List.replicate 0 true from rfl,
      shiftRun_eq]
    simp
  have e1 : shiftRun (pairEncode (sI (scanRun (pairFstD x))) (uRest (pairSndD x))) =
      gatesBody (C'.gates.map (AlgGate.shift C.size)) := by
    rw [hs₁, ← hx₂, uRest_encodeNat, shiftRun_eq]
  have hu : uHead (pairFstD x) = List.replicate n true := by rw [← hx₁, uHead_encodeNat]
  have hpos : 0 < C.size := List.length_pos_of_ne_nil hw.1
  have hd : (List.replicate C.size true ++ List.replicate C'.size true).drop 1 =
      List.replicate (C.size + C'.size - 1) true := by
    rw [← List.replicate_add, List.drop_replicate]
  rw [subW, e0, e1, hs₁, hs₂, hu, hd, List.drop_replicate, AlgCircuit.encode, subCircuit,
    encodeGates_eq]
  simp [gatesBody, AlgGate.encode, BoolCircuit.encodeNat]

/-- `subW` is polynomial-time.

**Proof sketch.** An append of polynomial-time pieces: `uHead`, the two shifting loops
(`polyTimeComputable_shiftRun`), the node counts `sI ∘ scanRun`, and constants. -/
theorem polyTimeComputable_subW : PolyTimeComputable subW := by
  have h₁ := polyTimeComputable_pairFstD
  have h₂ := polyTimeComputable_pairSndD
  have hsI : PolyTimeComputable (fun x => sI (scanRun x)) :=
    @polyTimeComputable_app sI scanRun (polyTimeComputable_pairFstD.comp polyTimeComputable_slot3)
      polyTimeComputable_scanRun
  have hm₁ : PolyTimeComputable (fun x => sI (scanRun (pairFstD x))) :=
    @polyTimeComputable_app (fun x => sI (scanRun x)) pairFstD hsI h₁
  have hm₂ : PolyTimeComputable (fun x => sI (scanRun (pairSndD x))) :=
    @polyTimeComputable_app (fun x => sI (scanRun x)) pairSndD hsI h₂
  have hr₁ : PolyTimeComputable (fun x => shiftRun (pairEncode [] (uRest (pairFstD x)))) :=
    @polyTimeComputable_app shiftRun (fun x => pairEncode [] (uRest (pairFstD x)))
      polyTimeComputable_shiftRun
      ((polyTimeComputable_const []).pairEncode (polyTimeComputable_uRest.comp h₁))
  have hr₂ : PolyTimeComputable (fun x =>
      shiftRun (pairEncode (sI (scanRun (pairFstD x))) (uRest (pairSndD x)))) :=
    @polyTimeComputable_app shiftRun
      (fun x => pairEncode (sI (scanRun (pairFstD x))) (uRest (pairSndD x)))
      polyTimeComputable_shiftRun (hm₁.pairEncode (polyTimeComputable_uRest.comp h₂))
  have hu : PolyTimeComputable (fun x => uHead (pairFstD x)) := polyTimeComputable_uHead.comp h₁
  have ht₁ : PolyTimeComputable (fun x => (sI (scanRun (pairFstD x))).drop 1) :=
    @polyTimeComputable_app (fun w => w.drop 1) (fun x => sI (scanRun (pairFstD x)))
      polyTimeComputable_tail hm₁
  have ht₂ : PolyTimeComputable (fun x =>
      (sI (scanRun (pairFstD x)) ++ sI (scanRun (pairSndD x))).drop 1) :=
    @polyTimeComputable_app (fun w => w.drop 1)
      (fun x => sI (scanRun (pairFstD x)) ++ sI (scanRun (pairSndD x)))
      polyTimeComputable_tail (hm₁.append hm₂)
  have hall : PolyTimeComputable (fun x => uHead (pairFstD x) ++ [false] ++
      shiftRun (pairEncode [] (uRest (pairFstD x))) ++
      shiftRun (pairEncode (sI (scanRun (pairFstD x))) (uRest (pairSndD x))) ++
      [true, false, true, true] ++ (sI (scanRun (pairFstD x))).drop 1 ++ [false] ++
      (sI (scanRun (pairFstD x)) ++ sI (scanRun (pairSndD x))).drop 1 ++ [false, false]) :=
    ((((((((hu.append (polyTimeComputable_const [false])).append hr₁).append hr₂).append
      (polyTimeComputable_const [true, false, true, true])).append ht₁).append
      (polyTimeComputable_const [false])).append ht₂).append (polyTimeComputable_const [false,
          false]))
  exact hall

end PIT

open PIT

/-- The test of `pitToZerop`: both components encode well-formed circuits over the same number
of inputs. -/
def pitPairOk (x : List Bool) : Bool :=
  validW (pairFstD x) && validW (pairSndD x) &&
    decide ((uHead (pairFstD x)).length = (uHead (pairSndD x)).length)

/-- **The reduction `PIT ≤ₚ ZEROP`** [AB09, §7.2.3]: `⟨C, C′⟩ ↦ code(C − C′)` on pairs of
well-formed circuits over the same inputs, and `[]` (which encodes no circuit) otherwise. -/
def pitToZerop (x : List Bool) : List Bool := if pitPairOk x then subW x else []

/-- The reduction is polynomial-time. -/
theorem polyTimeComputable_pitToZerop : PolyTimeComputable pitToZerop := by
  have hv₁ := polyTimeComputable_test_app polyTimeComputable_validW polyTimeComputable_pairFstD
  have hv₂ := polyTimeComputable_test_app polyTimeComputable_validW polyTimeComputable_pairSndD
  have heq : PolyTimeComputable (fun x => [decide ((uHead (pairFstD x)).length =
      (uHead (pairSndD x)).length)]) := by
    have := polyTimeComputable_test_app polyTimeComputable_lenEq
      ((polyTimeComputable_uHead.comp polyTimeComputable_pairFstD).pairEncode
        (polyTimeComputable_uHead.comp polyTimeComputable_pairSndD))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode] using this
  exact polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_and hv₁ hv₂) heq)
    polyTimeComputable_subW (polyTimeComputable_const [])

/-- The test holds exactly on pairs of codes of well-formed circuits over the same inputs. -/
theorem pitPairOk_iff (x : List Bool) :
    pitPairOk x = true ↔ ∃ (n : ℕ) (C C' : AlgCircuit n),
      decode (pairFstD x) = some ⟨n, C⟩ ∧ decode (pairSndD x) = some ⟨n, C'⟩ ∧
        C.WellFormed ∧ C'.WellFormed := by
  constructor
  · intro h
    simp only [pitPairOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hv₁, hv₂⟩, hn⟩ := h
    obtain ⟨⟨n, C⟩, hd₁, hw⟩ := (validW_iff _).mp hv₁
    obtain ⟨⟨n', C'⟩, hd₂, hw'⟩ := (validW_iff _).mp hv₂
    have hx₁ := encode_of_decode hd₁
    have hx₂ := encode_of_decode hd₂
    simp only [AlgCircuit.encode] at hx₁ hx₂
    rw [← hx₁, ← hx₂, uHead_encodeNat, uHead_encodeNat, List.length_replicate,
      List.length_replicate] at hn
    subst hn
    exact ⟨n, C, C', hd₁, hd₂, hw, hw'⟩
  · rintro ⟨n, C, C', h₁, h₂, hw, hw'⟩
    have hx₁ := encode_of_decode h₁
    have hx₂ := encode_of_decode h₂
    simp only [AlgCircuit.encode] at hx₁ hx₂
    simp only [pitPairOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨(validW_iff _).mpr ⟨_, h₁, hw⟩, (validW_iff _).mpr ⟨_, h₂, hw'⟩⟩, ?_⟩
    rw [← hx₁, ← hx₂, uHead_encodeNat, uHead_encodeNat]

/-- **Correctness of the reduction** [AB09, §7.2.3]: `⟨C, C′⟩ ∈ PIT` iff `code(C − C′) ∈ ZEROP`.

**Proof sketch.** On a pair of well-formed circuits over `n` inputs the image is the code of
`C − C′` (`PIT.subW_eq`), which is well formed (`WellFormed.subCircuit`) and computes zero iff
`C ≡ C′` (`toMvPolynomial_eq_iff_subCircuit`); decoding is injective, so membership of the
image in `ZEROP` is exactly this. Otherwise the image `[]` encodes no circuit, and the pair is
not in `PITLang` (`mem_PITLang_iff`). -/
theorem mem_PITLang_iff_pitToZerop (x : List Bool) : x ∈ PITLang ↔ pitToZerop x ∈ ZEROP := by
  rw [mem_PITLang_iff, mem_ZEROP_iff]
  by_cases hok : pitPairOk x = true
  · obtain ⟨n, C, C', h₁, h₂, hw, hw'⟩ := (pitPairOk_iff x).mp hok
    rw [pitToZerop, if_pos hok, subW_eq h₁ h₂ hw hw', decode_encode]
    constructor
    · rintro ⟨n₀, C₀, C₀', e₁, e₂, -, -, hp⟩
      rw [h₁] at e₁
      rw [h₂] at e₂
      cases e₁
      cases e₂
      exact ⟨_, rfl, hw.subCircuit hw', (toMvPolynomial_eq_iff_subCircuit hw.1 hw'.1).mp hp⟩
    · rintro ⟨c, hc, -, hp⟩
      cases hc
      exact ⟨n, C, C', h₁, h₂, hw, hw', (toMvPolynomial_eq_iff_subCircuit hw.1 hw'.1).mpr hp⟩
  · rw [pitToZerop, if_neg hok]
    constructor
    · rintro ⟨n, C, C', h₁, h₂, hw, hw', -⟩
      exact absurd ((pitPairOk_iff x).mpr ⟨n, C, C', h₁, h₂, hw, hw'⟩) hok
    · rintro ⟨c, hc, -⟩
      have := lt_length_encode c
      rw [encode_of_decode hc] at this
      simp at this

/-- **`PIT ≤ₚ ZEROP`** [AB09, §7.2.3]. -/
theorem PITLang_le_ZEROP : PITLang ≤ₚ ZEROP :=
  ⟨pitToZerop, polyTimeComputable_pitToZerop, mem_PITLang_iff_pitToZerop⟩

/-! ### `coRP` is closed under `≤ₚ` -/

/-- **`coRP` is closed under `≤ₚ`** (PTM form). -/
theorem coRP_PTM_of_polyTimeReducible {L L' : Language Bool} (hred : L' ≤ₚ L)
    (h : L ∈ coRP_PTM) : L' ∈ coRP_PTM :=
  (mem_coRP_PTM_iff _).2 (InCoRP.of_polyTimeReducible hred ((mem_coRP_PTM_iff _).1 h))

/-- **`PIT ∈ coRP` through `PIT ≤ₚ ZEROP`** (PTM form) [AB09, §7.2.3]: re-derives
`Randomized.PITLang_mem_coRP_PTM` along the book's route, from `ZEROP ∈ coRP` and the closure
of `coRP` under `≤ₚ`. -/
theorem PITLang_mem_coRP_PTM_of_reduction : PITLang ∈ coRP_PTM :=
  coRP_PTM_of_polyTimeReducible PITLang_le_ZEROP ZEROP_mem_coRP_PTM

end Randomized
