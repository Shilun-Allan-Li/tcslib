/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Langs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word-level checks of the code languages

What the logspace deciders of the four code languages actually test, as predicates on the
code words: the validity test `Complexity.Codec.ValidChk` of
`TCSlib.Complexity.SpaceComplexity.Codec.Valid`, plus

* for the initial code: header `(q₀, empty)`, the initial cell shape, input position `1`,
  and the head flag of tape `0` in the middle cell;
* for an accepting code: header `(halted, accept)`;
* for a step: the second word has the right length and final letter, and for one of the two
  choice bits its input position is the moved one and the sliding check of the two chunk
  regions accepts under the local rule of that bit's action.

Each check recognizes exactly the code words of the corresponding configurations, and so
decides membership in the code languages on well-shaped inputs.

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.InitChk`, `Complexity.Codec.AcceptChk`, `Complexity.Codec.StepChk`.
* `Complexity.Codec.movePos`, `Complexity.Codec.inpOf`, `Complexity.Codec.aI`,
  `Complexity.Codec.Gs` — the arithmetic and finite data of a step check.

## Main results

* `Complexity.Codec.initChk_iff`, `acceptChk_iff`, `stepChk_iff`.
* `Complexity.Codec.validLang_iff`, `initLang_iff`, `acceptLang_iff`, `stepLang_iff` —
  membership of well-shaped inputs in terms of the checks.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## Reading single letters of a code word -/

/-- Letter `t` of block `j` of a concatenation of fixed-width blocks. -/
lemma getD_flatten_block {α : Type} (L : List (List α)) (w : ℕ)
    (hL : ∀ b ∈ L, b.length = w) (j t : ℕ) (hj : j < L.length) (ht : t < w) (d : α) :
    L.flatten.getD (w * j + t) d = L[j].getD t d := by
  have e := take_drop_flatten L w hL j hj
  rw [← e, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos ht, List.getElem?_drop]

/-- Letter `t` of chunk `j` of a code word is bit `t` of the chunk of cell `j`. -/
lemma getD_cfgWord_chunk (s : ℕ) (C : Cfg N.k Bool N.State x) (j t : ℕ) (hj : j < 2 * s + 1)
    (ht : t < W N) :
    (cfgWord s C).getD (W N * j + t) false = chunkBit N (cellOf s C j) t := by
  have hlt : W N * j + t < W N * (2 * s + 1) := by
    calc W N * j + t < W N * j + W N := by omega
      _ = W N * (j + 1) := by ring
      _ ≤ W N * (2 * s + 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [cfgWord, List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [length_chunksWord]; exact hlt),
    ← List.getD_eq_getElem?_getD]
  unfold chunksWord
  rw [getD_flatten_block _ (W N) (by simp) j t (by simpa using hj) ht]
  simp only [List.getElem_ofFn]
  exact getD_encChunk N _ t ht

/-! ## Initial and accepting codes -/

/-- An output summary is empty exactly for the empty output. -/
lemma outSummary_eq_empty_iff (u : List Bool) : outSummary u = .empty ↔ u = [] := by
  cases u with
  | nil => simp [outSummary]
  | cons a u => cases u <;> cases a <;> simp [outSummary]

variable (N) in
/-- **The initial-code check** on a word `w`: valid, header `(q₀, empty)`, every cell of the
initial shape (blank, all heads or none), input position `1`, and (with at least one work
tape) the head of tape `0` flagged in the middle cell `s`. -/
def InitChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (some N.tm.q₀, 0) ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.2.2.2.2 = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) = 1 ∧
    (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)

/-- **The initial-code check recognizes the code of the initial configuration.**

**Proof sketch.** (⇐) Read the header, the initial shape, the position field and the middle
cell off the layout (`vScan_cfgWord`, `cfgWord_pos`, `getD_cfgWord_chunk`). (⇒) The word
is the code of some window-bounded `C` (`validChk_iff`); the header gives the state `q₀` and
the empty output; the initial shape makes every cell blank (and outside the window cells are
blank anyway) and puts all heads in one cell, and the middle-cell flag puts the head of tape
`0`, hence all heads, at position `0`. So `C` has the vertex of the initial configuration,
and codes depend only on the vertex (`cfgWord_congr`). -/
theorem initChk_iff (s : ℕ) (w : List Bool) :
    InitChk N x s w ↔ w = cfgWord s (N.tm.initCfg x) := by
  have hWin : InWin N s (N.tm.initCfg x) := fun i => by simp [NDTM.initCfg, Cfg.init]
  constructor
  · rintro ⟨hval, hhd, hiok, hpos, hcen⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s C hC
    rw [h1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    obtain ⟨hst, hsum⟩ := hhd
    have hout : C.output = [] := by
      apply (outSummary_eq_empty_iff _).mp
      exact sumIdx_injective (by rw [hsum]; rfl)
    rw [h4, decide_eq_true_eq] at hiok
    rw [cfgWord_pos, bitsVal_padBits] at hpos
    have hblank : ∀ i z, C.workTapes i z = none := by
      intro i z
      by_cases hz : |z| ≤ s
      · have := (hiok (z + s).toNat (by rw [abs_le] at hz; omega)).1 i
        simp only [cellOf] at this
        rwa [show (((z + s).toNat : ℕ) : ℤ) - s = z by rw [abs_le] at hz; omega] at this
      · by_contra hne; exact hz ((hC i).2 z hne)
    have hheads : ∀ i, C.workTapePos i = 0 := by
      intro i
      have hk : 0 < N.k := Fin.pos i
      have h0 : C.workTapePos ⟨0, hk⟩ = 0 := by
        rcases hcen with h | h
        · omega
        · have := getD_cfgWord_chunk s C s (hH N + 2) (by omega) (by simp [W]; omega)
          rw [show W N * s + (hH N + 2) = W N * s + (hH N + 2) from rfl, this] at h
          rw [show hH N + 2 = hH N + 3 * (⟨0, hk⟩ : Fin N.k) + 2 by simp,
            chunkBit_tape N _ _ 2 (by omega)] at h
          simpa [cellOf] using h
      have tog := (hiok s (by omega)).2
      simp only [cellOf, sub_self] at tog
      rcases tog with h | h
      · simpa using h i
      · have := h ⟨0, hk⟩
        simp [h0] at this
    have hcore : NDTM.coreSum C = NDTM.coreSum (N.tm.initCfg x) := by
      simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, NDTM.initCfg, Cfg.init, hst, hout,
        Prod.mk.injEq, true_and]
      refine ⟨⟨Fin.ext (by simpa using hpos), funext fun i => funext fun z => hblank i z,
        funext hheads⟩, trivial⟩
    exact cfgWord_congr hcore
  · rintro rfl
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s (N.tm.initCfg x) hWin
    refine ⟨(validChk_iff x s _).mpr ⟨_, hWin, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [h1]; simp [NDTM.initCfg, Cfg.init, outSummary, sumIdx]
    · rw [h4, decide_eq_true_eq]
      intro j hj
      refine ⟨fun i => by simp [cellOf, NDTM.initCfg, Cfg.init], ?_⟩
      by_cases hjs : (j : ℤ) - s = 0
      · left; intro i; simp [cellOf, NDTM.initCfg, Cfg.init, hjs]
      · right; intro i; simp [cellOf, NDTM.initCfg, Cfg.init]; omega
    · rw [cfgWord_pos, bitsVal_padBits]; rfl
    · by_cases hk : N.k = 0
      · exact Or.inl hk
      · right
        have hk' : 0 < N.k := Nat.pos_of_ne_zero hk
        rw [getD_cfgWord_chunk s _ s (hH N + 2) (by omega) (by simp [W]; omega),
          show hH N + 2 = hH N + 3 * (⟨0, hk'⟩ : Fin N.k) + 2 by simp,
          chunkBit_tape N _ _ 2 (by omega)]
        simp [cellOf, NDTM.initCfg, Cfg.init]

variable (N) in
/-- **The accepting-code check** on a word `w`: valid with header `(halted, accept)`. -/
def AcceptChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (none, 1)

/-- **The accepting-code check recognizes the codes of accepting configurations.**

**Proof sketch.** The header of a code word is the state and the summary index
(`vScan_cfgWord`); summary index `1` is the summary `accept`, i.e. output `[true]`
(`outSummary_eq_accept_iff`). -/
theorem acceptChk_iff (s : ℕ) (w : List Bool) :
    AcceptChk N x s w ↔ ∃ C : Cfg N.k Bool N.State x, InWin N s C ∧ cfgWord s C = w ∧
      C.state = none ∧ C.output = [true] := by
  constructor
  · rintro ⟨hval, hhd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    rw [(vScan_cfgWord s C hC).1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    refine ⟨C, hC, rfl, hhd.1, (outSummary_eq_accept_iff _).mp ?_⟩
    exact sumIdx_injective (by rw [hhd.2]; rfl)
  · rintro ⟨C, hC, rfl, hst, hout⟩
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, ?_⟩
    rw [(vScan_cfgWord s C hC).1, hst, hout]
    rfl

/-! ## Steps -/

/-- The input position after a move, clamped to `[0, n + 1]`: the arithmetic of
`Turing.moveInputPos`. -/
def movePos (n p : ℕ) : SignType → ℕ
  | .zero => p
  | .pos => if p = n + 1 then p else p + 1
  | .neg => p - 1

/-- `movePos` is the value of the clamped move. -/
lemma val_moveInputPos {n : ℕ} (p : Fin (n + 2)) (mv : SignType) :
    (moveInputPos p mv).val = movePos n p.val mv := by
  have := p.isLt
  cases mv with
  | zero => simp [moveInputPos_zero, movePos]
  | pos =>
    simp only [movePos, moveInputPos, SignType.pos_eq_one, SignType.coe_one]
    split_ifs with h1 h2 h2 <;> simp_all <;> omega
  | neg =>
    simp only [movePos, moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg,
      SignType.coe_one]
    split_ifs with h1 <;> simp_all <;> omega

/-- The input symbol at position `p` (shifted by one; blank at both ends). -/
def inpOf (x : List Bool) (p : ℕ) : Option Bool :=
  if p = 0 ∨ p = x.length + 1 then none else some (x.getD (p - 1) false)

/-- The input symbol of a configuration is `inpOf` of its input position. -/
lemma inputSymbol_eq (C : Cfg N.k Bool N.State x) : C.inputSymbol = inpOf x C.inputPos.val := by
  have := C.inputPos.isLt
  unfold Cfg.inputSymbol inpOf
  by_cases h0 : C.inputPos = 0
  · simp [h0]
  · by_cases h1 : C.inputPos.val = x.length + 1
    · have : C.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h1
      simp [this]
    · have hv : C.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      rw [dif_neg h0, dif_neg h1, if_neg (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show C.inputPos.val - 1 <
        x.length by omega)]

variable (N) in
/-- The finite data a step check needs: the validity-scan state of the first word and the
input symbol under its input head. -/
abbrev SInfo := VSt N × Option Bool

set_option synthInstance.maxSize 1000 in
/-- Step data are finitely many. -/
instance SInfo.instFintype : Fintype (SInfo N) := inferInstance

set_option synthInstance.maxSize 1000 in
/-- Step data have decidable equality. -/
instance SInfo.instDecidableEq : DecidableEq (SInfo N) := inferInstance

/-- The header recorded by a validity scan (a default if none). -/
def hdOfV (st : VSt N) : Hd N := st.2.1.getD (none, 0)

variable (N) in
/-- The action of a step under the choice bit `b`, from the step data. -/
def aI (I : SInfo N) (b : Bool) : Action N.k Bool N.State :=
  effAct N (hdOfV I.1).1 I.2 I.1.2.2.2.1 b

variable (N) in
/-- The local rule of a step under the choice bit `b`, from the step data. -/
def Gs (I : SInfo N) (b : Bool) : SX N → SX N → SX N → SX N :=
  stepG (aI N I b) (newHd (aI N I b) (hdOfV I.1))

variable (N) in
/-- **The step check** on words `w`, `w'`: `w` is valid; `w'` has the code length and final
letter `1`; and for one choice bit `b`, the input position of `w'` is that of `w` moved by
`b`'s action, and the sliding check of the chunk regions under `b`'s local rule accepts. -/
def StepChk (x : List Bool) (s : ℕ) (w w' : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧ w'.length = W N * (2 * s + 1) + wP x.length + 1 ∧
    w'.getD (W N * (2 * s + 1) + wP x.length) false = true ∧
    ∃ b : Bool,
      bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)) =
        movePos x.length (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))
          (aI N (vScan N (w.take (W N * (2 * s + 1))),
            inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b).inputTape ∧
      sDone N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
          inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b)
        ((if b then Prod.snd else Prod.fst)
          (sScan N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) false)
            (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) true)
            (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))))) = true

/-- A word of length `a + b + 1` ending with `1` splits into its first `a` letters, the next
`b`, and the final `1`. -/
lemma word_split (w : List Bool) (a b : ℕ) (hlen : w.length = a + b + 1)
    (hlast : w.getD (a + b) false = true) :
    w = w.take a ++ (w.drop a).take b ++ [true] := by
  have htail : w.drop (a + b) = [true] := by
    have hl : (w.drop (a + b)).length = 1 := by simp; omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hl
    rw [hc]
    have h0 := congrArg (fun l : List Bool => l[0]?) hc
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    rw [List.getD_eq_getElem?_getD, h0] at hlast
    simp only [Option.getD_some] at hlast
    rw [hlast]
  rw [← htail, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- A component of the double sliding scan, by the choice bit. -/
lemma sScan_sel (G : Bool → SX N → SX N → SX N → SX N) (u u' : List Bool) (m : ℕ)
    (hu : u.length = W N * m) (hu' : u'.length = W N * m) (b : Bool) :
    (if b then Prod.snd else Prod.fst) (sScan N (G false) (G true) u u') =
      (List.zip (blocksD N u m) (blocksD N u' m)).foldl (slStep (G b)) (sInit N) := by
  rw [sScan_eq (G false) (G true) u u' m hu hu']
  cases b <;> rfl

/-- The step data of a code word: the action and local rule they determine are those of the
coded configuration. -/
lemma aI_cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C) (b : Bool) :
    aI N (vScan N ((cfgWord s C).take (W N * (2 * s + 1))),
        inpOf x (bitsVal (((cfgWord s C).drop (W N * (2 * s + 1))).take (wP x.length)))) b =
      effAct N C.state C.inputSymbol C.workTapeSymbols b ∧
    hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
  obtain ⟨h1, -, h3, -⟩ := vScan_cfgWord s C hC
  have hhd : hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
    simp only [hdOfV, h1, Option.getD_some, hdOf]
  refine ⟨?_, hhd⟩
  simp only [aI, hhd, hdOf, cfgWord_pos, bitsVal_padBits, ← inputSymbol_eq]
  congr 1
  funext i
  exact h3 i

/-- **The step check recognizes code words of configuration-graph edges.**

**Proof sketch.** Both directions go through the coded configuration `C` of the first word
(`validChk_iff`), whose scan data determine the action of each choice bit (`aI_cfgWord`).
For a choice bit `b`, with `C' = stepWith b C` (`stepWith_eq_apply`): the sliding check of
`b` accepts iff the chunk region of the second word is that of `C'` and `C'` is
window-bounded (`sScan_sel`, `sDone_step`); the input position of `C'` is the moved one
(`val_moveInputPos`), and a position field is determined by its value (`eq_padBits`); with
the length and the final letter (`word_split`), the second word is the code word of `C'`. -/
theorem stepChk_iff (s : ℕ) (w w' : List Bool) :
    StepChk N x s w w' ↔ ∃ C : Cfg N.k Bool N.State x, InWin N s C ∧ cfgWord s C = w ∧
      ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ InWin N s C' ∧ cfgWord s C' = w' := by
  constructor
  · rintro ⟨hval, hlen', hlast', b, hpos', hsd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    have hA' : (w'.take (W N * (2 * s + 1))).length = W N * (2 * s + 1) := by
      simp only [List.length_take]; omega
    rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1) (by simp [length_cfgWord]; omega) hA'] at hsd
    simp only [Gs] at hsd
    rw [ha, hhd, cfgWord_take] at hsd
    obtain ⟨hcells, hwin'⟩ := (sDone_step s C hC a _ hA').mp hsd
    refine ⟨C, hC, rfl, a.apply C, ⟨b, stepWith_eq_apply b C⟩, hwin', ?_⟩
    rw [word_split w' (W N * (2 * s + 1)) (wP x.length) hlen' hlast', hcells]
    simp only [cfgWord]
    congr 2
    have hP : ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length := by
      simp only [List.length_take, List.length_drop]; omega
    rw [eq_padBits ((w'.drop (W N * (2 * s + 1))).take (wP x.length)), hP, hpos', ha]
    simp only [cfgWord_pos, bitsVal_padBits]
    rw [← val_moveInputPos]
    rfl
  · rintro ⟨C, hC, rfl, C', ⟨b, hstep⟩, hC', rfl⟩
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    rw [stepWith_eq_apply] at hstep
    subst hstep
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, length_cfgWord s _, cfgWord_last s _, b, ?_, ?_⟩
    · rw [ha, cfgWord_pos, bitsVal_padBits, cfgWord_pos, bitsVal_padBits]
      exact val_moveInputPos _ _
    · have hA' : ((cfgWord s (a.apply C)).take (W N * (2 * s + 1))).length =
          W N * (2 * s + 1) := by simp only [List.length_take, length_cfgWord]; omega
      rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1)
        (by simp only [List.length_take, length_cfgWord]; omega) hA']
      simp only [Gs]
      rw [ha, hhd]
      simp only [cfgWord_take]
      exact (sDone_step s C hC a _ (length_chunksWord N _ _)).mpr ⟨rfl, hC'⟩

/-! ## Membership through the checks -/

/-- The code word of a configuration is the binary word of its code; a word equal to a code
word is the binary word of a number. -/
lemma cfgWord_eq_bits_iff (s : ℕ) (C : Cfg N.k Bool N.State x) (c : ℕ) :
    cfgCode s C = c ↔ cfgWord s C = Nat.bits c := by
  rw [← bits_cfgCode]
  exact ⟨fun h => h ▸ rfl, fun h => bits_injective h⟩

variable (N) in
/-- **Valid codes through the check**: on `⟨x, ⟨w, bits s⟩⟩` with any word `w`, membership in
`validLang` is the validity test of `w`. -/
theorem validLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ validLang N ↔ ValidChk (N := N) x.length s w := by
  rw [validChk_iff]
  constructor
  · rintro ⟨x', c, s', h, C, hC, hc⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
    obtain rfl := bits_injective h4
    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨x, cfgCode s C, s, by rw [bits_cfgCode], C, hC, rfl⟩

variable (N) in
/-- **Initial codes through the check.** -/
theorem initLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ initLang N ↔ InitChk N x s w := by
  rw [initChk_iff]
  constructor
  · rintro ⟨x', c, s', h, hc⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
    obtain rfl := bits_injective h4
    exact ((cfgWord_eq_bits_iff _ _ c).mp hc).symm
  · rintro rfl
    exact ⟨x, cfgCode s (N.tm.initCfg x), s, by rw [bits_cfgCode], rfl⟩

variable (N) in
/-- **Accepting codes through the check.** -/
theorem acceptLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ acceptLang N ↔ AcceptChk N x s w := by
  rw [acceptChk_iff]
  constructor
  · rintro ⟨x', c, s', h, C, hC, hc, hst, hout⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
    obtain rfl := bits_injective h4
    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc, hst, hout⟩
  · rintro ⟨C, hC, rfl, hst, hout⟩
    exact ⟨x, cfgCode s C, s, by rw [bits_cfgCode], C, hC, rfl, hst, hout⟩

variable (N) in
/-- **Step pairs through the check.** -/
theorem stepLang_iff (x w w' : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (pairEncode w' (Nat.bits s))) ∈ stepLang N ↔
      StepChk N x s w w' := by
  rw [stepChk_iff]
  constructor
  · rintro ⟨x', c, c', s', h, C, hC, hc, C', hstep, hC', hc'⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
    obtain ⟨rfl, h6⟩ := pairEncode_inj h4
    obtain rfl := bits_injective h6
    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc, C', hstep, hC',
      (cfgWord_eq_bits_iff _ C' c').mp hc'⟩
  · rintro ⟨C, hC, rfl, C', hstep, hC', rfl⟩
    exact ⟨x, cfgCode s C, cfgCode s C', s, by rw [bits_cfgCode, bits_cfgCode], C, hC, rfl, C',
      hstep, hC', rfl⟩

end Complexity.Codec
