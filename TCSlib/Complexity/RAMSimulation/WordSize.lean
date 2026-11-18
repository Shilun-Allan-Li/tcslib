/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.ClassP.TimeConstructiblePoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word size of a simulated word RAM

A word-RAM simulation computes its input-dependent word size once at startup.
`WordRAM.WordSizeComputable W TW SW` asks for a finite binary machine that writes
`W (|x|)` within `TW (|x|)` steps and `SW (|x|)` visited work cells.

## Main definitions

* `WordRAM.WordSizeComputable`.

## Main results

* `WordRAM.WordSizeComputable.mono` weakens the time and space bounds.
* `WordRAM.wordSizeComputable_logSpace` supplies logarithmic word sizes in linear time.
* `WordRAM.wordSizeComputable_of_spaceConstructible` supplies space-constructible word sizes.
* `WordRAM.wordSizeComputable_of_timeConstructible` and `WordRAM.wordSizeComputable_poly` supply
  time-constructible and polynomial word sizes, in time linear in their value.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1, p. 79: time- and space-constructible
  functions.)
-/

namespace WordRAM

open Turing

/-! ## Machines -/

/-- The bounded carry after one digit of multiplication by `c + 1`. -/
private def mulCarry (c : ℕ) (r : Fin (c + 1)) (b : Bool) : Fin (c + 1) :=
  ⟨((c + 1) * b.toNat + r.val) / 2, by
    have := r.isLt
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;>
      omega⟩

/-- A constant multiplier needs only finite control: the input scan emits the low bit and
retains the carry; the final phase emits the carry. The catalog has no such arithmetic leaf. -/
private def mulMachine (c : ℕ) : FinTM Bool where
  k := 0
  State := Fin (c + 1) ⊕ Fin (c + 1)
  tm :=
    { q₀ := Sum.inl 0
      tr := fun q inp _ => match q with
        | Sum.inl r => match inp with
          | some b => ⟨.pos, Fin.elim0, some (decide (((c + 1) * b.toNat + r.val) % 2 = 1)),
              some (Sum.inl (mulCarry c r b))⟩
          | none => ⟨0, Fin.elim0, none, some (Sum.inr r)⟩
        | Sum.inr r =>
          if h : r.val = 0 then ⟨0, Fin.elim0, none, none⟩
          else ⟨0, Fin.elim0, some (decide (r.val % 2 = 1)),
            some (Sum.inr ⟨r.val / 2, by have := r.isLt; omega⟩)⟩ }

/-- A positive number consists of its parity bit followed by the binary quotient. -/
private lemma parity_bits (n : ℕ) (hn : 0 < n) :
    n.bits = decide (n % 2 = 1) :: (n / 2).bits := by
  have hd : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp only [h] <;>
      norm_num <;> omega
  have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
    intro hz
    simp only [decide_eq_true_eq]
    omega
  exact (congrArg Nat.bits hd).trans (Complexity.LogProg.bits_two_mul_add _ _ hb)

/-- The carry phase emits the canonical carry word and halts.
**Proof sketch.** Induct on the carry. A nonzero carry emits its parity bit and
continues on its quotient by two; `parity_bits` identifies the complete output. -/
private theorem mul_flush (c : ℕ) {x : List Bool} (n : ℕ) :
    ∀ (hn : n < c + 1) (d : Cfg 0 Bool (mulMachine c).State x),
      d.state = some (Sum.inr ⟨n, hn⟩) →
      ((mulMachine c).tm.runFrom d (n.bits.length + 1)).state = none ∧
      ((mulMachine c).tm.runFrom d (n.bits.length + 1)).output = d.output ++ n.bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn d hs
    by_cases hz : n = 0
    · subst n
      simp only [Nat.zero_bits, List.length_nil, Nat.zero_add,
        MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some hs]
      constructor
      · rw [Action.apply_state]
        rfl
      · rw [Action.apply_output]
        rfl
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      have hb := parity_bits n hp
      have hlen : n.bits.length + 1 = 1 + ((n / 2).bits.length + 1) := by
        rw [hb, List.length_cons]
        omega
      let e := (mulMachine c).tm.step d
      have he : e.state = some (Sum.inr ⟨n / 2, by omega⟩) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, dif_neg hz]
      have ho : e.output = d.output ++ [decide (n % 2 = 1)] := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, dif_neg hz, Option.toList_some]
      obtain ⟨halt, output⟩ := ih (n / 2) (by omega) (by omega) e he
      rw [hlen, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
      refine ⟨halt, ?_⟩
      rw [output, ho, List.append_assoc, List.singleton_append, ← hb]

/-- Scanning a canonical binary suffix multiplies its value, with an incoming carry.
**Proof sketch.** Induct on the suffix value. One scan step removes its low bit,
emits the product's low bit, and recurses on the quotient and the bounded new carry.
The empty suffix dispatches to `mul_flush`. -/
private theorem mul_scan (c : ℕ) (n : ℕ) :
    ∀ (r : Fin (c + 1)) (x pre : List Bool) (d : Cfg 0 Bool (mulMachine c).State x),
      x = pre ++ n.bits → d.inputPos.val = pre.length + 1 →
      d.state = some (Sum.inl r) →
      ∃ t ≤ n.bits.length + c + 2,
        ((mulMachine c).tm.runFrom d t).state = none ∧
        ((mulMachine c).tm.runFrom d t).output = d.output ++ ((c + 1) * n + r.val).bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r x pre d hx hi hs
    by_cases hz : n = 0
    · subst n
      have he : d.inputSymbol = none := Cfg.inputSymbol_of_end (by
        have hl := congrArg List.length hx
        simp only [List.length_append, Nat.zero_bits, List.length_nil] at hl
        omega)
      let e := (mulMachine c).tm.step d
      have es : e.state = some (Sum.inr r) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, he]
      have eo : e.output = d.output := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, he, Option.toList_none, List.append_nil]
      obtain ⟨halt, out⟩ := mul_flush c r.val r.isLt e es
      refine ⟨1 + (r.val.bits.length + 1), ?_, ?_⟩
      · have := length_bits_le_self r.val
        have := r.isLt
        simp only [Nat.zero_bits, List.length_nil]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
        refine ⟨halt, ?_⟩
        simpa only [eo, Nat.mul_zero, Nat.zero_add] using out
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      let b := decide (n % 2 = 1)
      let v := (c + 1) * b.toNat + r.val
      let rr := mulCarry c r b
      have hb : n.bits = b :: (n / 2).bits := parity_bits n hp
      have hn : n = 2 * (n / 2) + b.toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
          simp only [b, h] <;> norm_num <;> omega
      have he : d.inputSymbol = some b := by
        have hbit : x[pre.length]'(by rw [hx, hb, List.length_append, List.length_cons]; omega) = b := by
          simp only [hx, hb]
          simp only [List.getElem_append_right (Nat.le_refl pre.length), Nat.sub_self,
            List.getElem_cons_zero]
        exact (inputSymbolInner pre.length (by omega) (by
          rw [hx, hb, List.length_append, List.length_cons]; omega)).trans (congrArg some hbit)
      let e := (mulMachine c).tm.step d
      have es : e.state = some (Sum.inl rr) := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_state]
        simp only [mulMachine, he, rr]
      have ei : e.inputPos.val = (pre ++ [b]).length + 1 := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_inputPos]
        simp only [mulMachine, he]
        rw [moveInputPos_pos_of_ne_right _ (by
          have hl := congrArg List.length hx
          rw [List.length_append, hb, List.length_cons] at hl
          omega)]
        simp only [List.length_append, List.length_singleton]
        omega
      have eo : e.output = d.output ++ [decide (v % 2 = 1)] := by
        dsimp only [e]
        rw [MultiTapeTM.step_of_some hs, Action.apply_output]
        simp only [mulMachine, he, v, Option.toList_some]
      obtain ⟨t, ht, halt, out⟩ := ih (n / 2) (by omega) rr x (pre ++ [b]) e
        (by rw [hx, hb, List.append_assoc, List.singleton_append]) ei es
      have val : (c + 1) * n + r.val = 2 * ((c + 1) * (n / 2)) + v := by
        calc
          _ = (c + 1) * (2 * (n / 2) + b.toNat) + r.val := by rw [← hn]
          _ = _ := by dsimp only [v]; ring
      have vp : 0 < (c + 1) * n + r.val := by positivity
      have vm : ((c + 1) * n + r.val) % 2 = v % 2 := by omega
      have vd : ((c + 1) * n + r.val) / 2 = (c + 1) * (n / 2) + rr.val := by
        dsimp only [rr, mulCarry, v]
        omega
      have product : ((c + 1) * n + r.val).bits =
          decide (v % 2 = 1) :: ((c + 1) * (n / 2) + rr.val).bits := by
        rw [parity_bits _ vp, vm, vd]
      refine ⟨1 + t, ?_, ?_⟩
      · rw [hb, List.length_cons]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one]
        refine ⟨halt, ?_⟩
        rw [out, eo, List.append_assoc, List.singleton_append, ← product]

/-- A fixed constant times a canonical binary input is computable with no work tapes,
using at most its input width plus a constant number of steps.
**Proof sketch.** At zero use `FinTM.constTM`; at a positive coefficient use
`mulMachine` and specialize `mul_scan` to the initial configuration with zero carry. -/
private theorem constant_multiplier (c : ℕ) :
    ∃ (M : FinTM Bool) (B : ℕ),
      (∀ (x : List Bool) (t : ℕ), M.tm.spaceUsed (M.tm.initCfg x) t = 0) ∧
      ∀ n, ∃ t ≤ n.bits.length + B, M.ComputesInTime n.bits (c * n).bits t := by
  cases c with
  | zero =>
    refine ⟨FinTM.constTM [], 1, FinTM.constTM_spaceUsed [], fun n => ⟨1, by omega, ?_⟩⟩
    simpa only [Nat.zero_mul, Nat.zero_bits, List.length_nil, Nat.zero_add] using
      FinTM.constTM_computes [] n.bits
  | succ c =>
    refine ⟨mulMachine c, c + 2,
      fun x t => MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl, fun n => ?_⟩
    obtain ⟨t, ht, halt, out⟩ := mul_scan c n 0 n.bits [] ((mulMachine c).tm.initCfg n.bits)
      rfl (by rw [MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl)
      (by rw [MultiTapeTM.initCfg_eq, Cfg.init_state]; rfl)
    refine ⟨t, by omega, (FinTM.computesInTime_iff _ _ _ _).mpr ⟨halt, ?_⟩⟩
    simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
      Fin.val_zero, Nat.add_zero] using out


/-- Changing the designated start state leaves runs from a fixed configuration, and
therefore visited work space, unchanged. -/
private lemma space_with_start {k : ℕ} {S : Type} {x : List Bool}
    (R : MultiTapeTM k Bool S) (q : S) (d : Cfg k Bool S x) (t : ℕ) :
    ({R with q₀ := q} : MultiTapeTM k Bool S).spaceUsed d t = R.spaceUsed d t := by
  rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
  apply congrArg Finset.card
  ext z
  simp only [MultiTapeTM.mem_visitedByTapeHead_iff, MultiTapeTM.runFrom_with_q₀]

/-- Sum a selected bank once, allowing a uniform bound on its unused tapes.
**Proof sketch.** Split the host bank into the image of the selection and its complement.
`Finset.sum_image` identifies the first sum, and the complement has at most `k` elements. -/
private lemma bank_sum_bound {m k : ℕ} (ι : Fin m ↪ Fin k) (a : Fin k → ℕ)
    (b : Fin m → ℕ) (B : ℕ) (hs : ∀ i, a (ι i) ≤ b i)
    (hf : ∀ j, j ∉ Set.range ι → a j ≤ B) :
    ∑ j, a j ≤ ∑ i, b i + k * B := by
  classical
  let s := Finset.univ.image ι
  have hpart := Finset.sum_sdiff (f := a) (Finset.subset_univ s)
  have hsel : ∑ j ∈ s, a j ≤ ∑ i, b i := by
    rw [Finset.sum_image (fun _ _ _ _ h => ι.injective h)]
    exact Finset.sum_le_sum fun i _ => hs i
  have hframe : ∑ j ∈ Finset.univ \ s, a j ≤ k * B := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ \ s, B := by
        apply Finset.sum_le_sum
        intro j hj
        apply hf
        intro he
        obtain ⟨i, rfl⟩ := he
        exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      _ = (Finset.univ \ s).card * B := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ k * B := Nat.mul_le_mul_right B (by
        exact (Finset.card_le_card (Finset.sdiff_subset)).trans (by
          rw [Finset.card_univ, Fintype.card_fin]))
  omega

/-- Capture a native numerical computation, multiply its buffered answer by a constant,
and emit the result with time and space bounds.

**Proof sketch.** `constant_multiplier` supplies the finite-control arithmetic leaf.
`embedSilentRetTM_firstReturn` captures the native computation through its first halt;
`rewindTM_run_ofCfg` returns the captured head to the origin, preserving the native bank.
`vhostEmitTM_runFrom` runs the multiplier on that buffer and forwards its final emission.
`embedEmitCfg_eq` identifies this entry even with arbitrary residue in the native bank.
Two applications of `seamCompTM_run_ofCfg`, with their first-return cuts, assemble the run.
For space, `bank_sum_bound` counts each selected bank once, while the capture, rewind and
virtual-input ledgers account for their boundary cells. Adding the phase bounds with
`seamCompTM_spaceUsed_le_add_ofCfg` gives a constant times the source space plus the answer
width and one. The two dispatches and rewind give the stated linear width overhead. -/
private theorem scale_computes (M : FinTM Bool) (c : ℕ) :
    ∃ (N : FinTM Bool) (A B : ℕ), ∀ (x : List Bool) (n t : ℕ),
      M.ComputesInTime x n.bits t →
      ∃ u ≤ t + 2 * n.bits.length + B,
        N.ComputesInTime x (c * n).bits u ∧
        N.tm.spaceUsed (N.tm.initCfg x) u ≤
          A * (M.tm.spaceUsed (M.tm.initCfg x) t + n.bits.length + 1) := by
  classical
  obtain ⟨P, B, ps, ph⟩ := constant_multiplier c
  let k := M.k + (1 + P.k)
  let σ : Fin M.k ↪ Fin k := Fin.castAddEmb (1 + P.k)
  let ι : Fin (1 + P.k) ↪ Fin k := Fin.natAddEmb M.k
  let cap : Fin k := ι 0
  have hcap : cap ∉ Set.range σ := by
    rintro ⟨j, hj⟩
    have he : j.val = M.k := congrArg Fin.val hj
    omega
  let C := embedSilentRetTM σ cap M.tm
  let R := rewindTM (Symbol := Bool) k cap
  let E := embedEmitTM ι (vhostEmitTM P.tm)
  let CR := seamCompTM C (Sum.inr ()) R .start
  let H := seamCompTM CR (Sum.inr .done) E (P.tm.q₀, true)
  let q : ((M.State ⊕ Unit) ⊕ RewindPhase) ⊕ (P.State × Bool) :=
    Sum.inl (Sum.inl (Sum.inl M.tm.q₀))
  let N : FinTM Bool :=
    { k := k
      State := ((M.State ⊕ Unit) ⊕ RewindPhase) ⊕ (P.State × Bool)
      tm := { H with q₀ := q } }
  refine ⟨N, 20 * k, B + 4, ?_⟩
  intro x n t hm
  obtain ⟨halt, out⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hm
  let d := M.tm.runFrom (M.tm.initCfg x) t
  let a₀ : Cfg k Bool (M.State ⊕ Unit) x := (embedSilentCfg σ cap (fun _ _ => none) (fun _ => 0) [] []
    (M.tm.initCfg x)).mapState Sum.inl
  let a₁ : Cfg k Bool (M.State ⊕ Unit) x :=
    { embedSilentCfg σ cap (fun _ _ => none) (fun _ => 0) [] [] d with
      state := some (Sum.inr ()) }
  obtain ⟨a, ha, arun, acut⟩ := embedSilentRetTM_firstReturn M x σ cap hcap
    (fun _ _ => none) (fun _ => 0) [] t halt
  have aword : a₁.workTapes cap = FinTM.bufferTape n.bits ∧
      a₁.workTapePos cap = (n.bits.length : ℤ) := by
    simpa only [a₁, d, List.nil_append, out] using
      embedSilentCfg_cap σ cap hcap (fun _ _ => none) (fun _ => 0) [] [] d
  have aout : a₁.output = [] := by
    dsimp only [a₁]
    rw [embedSilentCfg_output]
  let r₀ := a₁.mapState (fun _ => RewindPhase.start)
  obtain ⟨rrun, rcut, rheads⟩ := rewindTM_run_ofCfg cap n.bits n.bits.length (le_refl _) r₀
    (by rw [Cfg.mapState_state]; rfl) (by
      intro p hp hlt
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, aword.1, aword.2]
      congr 1
      omega)
  let r₁ : Cfg k Bool RewindPhase x :=
    { r₀ with
      state := some .done
      workTapePos := Function.update r₀.workTapePos cap (r₀.workTapePos cap - n.bits.length) }
  have crun := seamCompTM_run_ofCfg C (Sum.inr ()) R .start arun rfl acut rrun
  have ccut := seamCompTM_firstReturn_ofCfg C (Sum.inr ()) R .start .done
    arun rfl acut rrun rfl rcut
  obtain ⟨b, hb, hp⟩ := ph n
  let v₀ := vhostCfg (P.tm.initCfg n.bits) true r₁.inputPos []
  let e₀ := embedEmitCfg ι r₁.workTapes r₁.workTapePos [] v₀
  have tag : FinTM.VirtualTag (P.tm.initCfg n.bits).inputPos true := by
    rw [FinTM.VirtualTag_iff, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      have : (1 : ℕ) ≠ 0 := by decide
      exact (this (by simpa only [Fin.val_one] using h)).elim
    · intro _
      rfl
  have estart : e₀ = r₁.mapState (fun _ => (P.tm.q₀, true)) := by
    apply embedEmitCfg_eq
    · rw [vhostCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state,
        Cfg.mapState_state, Option.map_some]
      rfl
    · dsimp only [v₀]
      simp only [vhostCfg_inputPos, Cfg.mapState_inputPos]
    · rw [vhostCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
        Cfg.mapState_output]
      simp only [List.nil_append]
      simpa only [r₁, r₀, Cfg.mapState_output] using aout.symm
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have iz : i = 0 := Subsingleton.elim _ _
        subst i
        constructor
        · funext z
          dsimp only [v₀, r₁, r₀]
          simp only [vhostCfg_workTapes, Fin.addCases_left, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) aword.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_left, MultiTapeTM.initCfg_eq,
            Cfg.init_inputPos, Fin.val_one, Cfg.mapState_workTapePos]
          dsimp only [r₁]
          rw [show ι (Fin.castAdd P.k (0 : Fin 1)) = cap from rfl,
            Function.update_self, Cfg.mapState_workTapePos, aword.2]
          omega
      · have hsel : ι (Fin.natAdd 1 i) ∉ Set.range σ := by
          rintro ⟨j, hj⟩
          have he : j.val = M.k + (1 + i.val) := congrArg Fin.val hj
          omega
        have hne : ι (Fin.natAdd 1 i) ≠ cap := by
          intro he
          have hh : M.k + (1 + i.val) = M.k := congrArg Fin.val he
          omega
        have framed := embedSilentCfg_unselected σ cap (fun _ _ => none) (fun _ => 0)
          [] [] d (ι (Fin.natAdd 1 i)) hsel hne
        constructor
        · funext z
          dsimp only [v₀, r₁, r₀, a₁]
          simp only [vhostCfg_workTapes, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapes, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) framed.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapePos, Cfg.mapState_workTapePos]
          dsimp only [r₁]
          rw [Function.update_of_ne hne, Cfg.mapState_workTapePos]
          exact framed.2.symm
    · intro j _
      exact ⟨funext fun z => (Cfg.mapState_workTapes _ _ j z).symm,
        (Cfg.mapState_workTapePos _ _ j).symm⟩
  obtain ⟨tagEnd, _, vrun⟩ := vhostEmitTM_runFrom P.tm (P.tm.initCfg n.bits) true tag
    r₁.inputPos [] b
  have erun : E.runFrom e₀ b =
      embedEmitCfg ι r₁.workTapes r₁.workTapePos []
        (vhostCfg (P.tm.runFrom (P.tm.initCfg n.bits) b) tagEnd r₁.inputPos []) := by
    rw [embedEmitTM_runFrom, vrun]
  have hrun := seamCompTM_run_ofCfg CR (Sum.inr .done) E (P.tm.q₀, true)
    crun (by rw [Cfg.mapState_state]; rfl) ccut (by
      simpa only [Turing.Cfg.mapState_mapState, Function.comp_apply] using estart.symm ▸ erun)
  have nstart : N.tm.initCfg x = ((a₀.mapState Sum.inl).mapState Sum.inl) := by
    rw [MultiTapeTM.initCfg_with_q₀]
    rw [show a₀ = Cfg.init (Sum.inl M.tm.q₀) x from
      embedSilentCfg_initCfg M.tm σ cap hcap x]
    apply Cfg.ext
    · simp only [Cfg.init_state, Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.init_inputPos, Cfg.mapState_inputPos]
    · funext j z
      simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    · funext j
      simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    · simp only [Cfg.init_output, Cfg.mapState_output]
  let u := (a + 1 + (n.bits.length + 2)) + 1 + b
  refine ⟨u, by dsimp only [u]; omega, ?_, ?_⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [nstart, MultiTapeTM.runFrom_with_q₀, hrun]
    obtain ⟨phh, pho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hp
    simp only [Cfg.mapState_state, Cfg.mapState_output, embedEmitCfg_state,
      embedEmitCfg_output, vhostCfg_state, vhostCfg_output, phh, pho,
      Option.map_none, List.nil_append, and_self]
  · rw [nstart, space_with_start]
    have cspace : C.spaceUsed a₀ a ≤ M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) := by
      have sumBound := bank_sum_bound σ
        (fun j => C.spaceUsedByTape a₀ a j)
        (fun i => M.tm.spaceUsedByTape (M.tm.initCfg x) a i) (n.bits.length + 1)
        (fun i => by
          dsimp only
          rw [MultiTapeTM.spaceUsedByTape_eq_card,
            embedSilentRetTM_visitedByTapeHead,
            (embedSilentTM_visitedByTapeHead σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a i).1,
            ← MultiTapeTM.spaceUsedByTape_eq_card])
        (fun j hj => by
          dsimp only
          rw [MultiTapeTM.spaceUsedByTape_eq_card, embedSilentRetTM_visitedByTapeHead,
            ← MultiTapeTM.spaceUsedByTape_eq_card]
          by_cases he : j = cap
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a
            have ho := (M.tm.output_prefix (M.tm.initCfg x) ha).length_le
            rw [out] at ho
            omega
          · rw [(embedSilentTM_visitedByTapeHead_frame σ cap hcap M.tm
              (fun _ _ => none) (fun _ => 0) [] [] (M.tm.initCfg x) a j hj he).2]
            omega)
      dsimp only at sumBound
      simp only [← MultiTapeTM.spaceUsed_eq_sum] at sumBound
      exact sumBound.trans (Nat.add_le_add_right
        (M.tm.spaceUsed_mono (M.tm.initCfg x) ha) _)
    have rspace : R.spaceUsed r₀ (n.bits.length + 2) ≤ k * (2 * (n.bits.length + 2) + 1) := by
      apply MultiTapeTM.spaceUsed_le_of_abs_le
      intro v hv j
      have h := rheads j v hv
      by_cases hj : j = cap
      · rw [if_pos hj, Finset.mem_Icc] at h
        rw [abs_le]
        constructor <;> omega
      · rw [if_neg hj] at h
        rw [h, sub_self, abs_zero]
        positivity
    have espace : E.spaceUsed e₀ b ≤ n.bits.length + 2 + k := by
      have sumBound := bank_sum_bound ι
        (fun j => E.spaceUsedByTape e₀ b j)
        (fun i => (vhostEmitTM P.tm).spaceUsedByTape v₀ b i) 1
        (fun i => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead ι (vhostEmitTM P.tm) r₁.workTapes
            r₁.workTapePos [] v₀ b i).2])
        (fun j hj => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead_frame ι (vhostEmitTM P.tm) r₁.workTapes
            r₁.workTapePos [] v₀ b j hj).2])
      dsimp only at sumBound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at sumBound
      have hs := vhostEmitTM_spaceUsed_le P.tm (P.tm.initCfg n.bits) true tag r₁.inputPos [] b
      rw [ps] at hs
      exact sumBound.trans (Nat.add_le_add_right (by simpa only [Nat.zero_add] using hs) _)
    have crspace := seamCompTM_spaceUsed_le_add_ofCfg C (Sum.inr ()) R .start
      (T₂ := n.bits.length + 2) arun rfl acut
    have hspace := seamCompTM_spaceUsed_le_add_ofCfg CR (Sum.inr .done) E (P.tm.q₀, true)
      (T₂ := b) crun (by rw [Cfg.mapState_state]; rfl) ccut
    have eh : (r₁.mapState (Sum.inr : RewindPhase → (M.State ⊕ Unit) ⊕ RewindPhase)).mapState (fun _ => (P.tm.q₀, true)) = e₀ := by
      rw [Turing.Cfg.mapState_mapState]
      exact estart.symm
    rw [eh] at hspace
    have combined : H.spaceUsed ((a₀.mapState Sum.inl).mapState Sum.inl) u ≤
        M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) +
        k * (2 * (n.bits.length + 2) + 1) + (n.bits.length + 2 + k) := by
      exact hspace.trans ((Nat.add_le_add_right crspace _).trans
        (Nat.add_le_add (Nat.add_le_add cspace rspace) espace))
    apply combined.trans
    have hk : 0 < k := by dsimp only [k]; omega
    have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ k * M.tm.spaceUsed (M.tm.initCfg x) t :=
      Nat.le_mul_of_pos_left _ hk
    have hw : n.bits.length + 2 ≤ k * (n.bits.length + 2) := Nat.le_mul_of_pos_left _ hk
    calc
      _ ≤ k * M.tm.spaceUsed (M.tm.initCfg x) t + k * (n.bits.length + 1) +
          k * (2 * (n.bits.length + 2) + 1) + (k * (n.bits.length + 2) + k) := by omega
      _ = k * (M.tm.spaceUsed (M.tm.initCfg x) t + 4 * n.bits.length + 9) := by ring
      _ ≤ k * (20 * (M.tm.spaceUsed (M.tm.initCfg x) t + n.bits.length + 1)) := by
        apply Nat.mul_le_mul_left
        omega
      _ = _ := by ring

/-- Count a word's length in binary, returning `1` instead of `0` for the empty word.
**Proof sketch.** A fixed-word equality test chooses between the constant word `[true]`
and the catalog's binary length counter. The conditional time bound is linear. -/
private theorem normalized_counter :
    ∃ (V : FinTM Bool) (A : ℕ), ∀ w : List Bool,
      V.ComputesInTime w (if w = [] then [true] else w.length.bits) (A * (w.length + 1)) := by
  obtain ⟨L, b, hl, _⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let D := FinTM.ifEqTM [] [true] [false]
  have hd : D.ComputesFunInTime (fun w => [decide (w = [])]) (fun n => 4 * (n + 1)) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro w
    have h := (FinTM.computesFunInTime_iff _ _ _).mp
      (FinTM.ifEqTM_computes [] [true] [false]) w
    by_cases hw : w = []
    · simpa only [hw, if_pos rfl, decide_true, List.length_nil,
        List.length_singleton, max_self, Nat.zero_add] using h
    · simpa only [hw, if_false, decide_false, List.length_nil,
        List.length_singleton, max_self, Nat.zero_add] using h
  have hc : (FinTM.constTM [true]).ComputesFunInTime (fun _ => [true])
      (fun n => 2 * (n + 1)) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro w
    exact (FinTM.constTM_computes [true] w).mono (by
      simp only [List.length_singleton]
      omega)
  obtain ⟨V, A, hv⟩ := FinTM.computesFunInTime_cond hd hc hl
  refine ⟨V, A * (b + 7), fun w => ?_⟩
  have h := (FinTM.computesFunInTime_iff _ _ _).mp hv w
  simp only [decide_eq_true_eq] at h
  apply h.mono
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hm : max (2 * (w.length + 1)) (b * (w.length + 1)) ≤
      (b + 2) * (w.length + 1) := by
    rw [Nat.add_mul]
    exact max_le (by omega) (by omega)
  calc
    _ ≤ 4 * (w.length + 1) + (b + 2) * (w.length + 1) + 1 := by omega
    _ ≤ (b + 7) * (w.length + 1) := by ring_nf; omega

/-- Compute the normalized logarithmic width in linear time and logarithmic space.
**Proof sketch.** `exists_inputLengthTM` supplies the input length in binary, restores its
work heads to their origins and bounds their displacement by a constant times the answer
width plus one. A reversed native-bank embedding puts that counter tape beside a fresh
bank for a virtual-input `normalized_counter`. The latter emits the counter word's length
in binary, treating its empty input as length one; `length_bits_eq_log` and `logSpace_eq`
identify this value with the normalized logarithm. `seamCompTM_run_ofCfg` joins the phases
at the native counter's first exit. `bank_sum_bound` combines the native head envelope,
the hosted counter's time-derived space bound, and the virtual-input boundary cells.
The counter word has at most the normalized logarithmic width, and at most the original
input length, giving logarithmic space and linear total time. -/
private theorem logarithmic_computation :
    ∃ (M : FinTM Bool) (A : ℕ), ∀ x : List Bool,
      ∃ t ≤ A * (x.length + 1),
        M.ComputesInTime x (Complexity.logSpace x.length).bits t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ A * Complexity.logSpace x.length := by
  classical
  obtain ⟨K, S, fs, ds, R, entry, exit, C, counter⟩ := exists_inputLengthTM
  letI := fs
  letI := ds
  obtain ⟨V, A, hv⟩ := normalized_counter
  let k := K + (1 + V.k)
  let σ : Fin (K + 1) ↪ Fin k :=
    Fin.revPerm.toEmbedding.trans (Fin.castLEEmb (by dsimp only [k]; omega))
  let ι : Fin (1 + V.k) ↪ Fin k := Fin.natAddEmb K
  have shared : σ 0 = ι 0 := by
    apply Fin.ext
    change (K + 1) - 1 - 0 = K + 0
    omega
  let F := embedEmitTM σ R
  let E := embedEmitTM ι (vhostEmitTM V.tm)
  let H := seamCompTM F exit E (V.tm.q₀, true)
  let N : FinTM Bool :=
    { k := k
      State := S ⊕ (V.State × Bool)
      tm := { H with q₀ := Sum.inl entry } }
  let D := (K + 1) * (2 * C + 1) + V.k * (A + 1) + 2 * k + 3
  let B := C + 2 * A + 1 + 2 * D
  refine ⟨N, B, fun x => ?_⟩
  let y := x.length.bits
  let d₀ : Cfg (K + 1) Bool S x := Cfg.init entry x
  obtain ⟨t, ht, cut, heads, finished⟩ := counter d₀
    (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
    (by intro p _ _; rw [Cfg.init_workTapePos, zero_add, Cfg.init_workTapes])
    (by intro j _ p; rw [Cfg.init_workTapes])
  let d₁ : Cfg (K + 1) Bool S x :=
    { d₀ with
      state := some exit
      workTapes := fun j z =>
        if j = 0 ∧ d₀.workTapePos j ≤ z ∧ z < d₀.workTapePos j + (y.length : ℤ)
          then FinTM.bufferTape y (z - d₀.workTapePos j) else d₀.workTapes j z }
  let f₀ := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] d₀
  let f₁ := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] d₁
  have frun : F.runFrom f₀ t = f₁ := by
    rw [embedEmitTM_runFrom, finished]
  have fcut : ∀ u < t, (F.runFrom f₀ u).state ≠ some exit := by
    intro u hu
    rw [embedEmitTM_runFrom, embedEmitCfg_state]
    exact cut u hu
  have fstate : f₁.state = some exit := by
    rw [embedEmitCfg_state]
  have fword : f₁.workTapes (ι 0) = FinTM.bufferTape y := by
    rw [← shared, embedEmitCfg_selected_tape]
    funext z
    dsimp only [d₁, d₀]
    simp only [Cfg.init_workTapePos, Cfg.init_workTapes, zero_add, sub_zero,
      true_and]
    by_cases hz : 0 ≤ z ∧ z < (y.length : ℤ)
    · rw [if_pos hz]
    · rw [if_neg hz, FinTM.bufferTape_eq_none_of_not_mem y hz]
  have fpos : f₁.workTapePos (ι 0) = 0 := by
    rw [← shared, embedEmitCfg_selected_pos, Cfg.init_workTapePos]
  have fout : f₁.output = [] := by
    rw [embedEmitCfg_output, Cfg.init_output, List.nil_append]
  let v₀ := vhostCfg (V.tm.initCfg y) true f₁.inputPos []
  let e₀ := embedEmitCfg ι f₁.workTapes f₁.workTapePos [] v₀
  have estart : e₀ = f₁.mapState (fun _ => (V.tm.q₀, true)) := by
    apply embedEmitCfg_eq
    · simp only [v₀, vhostCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state,
        Cfg.mapState_state, fstate, Option.map_some]
    · dsimp only [v₀]
      simp only [vhostCfg_inputPos, Cfg.mapState_inputPos]
    · rw [vhostCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
        Cfg.mapState_output]
      simp only [List.nil_append]
      exact fout.symm
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have iz : i = 0 := Subsingleton.elim _ _
        subst i
        constructor
        · funext z
          dsimp only [v₀]
          simp only [vhostCfg_workTapes, Fin.addCases_left, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) fword.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_left, MultiTapeTM.initCfg_eq,
            Cfg.init_inputPos, Fin.val_one, Cfg.mapState_workTapePos]
          rw [show Fin.castAdd V.k (0 : Fin 1) = (0 : Fin (1 + V.k)) from rfl, fpos]
          norm_num
      · have outside : ι (Fin.natAdd 1 i) ∉ Set.range σ := by
          rintro ⟨j, hj⟩
          have hh : (σ j).val < K + 1 := j.rev.isLt
          have he : (σ j).val = K + (1 + i.val) := congrArg Fin.val hj
          omega
        have framed := embedEmitCfg_unselected σ (fun _ _ => none) (fun _ => 0) []
          d₁ (ι (Fin.natAdd 1 i)) outside
        constructor
        · funext z
          dsimp only [v₀]
          simp only [vhostCfg_workTapes, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapes, Cfg.mapState_workTapes]
          exact congrArg (fun f => f z) framed.1.symm
        · rw [vhostCfg_workTapePos, Fin.addCases_right, MultiTapeTM.initCfg_eq,
            Cfg.init_workTapePos, Cfg.mapState_workTapePos]
          exact framed.2.symm
    · intro j _
      exact ⟨funext fun z => (Cfg.mapState_workTapes _ _ j z).symm,
        (Cfg.mapState_workTapePos _ _ j).symm⟩
  have width : (if y = [] then [true] else y.length.bits) =
      (Complexity.logSpace x.length).bits := by
    by_cases hx : x.length = 0
    · simp only [y, hx, Nat.zero_bits, Complexity.logSpace_eq,
        Nat.log_zero_right, Nat.zero_add, Nat.one_bits, if_true]
    · have he := Complexity.LogProg.length_bits_eq_log hx
      have hn : y ≠ [] := by
        intro heq
        have hlen := congrArg List.length heq
        dsimp only [y] at hlen
        rw [he, List.length_nil] at hlen
        omega
      rw [if_neg hn]
      exact congrArg Nat.bits (he.trans (Complexity.logSpace_eq x.length).symm)
  let b := A * (y.length + 1)
  have vcomp : V.ComputesInTime y (Complexity.logSpace x.length).bits b := by
    rw [← width]
    exact hv y
  have tag : FinTM.VirtualTag (V.tm.initCfg y).inputPos true := by
    rw [FinTM.VirtualTag_iff, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      have : (1 : ℕ) ≠ 0 := by decide
      exact (this (by simpa only [Fin.val_one] using h)).elim
    · intro _
      rfl
  obtain ⟨tagEnd, _, vrun⟩ := vhostEmitTM_runFrom V.tm (V.tm.initCfg y) true tag
    f₁.inputPos [] b
  have erun : E.runFrom e₀ b =
      embedEmitCfg ι f₁.workTapes f₁.workTapePos []
        (vhostCfg (V.tm.runFrom (V.tm.initCfg y) b) tagEnd f₁.inputPos []) := by
    rw [embedEmitTM_runFrom, vrun]
  have hrun := seamCompTM_run_ofCfg F exit E (V.tm.q₀, true)
    frun fstate fcut (estart ▸ erun)
  have fstart : f₀ = Cfg.init entry x := by
    apply embedEmitCfg_eq
    · rw [Cfg.init_state, Cfg.init_state]
    · rw [Cfg.init_inputPos, Cfg.init_inputPos]
    · rw [Cfg.init_output, Cfg.init_output, List.nil_append]
    · intro i
      constructor
      · funext z
        rw [Cfg.init_workTapes, Cfg.init_workTapes]
      · rw [Cfg.init_workTapePos, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext z
        rw [Cfg.init_workTapes]
      · rw [Cfg.init_workTapePos]
  have nstart : N.tm.initCfg x = f₀.mapState Sum.inl := by
    rw [MultiTapeTM.initCfg_with_q₀, fstart]
    apply Cfg.ext
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.init_state, Option.map_some]
    · simp only [Cfg.init_inputPos, Cfg.mapState_inputPos]
    · funext j z
      simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    · funext j
      simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    · simp only [Cfg.init_output, Cfg.mapState_output]
  refine ⟨t + 1 + b, ?_, ?_, ?_⟩
  · have hb : b ≤ A * (x.length + 1) := Nat.mul_le_mul_left A
      (Nat.add_le_add_right (length_bits_le_self x.length) 1)
    calc
      _ ≤ C * (x.length + 1) + (x.length + 1) + A * (x.length + 1) := by omega
      _ = (C + A + 1) * (x.length + 1) := by ring
      _ ≤ B * (x.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [B]; omega)
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [nstart, MultiTapeTM.runFrom_with_q₀, hrun]
    obtain ⟨vh, vo⟩ := (FinTM.computesInTime_iff _ _ _ _).mp vcomp
    simp only [Cfg.mapState_state, Cfg.mapState_output, embedEmitCfg_state,
      embedEmitCfg_output, vhostCfg_state, vhostCfg_output, vh, vo,
      Option.map_none, List.nil_append, and_self]
  · rw [nstart, space_with_start]
    have nativeSpace : R.spaceUsed d₀ t ≤ (K + 1) * (2 * (C * (y.length + 1)) + 1) :=
      R.spaceUsed_le_of_abs_le d₀ t (C * (y.length + 1)) heads
    have fspace : F.spaceUsed f₀ t ≤
        (K + 1) * (2 * C + 1) * (y.length + 1) + k := by
      have bound := bank_sum_bound σ (fun j => F.spaceUsedByTape f₀ t j)
        (fun i => R.spaceUsedByTape d₀ t i) 1
        (fun i => by
          dsimp only [f₀, F]
          rw [(embedEmitTM_visitedByTapeHead σ R (fun _ _ => none) (fun _ => 0) [] d₀ t i).2])
        (fun j hj => by
          dsimp only [f₀, F]
          rw [(embedEmitTM_visitedByTapeHead_frame σ R (fun _ _ => none)
            (fun _ => 0) [] d₀ t j hj).2])
      dsimp only at bound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at bound
      apply bound.trans
      apply Nat.add_le_add_right
      apply nativeSpace.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      ring_nf
      omega
    have espace : E.spaceUsed e₀ b ≤ V.k * (A * (y.length + 1) + 1) + y.length + 2 + k := by
      have bound := bank_sum_bound ι (fun j => E.spaceUsedByTape e₀ b j)
        (fun i => (vhostEmitTM V.tm).spaceUsedByTape v₀ b i) 1
        (fun i => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead ι (vhostEmitTM V.tm) f₁.workTapes
            f₁.workTapePos [] v₀ b i).2])
        (fun j hj => by
          dsimp only [e₀, E]
          rw [(embedEmitTM_visitedByTapeHead_frame ι (vhostEmitTM V.tm) f₁.workTapes
            f₁.workTapePos [] v₀ b j hj).2])
      dsimp only at bound
      simp only [← MultiTapeTM.spaceUsed_eq_sum, Nat.mul_one] at bound
      have hs := vhostEmitTM_spaceUsed_le V.tm (V.tm.initCfg y) true tag f₁.inputPos [] b
      have vs : V.tm.spaceUsed (V.tm.initCfg y) b ≤ V.k * (A * (y.length + 1) + 1) :=
        vcomp.spaceUsed_le b
      exact bound.trans (Nat.add_le_add_right (hs.trans (by omega)) _)
    have total := seamCompTM_spaceUsed_le_add_ofCfg F exit E (V.tm.q₀, true)
      (T₂ := b) frun fstate fcut
    rw [← estart] at total
    have bound : H.spaceUsed (f₀.mapState Sum.inl) (t + 1 + b) ≤ D * (y.length + 1) := by
      apply (total.trans (Nat.add_le_add fspace espace)).trans
      have vk : V.k * (A * (y.length + 1) + 1) ≤ V.k * ((A + 1) * (y.length + 1)) := by
        apply Nat.mul_le_mul_left
        ring_nf
        omega
      have kk : k ≤ k * (y.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      calc
        _ ≤ (K + 1) * (2 * C + 1) * (y.length + 1) + k * (y.length + 1) +
            (V.k * ((A + 1) * (y.length + 1)) + 2 * (y.length + 1) + k * (y.length + 1)) := by omega
        _ = ((K + 1) * (2 * C + 1) + V.k * (A + 1) + 2 * k + 2) * (y.length + 1) := by ring
        _ ≤ D * (y.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [D]; omega)
    apply bound.trans
    have logpos : 1 ≤ Complexity.logSpace x.length := by rw [Complexity.logSpace_eq]; omega
    have widthle : y.length ≤ Complexity.logSpace x.length := by
      rw [Complexity.logSpace_eq]
      exact Complexity.LogProg.length_bits_le_log x.length
    calc
      _ ≤ D * (2 * Complexity.logSpace x.length) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * D) * Complexity.logSpace x.length := by ring
      _ ≤ B * Complexity.logSpace x.length := Nat.mul_le_mul_right _ (by dsimp only [B]; omega)

/-- **The word size is computable within `TW` and `SW`**: some finite binary machine, on every
input `x`, halts within `TW |x|` steps with the binary representation of `W (|x|)` on its output
tape (`Nat.bits`, as in `Complexity.SpaceConstructible` and `Complexity.TimeConstructible`), having
visited at most `SW |x|` work cells up to then. The stage-2 machine runs it once, at the start,
with its output captured on a work tape, and pays `TW` and `SW` once. Deviation: it bounds time
and space together, where [AB09] has separate time- and space-constructibility (§1.3, §4.1);
design §16b item 1. -/
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length

/-- A word size computable within `TW` and `SW` is computable within any larger bounds.

**Proof sketch.** The same machine and halting times; `t ≤ TW n ≤ TW' n`, and the space bound
weakens pointwise. -/
theorem WordSizeComputable.mono {W TW SW TW' SW' : ℕ → ℕ} (h : WordSizeComputable W TW SW)
    (hT : ∀ n, TW n ≤ TW' n) (hS : ∀ n, SW n ≤ SW' n) : WordSizeComputable W TW' SW' := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun x => ?_⟩
  obtain ⟨t, ht, hcomp, hspace⟩ := hM x
  exact ⟨t, ht.trans (hT x.length), hcomp, hspace.trans (hS x.length)⟩

/-- **Logarithmic word sizes** (the P and L grades): for every `c`, the word size
`c · (⌊log₂ n⌋ + 1)` is computable in linear time and logarithmic space.

**Proof sketch.** `logarithmic_computation` computes the normalized logarithm in linear
time and logarithmic space, including its value one on the empty input. `scale_computes`
then captures that binary answer, multiplies it by `c` using `constant_multiplier`, and
emits the result. `Turing.length_bits_le_self` and `Complexity.logSpace_le_succ` absorb
the extra binary-width time into a linear bound. The positivity of the normalized
logarithm absorbs the constant space allowance. -/
theorem wordSizeComputable_logSpace (c : ℕ) :
    ∃ a : ℕ, WordSizeComputable (fun n => c * Complexity.logSpace n) (fun n => a * (n + 1))
      (fun n => a * Complexity.logSpace n) := by
  obtain ⟨M, a, hm⟩ := logarithmic_computation
  obtain ⟨N, A, B, scaled⟩ := scale_computes M c
  let d := a + 2 + B + A * (a + 2)
  refine ⟨d, N, fun x => ?_⟩
  obtain ⟨t, ht, comp, space⟩ := hm x
  obtain ⟨u, hu, answer, used⟩ := scaled x (Complexity.logSpace x.length) t comp
  have one : 1 ≤ Complexity.logSpace x.length := by rw [Complexity.logSpace_eq]; omega
  have width := length_bits_le_self (Complexity.logSpace x.length)
  have linear := Complexity.logSpace_le_succ x.length
  refine ⟨u, ?_, answer, ?_⟩
  · have hb : B ≤ B * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc
      _ ≤ t + 2 * (Complexity.logSpace x.length).bits.length + B := hu
      _ ≤ a * (x.length + 1) + 2 * (x.length + 1) + B * (x.length + 1) := by omega
      _ = (a + 2 + B) * (x.length + 1) := by ring
      _ ≤ d * (x.length + 1) := Nat.mul_le_mul_right _ (by dsimp only [d]; omega)
  · calc
      _ ≤ A * (M.tm.spaceUsed (M.tm.initCfg x) t +
          (Complexity.logSpace x.length).bits.length + 1) := used
      _ ≤ A * (a * Complexity.logSpace x.length + Complexity.logSpace x.length +
          Complexity.logSpace x.length) := by
        apply Nat.mul_le_mul_left
        omega
      _ = (A * (a + 2)) * Complexity.logSpace x.length := by ring
      _ ≤ d * Complexity.logSpace x.length := Nat.mul_le_mul_right _ (by dsimp only [d]; omega)

/-- **Space-constructible word sizes** (Savitch's shape): if `S` is space-constructible, then for
every `c` the word size `c · S(n)` is computable in space `O(S(n))`, within some time bound `TW`
that is not controlled and that the space grades do not need.

**Proof sketch.** Read the witness through `Complexity.spaceConstructible_iff`.
`Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` gives a uniform
configuration-count deadline and retains the original space bound at that deadline.
`scale_computes` captures the witness's binary output, multiplies it by `c`, and emits
it. `Turing.length_bits_le_self` bounds the captured width by `S`, while
`logSpace ≤ S` and `logSpace_eq` give `1 ≤ S`. Thus all extra space is absorbed into a
constant times `S`. The source deadline plus the scaling overhead defines `TW`. -/
theorem wordSizeComputable_of_spaceConstructible {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ) :
    ∃ (a : ℕ) (TW : ℕ → ℕ), WordSizeComputable (fun n => c * S n) TW (fun n => a * S n) := by
  obtain ⟨lower, C, _, M, hm⟩ := (Complexity.spaceConstructible_iff S).mp hS
  obtain ⟨ht, hs⟩ := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨N, A, B, scaled⟩ := scale_computes M c
  let T := fun n => M.configBound n (C * S n)
  refine ⟨A * (C + 2), (fun n => T n + 2 * (S n).bits.length + B), N, ?_⟩
  intro x
  obtain ⟨u, hu, comp, space⟩ := scaled x (S x.length) (T x.length)
    ((FinTM.computesFunInTime_iff _ _ _).mp ht x)
  refine ⟨u, hu, comp, space.trans ?_⟩
  have one : 1 ≤ S x.length := by
    have hh := lower x.length
    rw [Complexity.logSpace_eq] at hh
    omega
  have width := length_bits_le_self (S x.length)
  have hspace := hs x (T x.length)
  calc
    _ ≤ A * (C * S x.length + S x.length + S x.length) := by
      apply Nat.mul_le_mul_left
      omega
    _ = _ := by ring

/-! ## Polynomial word sizes -/

/-- **A time-constructible function is a word size computable in time and space linear in its
value.** [AB09, §1.3]

**Proof sketch.** `Complexity.timeConstructible_iff` gives a machine writing `Nat.bits (T |x|)`
within `c·(T |x| + 1)` steps. Its visited work cells are at most its number of tapes times the
time plus one (`Turing.MultiTapeTM.spaceUsed_le_mul_succ`). The coefficient
`(M.k + 1)·(c + 1)` bounds both the deadline and these visited cells by a constant times
`T |x| + 1`. -/
theorem wordSizeComputable_of_timeConstructible {T : ℕ → ℕ}
    (hT : Complexity.TimeConstructible T) :
    ∃ a : ℕ, WordSizeComputable T (fun n => a * (T n + 1)) (fun n => a * (T n + 1)) := by
  obtain ⟨_, c, _, M, hM⟩ := (Complexity.timeConstructible_iff T).mp hT
  refine ⟨(M.k + 1) * (c + 1), M, fun x => ?_⟩
  refine ⟨c * (T x.length + 1), ?_, hM x, ?_⟩
  · exact Nat.mul_le_mul_right _ (by nlinarith)
  · calc
      _ ≤ M.k * (c * (T x.length + 1) + 1) :=
        MultiTapeTM.spaceUsed_le_mul_succ _ _ _
      _ ≤ M.k * ((c + 1) * (T x.length + 1)) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ ≤ (M.k + 1) * ((c + 1) * (T x.length + 1)) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = _ := by ring

/-- **Polynomial word sizes**: `n ↦ C·(n+1)^(c+1)`, for `C > 0`, is a word size computable within
time and space `a·(n+1)^(c+1)`. Words this wide hold, for instance, residues modulo a prime of
polynomially many bits. [AB09, §1.3]

**Proof sketch.** `wordSizeComputable_of_timeConstructible` applied to
`Complexity.timeConstructible_poly C c hC`, then `WordSizeComputable.mono` with
`C·(n+1)^(c+1) + 1 ≤ (C + 1)·(n+1)^(c+1)`. Multiplying the witness's coefficient by
`C + 1` gives the same polynomial bound for time and space. -/
theorem wordSizeComputable_poly (C c : ℕ) (hC : 0 < C) :
    ∃ a : ℕ, WordSizeComputable (fun n => C * (n + 1) ^ (c + 1))
      (fun n => a * (n + 1) ^ (c + 1)) (fun n => a * (n + 1) ^ (c + 1)) := by
  obtain ⟨a, hW⟩ := wordSizeComputable_of_timeConstructible
    (Complexity.timeConstructible_poly C c hC)
  have bound (n : ℕ) : a * (C * (n + 1) ^ (c + 1) + 1) ≤
      (a * (C + 1)) * (n + 1) ^ (c + 1) := by
    have hp : 1 ≤ (n + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ a * ((C + 1) * (n + 1) ^ (c + 1)) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  exact ⟨a * (C + 1), hW.mono bound bound⟩

end WordRAM
