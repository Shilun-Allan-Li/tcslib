/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the primitive catalog

The instruction set of the machine-construction library
(`machine-library-design.md` §4, P1–P12): the timed string functions every
Chapter-2 fill batch privately rebuilt, stated once as machine contracts.
`Turing.FinTM.computesFunInTime_id` and
`Turing.FinTM.computesFunInTime_const` (in
`TCSlib.Complexity.TuringMachine.Composition`) are catalog entries P1–P2
and already proved; this module states the rest.

**Status: proved.** Every theorem below is proved; roughly half were
harvests — their fills adapted already-proved private constructions from
the Chapter-2 epoch-2 batches (named per entry) — and the rest are new
small machines. Following the house idiom of
`TCSlib.Complexity.TuringMachine.Composition`, the contracts are
existentially packaged; each fill implements a named private machine with
its run invariants and closes the existential. Multi-argument interfaces
go through `Turing.pairEncode`, whose self-delimiting grammar lets a
pipeline stage **thread the original input through its output** — the
`pairLenCheck` and `stripLast` contracts below are deliberately stated in
that threaded form, which is exactly how the Chapter-2 verifier
constructions consume them. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

**Catalog refinements at spec time** (recorded against the frozen design
§4): P6 is realized as the fixed-first-component encoder plus the threaded
extractors/validity test; P7 (replicate) is subsumed by the unary clause of
P5, whose instances are what the emission customers actually consume; P8
is realized in threaded form (`pairLenCheck`); P12 (`clearTM`) has no
standalone string-function contract — clearing is intra-machine and lives
in the loop fill's toolkit. **Round-2 additions** (per round-1 finding 3:
the extractors discard the other component by design, and sequential
composition alone never yields simultaneous access to two results): P13
`pairConcat` (the D-WRAP shape), P14 `pairDup` (the entry stage of
data-retaining pipelines), and the threaded-map combinator `pairMapSnd`;
P10's narrowing is recorded, and result-bearing search is now
`Turing.FinTM.exists_loopFindTM` (`machine-library-design.md` §9b).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
  folklore tape subroutines of the textbook's simulation arguments.)

**Implementation note (batch P).** The first eleven targets in the batch
brief's fill order and the four continuation targets `pairLenCheck`,
`stripLast`, `pairMapSnd`, and `splitSolve` are proved. The original spec-phase
prose above and on the contracts is retained as the audit record. The length
counter is obtained from the public `Complexity.timeConstructible_id`, whose
proved machine implements precisely the sketched amortized counter. The three
extractors share one private buffered parser, so suffix-only extraction also
buffers and replays silently before copying the suffix; its linear envelope
is unchanged. The fixed-width incrementer adapts the enumerator's carry
semantics to two native-input scans, validating before physical emission.


**Implementation note (batch P2).** The threaded length checker, marker stripper,
threaded map, and split search are proved. The length checker composes the existing
buffered first extractor with the unary generator, captures the result with
`capture_run`, then reparses and counts down on the native payload. Malformed
inputs emit only `[false]`. The marker stripper first guards on a valid
extracted suffix containing a true bit; the successful branch buffers the
whole original encoding, erases its final marker/false-run, and replays the
retained encoding. The guard is complete before any physical output. Both
routes reuse the in-file parser/scan invariant patterns and proved public
wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
component for the threaded map, with its time evaluated at the actual suffix
length; the retained-prefix/captured-output controller is proved below.


**Implementation note (batch P3).** The threaded map is proved.
`pairMapTM` captures `catalogPayload_computes` on the original physical input,
rewinds the capture and input, validates without emission, then replays the
original encoded prefix and captured result. `pairMap_computes` bounds this
controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
All original contract docstrings are retained as the audit record.

The split-search theorem is proved. Its private components include the unary
orbit/search bridges and
`splitSolve_of_body`, which closes the public result only when supplied the
actual startup and round contracts; a candidate-preserving unary-bank
preparer; a counted source-simulation correspondence; the generator's exact
loop endpoint; and a scratch-restoration controller with a positive first
return and no earlier visit to its return state. The combined `splitBodyTM`
and `splitBody_round` assemble these components and prove `hround`.
-/

/-! Batch P4 closure note: the split-search body is now constructed and proved.
`splitBodyTM` separates preparation, counted source evaluation, checked rewind,
rejection restoration, and native-bit emission into disjoint finite phases.
`splitBody_round` composes their exact seams and proves positive duration and
strict-interior anchor exclusion, including the arbitrary-bit past-end stall.
`splitEmit_run` supplies the native-slice payload; `splitBody_envelope` accounts
for every phase within the common polynomial bound. Both exponent cases
instantiate this body through the proved `splitSolve_of_body` loop closure.
All fifteen primitive contracts are now proved without admissions. Earlier
spec/checkpoint status notes above are retained as historical documentation. -/

namespace Turing.FinTM

/-! Implementation note (batch P): the private prefix construction below is
adapted in-file from `ClassNP/Reductions.lean`; no private declaration from
that module is used. Completed contracts retain their audited spec docstrings. -/

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def catalogPrefixTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (catalogPrefixTM w).tm.runFrom ((catalogPrefixTM w).tm.initCfg x) i =
      catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [catalogPrefixCfg, catalogPrefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, catalogPrefixCfg, catalogPrefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (catalogPrefixTM w).tm.runFrom
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [catalogPrefixCfg]; omega) (by omega)
    change ((catalogPrefixTM w).tm.tr ⟨w.length, by omega⟩
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [catalogPrefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, catalogPrefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- Prefixing computes `w ++ x` in exactly the bound `|w| + |x| + 1`,
including the final blank-reading halting step.

**Proof sketch.** Concatenate the fixed-word emission run and the input-copy
run; the input head then scans the right boundary, so one final step halts
without emitting anything further. This also covers empty prefix and input. -/
private lemma catalogPrefixTM_computes (w : List Bool) :
    (catalogPrefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [catalogPrefixTM, catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) j =
      scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · simp only [Action.apply, scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def pairDupTM : FinTM Bool where
  k := 0
  State := Fin 5
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some 1⟩
          | none => ⟨.neg, fun j => j.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun j => j.elim0, inp, some 0⟩
        | 2 => match inp with
          | some _ => controlAction .neg (some 2)
          | none => controlAction .pos (some 3)
        | 3 => ⟨0, fun j => j.elim0, some true, some 4⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 4⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Every two first-pass transitions emit one doubled input bit.
**Proof sketch.** The first transition emits while staying at the scanned
cell, and the second emits that same bit and advances. Induction concatenates
these two-step blocks, leaving the right blank for the separator transition. -/
private lemma pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * j) =
      scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [scanCfg, pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : pairDupTM.tm.step
        (scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [pairDupTM, Action.apply, scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma pairDup_computes (x : List Bool) :
    pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : pairDupTM.tm.step (scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [pairDupTM, c]
    · simpa [pairDupTM, Action.apply, scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [pairDupTM, Action.apply, scanCfg, c]
  have hr := rewind_scan pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, pairDupTM, c, scanCfg, Action.apply, List.append_assoc]
  have h1 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    scanCopy_finish pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (scanCfg x (some q) pre.length (by omega) out) =
        scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [scanCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
      · rfl
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- A true-prefix scan either remains silent or emits one false per true.
**Proof sketch.** Induct on the prefix length. Taking a shorter prefix gives
the induction hypothesis, and the last entry of the longer prefix identifies
the symbol read by the next transition. -/
private lemma scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (scanCfg x (some q) 0 (by omega) []) j =
      scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
  intro j
  induction j with
  | zero => intro hj hp; cases emit <;> rfl
  | succ j ih =>
    intro hj hp
    have hshort : x.take j = List.replicate j true := by
      have h := congrArg (List.take j) hp
      simpa only [List.take_take, List.take_replicate, Nat.min_eq_left (by omega : j ≤ j + 1)] using h
    have hb : x[j]? = some true := by
      have h := congrArg (fun w : List Bool => w[j]?) hp
      simpa [List.getElem?_take, Nat.lt_succ_self] using h
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) hshort]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · cases emit <;> simp [Action.apply, scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma incFixed_cases (x : List Bool) :
    (x = List.replicate x.length true ∧ incFixed x = none) ∨
      ∃ j rest, x = List.replicate j true ++ false :: rest ∧
        incFixed x = some (List.replicate j false ++ true :: rest) := by
  induction x with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b x ih =>
    cases b with
    | false => exact Or.inr ⟨0, x, rfl, rfl⟩
    | true =>
      rcases ih with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
      · exact Or.inl ⟨by simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hx, by simp [incFixed, hinc]⟩
      · exact Or.inr ⟨j + 1, rest, by simp [hx, List.replicate_succ],
          by simp [incFixed, hinc, List.replicate_succ]⟩

/-- Detect a nonoverflowing word silently, rewind, then perform the carry
while emitting. This is the enumerator's carry discipline adapted to native
input and append-only output; unlike the in-place harvest, it validates first. -/
private def incFixedTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, none, some 0⟩
          | some false => controlAction .neg (some 1)
          | none => controlAction 0 none
        | 1 => match inp with
          | some _ => controlAction .neg (some 1)
          | none => controlAction .pos (some 2)
        | 2 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, some false, some 2⟩
          | some false => ⟨.pos, fun j => j.elim0, some true, some 3⟩
          | none => controlAction 0 none
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 3⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Fixed-width increment is computed within `3(|x|+1)` steps, with no output
on overflow, including the empty word.
**Proof sketch.** The all-true case scans and halts silently. Otherwise let
`j` be the first false's index. Detection plus rewind costs `2j+2`; carry
emission and suffix copy cost `|x|+1`. Since `j < |x|`, the advertised
linear envelope covers the whole run. -/
private lemma incFixed_computes (x : List Bool) :
    incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg], hr]
      unfold MultiTapeTM.step
      change ((incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [incFixedTM, controlAction, Action.apply, scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg],
        scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [incFixedTM, controlAction, Action.apply, scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : incFixedTM.tm.runFrom (scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        scanTrues_run incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
      · rfl
    have hcopy := scanCopy_suffix incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (scanCfg x (some q) i (by omega) out) =
      scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
  · rfl

/-- Scan aligned pairs of bits, retaining just the first bit of the current
block. Only a terminal verdict transition emits output. -/
private def pairValidTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q, inp with
        | none, some b => ⟨.pos, fun j => j.elim0, none, some (some b)⟩
        | some b, some c =>
          if b = c then ⟨.pos, fun j => j.elim0, none, some none⟩
          else ⟨.pos, fun j => j.elim0, some (!b && c), none⟩
        | _, none => ⟨0, fun j => j.elim0, some false, none⟩ }

/-- One aligned block either continues silently or halts with its verdict. -/
private lemma pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    pairValidTM.tm.runFrom (scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
  have h2 := scanStep_right pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [pairValidTM, h])
  change pairValidTM.tm.step (pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (pairValidTM.tm.step (pairValidTM.tm.step _)).state = none ∧
      (pairValidTM.tm.step (pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    cases b <;> simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [scanCfg, pairDecode]

/-- The validity test starts with an empty aligned prefix and uses the
linear envelope `|x|+1`. -/
private lemma pairValid_computes (x : List Bool) :
    pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := pairValid_run x x [] rfl
  have hinit : pairValidTM.tm.initCfg x = scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [pairValidTM, scanCfg]
  have h : pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht

/-- A shared extractor buffers the decoded prefix, validates the separator,
rewinds and replays the buffer, then optionally copies the suffix. The two
flags select the first component, the second, or their concatenation. -/
private def pairExtractTM (first second : Bool) : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Fin 3
  tm :=
    { q₀ := .inl none
      tr := fun q inp work => match q with
        | .inl none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .inl (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.inl none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some (.inr 0)⟩
        | .inr q => match q.val with
          | 0 => match work 0 with
            | some _ => ⟨0, fun _ => (none, .neg), none, some (.inr 0)⟩
            | none => ⟨0, fun _ => (none, .pos), none, some (.inr 1)⟩
          | 1 => match work 0 with
            | some b => ⟨0, fun _ => (none, .pos), if first then some b else none, some (.inr 1)⟩
            | none => ⟨0, fun _ => (none, 0), none, some (.inr 2)⟩
          | _ => if second then match inp with
              | some b => ⟨.pos, fun _ => (none, 0), some b, some (.inr 2)⟩
              | none => ⟨0, fun _ => (none, 0), none, none⟩
            else ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The shared extractor's one-buffer configurations. -/
private def extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairExtractTM first second).tm.step
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [extractCfg, hx])
  · funext i; simp [pairExtractTM, Action.apply, extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _) = _
  rw [extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [extractCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ := by
    exact moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [pairExtractTM, Action.apply, extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (pairExtractTM first second).tm.step
        (extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) j =
      extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht

/-- Replay's right-blank test dispatches to the suffix state silently. -/
private lemma extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (pairExtractTM first true).tm.runFrom
      (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairExtractTM, Action.apply, extractCfg, hx]
    · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    · simp [pairExtractTM, Action.apply, extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (pairExtractTM first true).tm.step
        (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, extract_rewind first second x a _ _ _ (by omega),
      extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, pairExtractTM, extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).state = none ∧
      ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).output = _
    rw [extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    cases b <;> simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [extract_block first second x pre rest a true false hx]
        simp [extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The three extractor modes share the uniform linear envelope `5(|x|+1)`.
The initial buffer and decoded prefix are empty. -/
private lemma pairExtract_computes (first second : Bool) (x : List Bool) :
    (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := extract_run first second x x [] [] rfl
  have hinit : (pairExtractTM first second).tm.initCfg x =
      extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairExtractTM, extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-! The unary polynomial generator below is adapted privately from
`ClassNP/TMSAT.lean`, including its exact loop-depth ledger. -/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance catalogPolyControlFintype (c C : ℕ) : Fintype (CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (CatalogPolyControl c C) :=
  (proxy_equiv% (CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : CatalogPolyControl c C) : Action (c + 1) Bool (CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := CatalogPolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (catalogPolyMove i d s').apply (catalogPolyCfg x q s h o) =
      catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [catalogPolyMove, catalogPolyCfg, Action.apply, hj]
  · simp [catalogPolyMove, catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [catalogPolyCfg] using catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [catalogPolyCfg] using catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (catalogPolyCost q C i + 2) + q + 2) =
      catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (catalogPolyUnaryTM c C).tm.runFrom
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (catalogPolyCost q C i + 2) =
        catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, hj]
      have hs : (catalogPolyUnaryTM c C).tm.step (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) 1 =
            catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (catalogPolyUnaryTM c C).tm.runFrom
            (catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (catalogPolyCost q C i) =
            catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (catalogPolyCost q C (i - 1) + 2) + q + 2 =
              catalogPolyCost q C i := by
            calc
              _ = catalogPolyCost q C (i - 1 + 1) := rfl
              _ = catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show catalogPolyCost q C i + 2 = 1 + catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (catalogPolyUnaryTM c C).tm.step
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
          catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (catalogPolyCost q C i + 2) + q + 2 =
          (catalogPolyCost q C i + 2) + (r * (catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma catalogPolyTape_write (q : ℕ) :
    Function.update (catalogPolyTape q) (q : ℤ) (some true) = catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      catalogPolyCost q C (r + 1) = q * (catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x) i =
      catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, catalogPolyCopyCfg, catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact catalogPolyTape_write i
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma catalogPoly_start (c C : ℕ) (x : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCopyCfg c C x x.length (le_refl _)) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact catalogPolyTape_write x.length
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma catalogPoly_unary_computes (c C : ℕ) :
    (catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost (x.length + 1) C (c + 1)) =
      catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  have hbase : (catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, catalogPoly_start, hloop]
    simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring


/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => lenAction M 0 0 (some false) none
            | some _ => lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some b => lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some d => if b = d then lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then lenAction M 0 0 (some false) none
          else lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (lenAction M m d b q').apply (lenCfg M c q i hi r) =
      {lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [lenAction, lenCfg, Action.apply, hk]
    · simpa [lenAction, lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [lenCfg_read]
      simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (pairCountTM M).tm.step
          (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [pairCountTM, hin, hw]
        exact lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho

/-- The first half of an aligned block changes only finite control and the
input position; countdown cells remain untouched during validation. -/
private lemma lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (pairCountTM M).tm.step
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairCountTM, hin]
  exact lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (pairCountTM M).tm.runFrom
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (pairCountTM M).tm.step ((pairCountTM M).tm.step _) = _
  rw [lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).state = none ∧
      ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).output = _
    rw [lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    cases b <;> simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [lenParse_block M c pre rest true false r hx]
        simp [lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma catalogRewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- A completed generator is captured without physical output, then its
last cell and the first physical input cell are exposed for comparison.
**Proof sketch.** Use the least source halting time to discharge `capture_run`'s
liveness guard. One step moves the capture head left; quantitative rewind
restores the input head while preserving the completed generator bank. -/
private lemma lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
        lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairCountTM M).State := Sum.inl
  let ret : (pairCountTM M).State := .inr (.inl 0)
  have hinit : (pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (pairCountTM M).State x :=
    {lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [pairCountTM, ret, lenAction, Action.apply, captureCfg, ready, lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairCountTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inr none)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) ready rfl
  refine ⟨t + 1 + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [hback, hr]
    rfl

/-- The captured checker compares a valid pair's payload with the length of
the generator's output, and rejects every malformed input.
**Proof sketch.** Compose the silent capture/rewind prefix with the aligned
parser and countdown ledger, then absorb the two linear scans. -/
private lemma pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def rawStripTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some b => ⟨0, fun _ => (some none, .neg), none, some (if b then 2 else 1)⟩
      | 2 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 3⟩
      | _ => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 3⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Raw-strip configurations expose the indexed input and a contiguous buffer. -/
private def stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) j =
      stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [rawStripTM, stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [rawStripTM, stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    rawStripTM.tm.runFrom
      (stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : rawStripTM.tm.step
        (stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    rawStripTM.tm.runFrom (stripCfg x (some 3) i hi a 0 []) j =
      stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, rawStripTM, stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    rawStripTM.tm.step
      (stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [stripCfg, rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, rawStripTM, stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      simpa [splitAtLastTrue] using rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma rawStrip_computes : rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) (x.length + 1) =
      stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', rawStrip_copy x x.length (le_refl _)]
    have hin : (stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [rawStripTM, stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := rawStrip_trim x x x.length (le_refl _)
  have hc : rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def anyTrueTM : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | some false => ⟨.pos, fun i => i.elim0, none, some ()⟩
      | some true => ⟨0, fun i => i.elim0, some true, none⟩
      | none => ⟨0, fun i => i.elim0, some false, none⟩ }

/-- The marker-existence scan halts within one more than the remaining length.
**Proof sketch.** False bits advance silently; a true or the right boundary
emits the corresponding verdict and halts. -/
private lemma anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, anyTrueTM, Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [hx, anyTrueTM, Action.apply, scanCfg]
    | false =>
      have hs := scanStep_right anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma anyTrue_computes : anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := anyTrue_run x x [] rfl
  have hinit : anyTrueTM.tm.initCfg x = scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma catalogMarker_cases (v : List Bool) :
    (v.any id = false ∧ splitAtLastTrue v = none) ∨
      ∃ u, v.any id = true ∧ splitAtLastTrue v = some u ∧
        ∀ pre, splitAtLastTrue (pre ++ v) = some (pre ++ u) := by
  induction v using List.reverseRecOn with
  | nil => left; simp [splitAtLastTrue]
  | append_singleton v b ih =>
    cases b with
    | false =>
      rcases ih with ⟨ha, hs⟩ | ⟨u, ha, hs, hp⟩
      · left; simpa [splitAtLastTrue] using And.intro ha hs
      · right
        refine ⟨u, by simpa using ha, by simpa [splitAtLastTrue] using hs, ?_⟩
        intro pre
        simpa [splitAtLastTrue, List.append_assoc] using hp pre
    | true =>
      right
      refine ⟨v, by simp, by simp [splitAtLastTrue], ?_⟩
      intro pre
      simp [splitAtLastTrue]

/-- The total suffix extractor never lengthens its input, including malformed
inputs, whose extracted suffix is empty. -/
private lemma catalogPayload_length (x : List Bool) :
    ((pairDecode x).map Prod.snd |>.getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some p =>
    rcases p with ⟨a, b⟩
    have hx := Turing.eq_pairEncode_of_pairDecode x a b hd
    simp only [Option.map_some, Option.getD_some]
    rw [hx]
    simp only [pairEncode, List.length_append]
    omega

/-- Run the given machine on the parsed payload, using the public relocated
composition engine and the payload's actual length. This is the quantitative
continuation interface for the threaded map; it does not yet emit the retained
first component or capture the transformed payload for that emission.
**Proof sketch.** The proved extractor validates and buffers before emission.
`bufferedComp_start` installs its suffix as virtual input; `bufferedSecondCfg_run`
simulates the payload machine with `bufferTape`/`virtualMove`. Charge its time
to `Tg |x|` using the nonexpanding suffix bound, not the extractor's larger
running-time bound. This distinction is necessary for arbitrary monotone `Tg`. -/
private lemma catalogPayload_computes {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    (bufferedCompTM (pairExtractTM false true) Mg).ComputesFunInTime
      (fun x => g ((pairDecode x).map Prod.snd |>.getD []))
      (fun n => 6 * (n + 1) + Tg n + 1) := by
  intro x
  let y := (pairDecode x).map Prod.snd |>.getD []
  have hF : (pairExtractTM false true).ComputesInTime x y (5 * (x.length + 1)) := by
    have hf := pairExtract_computes false true x
    cases hd : pairDecode x with
    | none => simpa [y, hd] using hf
    | some p => cases p; simpa [y, hd] using hf
  have hlen : y.length ≤ x.length := catalogPayload_length x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start (pairExtractTM false true) Mg x y (5 * (x.length + 1)) hF
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run (pairExtractTM false true) Mg (Mg.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (Tg y.length)
  have hc := (computesInTime_iff _ _ _ _).mp (hg y)
  have hbase : (bufferedCompTM (pairExtractTM false true) Mg).ComputesInTime x (g y)
      (a + Tg y.length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  have htime : Tg y.length ≤ Tg x.length := hTg hlen
  exact hbase.mono (by dsimp only; omega)

/-- **P3, prepend a fixed word** (harvest: the HALT
batch's `prefixTM`/`prefixTM_computes`, whose promotion the batch formally
requested). Emitting the fixed word `w` and then copying the input is
computable in linear time; the constant may depend on `w`, which is fixed
before the machine.

**Construction sketch.** The fixed emission chain of
`Turing.FinTM.computesFunInTime_const` for `w`, then the one-state copy
scan of `Turing.FinTM.computesFunInTime_id`; the harvest source proves the
exact budget `|w| + |x| + 1`. -/
theorem computesFunInTime_prepend (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) fun n => c * (n + 1) := by
  refine ⟨catalogPrefixTM w, w.length + 1, fun x => (catalogPrefixTM_computes w x).mono ?_⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- **P4, input length in binary** (new; the unary
scan is a one-state sweep and the binary counter discipline is the
`Turing.incFixed` carry loop). The little-endian binary representation
`Nat.bits` of the input length is computable in linear time.

**Construction sketch.** One left-to-right input scan driving an in-place
binary counter on a work tape (the `Turing.incFixed` carry discipline, cost
amortized constant per input cell), then emit the counter word. -/
theorem computesFunInTime_lengthBits :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length) fun n => c * (n + 1) := by
  obtain ⟨_, c, _, M, hM⟩ := Complexity.timeConstructible_id
  exact ⟨M, c, hM⟩

/-- **P5, polynomial evaluation, unary clause**
(harvest: the TMSAT batch's `polyUnaryTM`/`poly_unary_computes`, proved with
budget `(C + 5(e+1) + 4)·(n+1)^(e+1)`). The exact unary value of
`C·(n+1)^e` at the input length is computable within a constant multiple of
`(n+1)^(e+1)`. Its instances are also the exact-emission primitive the
reduction constructions consume (catalog entry P7, subsumed here).

**Construction sketch** (indexing corrected per round-1 finding 5: the
harvest source's `poly_unary_computes` with loop parameter `c` emits
exponent `c + 1`, so this contract harvests with parameter `e - 1`): for
`e > 0`, `e` nested unary loop tapes of side length `n + 1`, installed by
one input scan, the innermost loop emitting `C` trues per box point —
exactly `C·(n+1)^e` in total; for `e = 0` the output is the constant
`List.replicate C true`, a fixed emission chain. A recursive invariant
restores completed inner heads, with loop depth `r` costing at most
`(C + 1 + 5r)·(n+1)^r`. -/
theorem computesFunInTime_polyUnary (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        fun n => c * (n + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    simpa using computesFunInTime_const (List.replicate C true)
  | succ d =>
    refine ⟨catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, fun x => ?_⟩
    apply (catalogPoly_unary_computes d C x).mono
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos x.length) (by omega))

/-- **P5, polynomial evaluation, binary clause**
(harvest: the TMSAT batch's composition of the unary generator with the
binary length counter). The little-endian binary representation of
`C·(n+1)^e` at the input length is computable within a constant multiple
of `(n+1)^(e+1)`.

**Construction sketch.** The unary generator above composed with the
binary length counter of `computesFunInTime_lengthBits` through the public
buffered composition (`Turing.FinTM.computesFunInTime_comp`) — the harvest
source's exact route, under the same `e - 1` harvest-indexing convention
as the unary clause (round-1 finding 5). -/
theorem computesFunInTime_polyBits (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨U, a, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨B, b, hB⟩ := computesFunInTime_lengthBits
  obtain ⟨M, d, hM⟩ := computesFunInTime_comp hU hB
    (by intro m n h; exact Nat.mul_le_mul_left b (Nat.add_le_add_right h 1))
  refine ⟨M, d * (a + 1) * (b + 1), fun x => ?_⟩
  have hm := hM x
  simp only [Function.comp_apply, List.length_replicate] at hm
  apply hm.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hb : b + 1 ≤ (b + 1) * P := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (b + 1) hp
  have hbound : a * P + b * (a * P + 1) + 1 ≤ (a + 1) * (b + 1) * P := by
    calc
      _ = a * (b + 1) * P + (b + 1) := by ring
      _ ≤ a * (b + 1) * P + (b + 1) * P := Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ d * ((a + 1) * (b + 1) * P) := Nat.mul_le_mul_left d hbound
    _ = _ := by ring

/-- **P6, pairing with a fixed first component**
(harvest: the HALT batch's `fixedPair_computes`, proved with the exact
budget `2|α| + |x| + 3`; its promotion was formally requested). For a
fixed word `α`, the self-delimiting pairing `pairEncode α x` is computable
in linear time. This is the threading stage: downstream threaded contracts
receive `pairEncode a b` and act on `b` while carrying `a`.

**Construction sketch.** `pairEncode α x` is literally
`(α doubled) ++ [false, true] ++ x`, so this is the prepend primitive at
that fixed word; it is kept as its own contract because consumers cite the
pairing grammar, and the harvest source proves the exact budget
`2|α| + |x| + 3`. -/
theorem computesFunInTime_pairEncodeFixed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x) fun n => c * (n + 1) := by
  simpa only [pairEncode] using
    computesFunInTime_prepend ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6, first-component extraction** (new; the
aligned two-bit scan of the `Turing.pairDecode` grammar as a machine). On
a well-formed pair the doubled prefix is undoubled and emitted; on a
malformed input the output is `[]`.

**Construction sketch.** Output is append-only, so the scan must not emit
before the parse succeeds: undouble aligned `00`/`11` blocks onto a work
tape until the aligned `01` separator, then replay the buffer to the
output; any misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairFst :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true false, 5, fun x => ?_⟩
  have h := pairExtract_computes true false x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, second-component extraction** (new; the
same aligned scan, emitting the suffix after the separator instead). On a
malformed input the output is `[]`. Iterating this extractor is how the
nested-quadruple parsers of the TMSAT constructions decompose.

**Construction sketch.** Scan aligned blocks without emitting until the
separator is found (validity of the prefix must be known before any suffix
bit may be emitted), then copy the suffix verbatim; a misaligned block
halts silently. -/
theorem computesFunInTime_pairSnd :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM false true, 5, fun x => ?_⟩
  have h := pairExtract_computes false true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, grammar validity** (new). The single-bit
test for membership in the `Turing.pairDecode` grammar, the guard stage
every parser pipeline rejects malformed inputs with.

**Construction sketch.** One aligned two-bit scan in finite control; emit
the single verdict bit at the separator or at the first misaligned block.
No buffering is needed — only one bit is ever emitted, at the end. -/
theorem computesFunInTime_pairValid :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        fun n => c * (n + 1) := by
  exact ⟨pairValidTM, 1, fun x => by simpa using pairValid_computes x⟩

/-- **P13, pair to concatenation** (round-2 addition
per round-1 finding 3 — the D-WRAP obligation's exact shape). On
`pairEncode x u`, emit `x ++ u`; malformed inputs yield `[]`, the threaded
rejection the downstream guard reads (the reduction wrapper's own
`[false]` rejection is assembled at the decider stage).

**Construction sketch.** Undouble the aligned prefix onto a work tape —
nothing emitted while validity is unknown; at the aligned separator,
replay the buffered first component and then copy the suffix verbatim; a
misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairConcat :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true true, 5, fun x => ?_⟩
  have h := pairExtract_computes true true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P14, duplication into a pair** (round-2 addition
per round-1 finding 3 — the entry stage of data-retaining pipelines:
the reduction emitter retains `x` while its duplicate feeds the generated
components). Emit `pairEncode x x`.

**Construction sketch.** Two input passes: emit each read bit doubled,
then the separator, then copy the input verbatim. No buffering is needed
— the pairing prefix is valid bit by bit, and every input is legal. -/
theorem computesFunInTime_pairDup :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x) fun n => c * (n + 1) := by
  exact ⟨pairDupTM, 4, pairDup_computes⟩

/-- The threaded-map controller uses the last tape only for captured output;
all administrative actions preserve its contents and the source bank. -/
private def mapAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool)))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture the payload computation, rewind both relevant heads, and silently
validate the original pair. Only after validation, replay the native encoded
prefix followed by the captured payload. The source bank is never reused. -/
private def pairMapTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => mapAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => match work (Fin.last M.k) with
          | some _ => mapAction M 0 .neg none (some (.inr (.inl 1)))
          | none => mapAction M 0 .pos none (some (.inr (.inl 2)))
        | 2 => controlAction .neg (some (.inr (.inl 3)))
        | 3 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 3)))
          | none => controlAction .pos (some (.inr (.inr (false, none))))
        | 4 => controlAction .neg (some (.inr (.inl 5)))
        | 5 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 5)))
          | none => controlAction .pos (some (.inr (.inr (true, none))))
        | _ => match work (Fin.last M.k) with
          | some b => mapAction M 0 .pos (some b) (some (.inr (.inl 6)))
          | none => mapAction M 0 0 none none
      | .inr (.inr (emit, none)) => match inp with
        | none => mapAction M 0 0 none none
        | some b => mapAction M .pos 0 (if emit then some b else none)
            (some (.inr (.inr (emit, some b))))
      | .inr (.inr (emit, some b)) => match inp with
        | none => mapAction M 0 0 none none
        | some d => mapAction M .pos 0 (if emit then some d else none)
            (if b = d then some (.inr (.inr (emit, none)))
             else if b then none
             else some (.inr (.inl (if emit then 6 else 4)))) }

/-- An administrative configuration preserves the completed source bank and
captured word, while exposing the input and capture-head positions. -/
private def mapCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairMapTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (out : List Bool) : Cfg (M.k + 1) Bool (pairMapTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairMapTM M).State))
      (.inr (.inl 0)) [] out c with
    state := q
    inputPos := p
    workTapePos := fun j => if hj : j.val < M.k then c.workTapePos ⟨j, hj⟩ else h }

/-- Administrative steps change only the named heads, control, and optional
output. No work-tape cell is written. -/
private lemma mapAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairMapTM M).State)
    (p : Fin (x.length + 2)) (h : ℤ) (out : List Bool)
    (m d : SignType) (b : Option Bool) :
    (mapAction M m d b q').apply (mapCfg M c q p h out) =
      mapCfg M c q' (moveInputPos p m) (h + d.cast) (out ++ b.toList) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  by_cases hj : j.val < M.k <;> simp [mapAction, mapCfg, Action.apply, hj]

/-- Rewinding the captured word from its final cell costs its length plus one.
**Proof sketch.** At the left blank, move right to the input-rewind phase.
Otherwise a single silent left step reduces the remaining prefix length. -/
private lemma mapBuffer_rewind (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ c.output.length →
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) []) (j + 1) =
      mapCfg M c (some (.inr (.inl 2))) p 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols, Fin.val_last,
      Nat.lt_irrefl, ↓reduceDIte, Nat.cast_zero, zero_sub, List.nil_append, bufferTape_left]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i; by_cases hi : i.val < M.k <;> simp [mapAction, Action.apply, hi]
    · rfl
  | succ j ih =>
    intro hj
    have hs : (pairMapTM M).tm.step
        (mapCfg M c (some (.inr (.inl 1))) p (((j + 1 : ℕ) : ℤ) - 1) []) =
        mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      change ((pairMapTM M).tm.tr (.inr (.inl 1)) _ _).apply _ = _
      have hw : (mapCfg M c (some (.inr (.inl 1))) p j []).workTapeSymbols
          (Fin.last M.k) = some (c.output[j]'(by omega)) := by
        simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
          List.getElem?_eq_getElem (by omega : j < c.output.length)]
      simp only [pairMapTM, hw]
      rw [mapAction_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Capture and rewind reach the silent validator with physical output empty.
**Proof sketch.** The least source halt supplies the capture guard. Rewind the
captured word, then the input, preserving every completed source tape. -/
private lemma mapStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + w.length + x.length + 5, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
        mapCfg M c (some (.inr (.inr (false, none)))) 1 0 [] := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairMapTM M).State := Sum.inl
  let ret : (pairMapTM M).State := .inr (.inl 0)
  have hinit : (pairMapTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairMapTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  have hback : (pairMapTM M).tm.step (captureCfg emb ret [] [] c) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    by_cases hi : i.val < M.k <;>
      simp [pairMapTM, ret, mapAction, Action.apply, captureCfg, mapCfg, hi, sub_eq_add_neg]
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
    (.inr (.inl 2)) (.inr (.inl 3)) (some (.inr (.inr (false, none))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (mapCfg M c (some (.inr (.inl 2))) c.inputPos 0 []) rfl
  have hlen : c.output.length = w.length := congrArg List.length ho
  have hfirst : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) (t + 1) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcap, hback]
  refine ⟨t + 1 + (c.output.length + 1) + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (t + 1) (c.output.length + 1), hfirst,
      mapBuffer_rewind M c c.inputPos c.output.length (le_refl _), hr]
    rfl

/-- The parser and prefix-replay phases read the indexed native input cell. -/
private lemma mapCfg_read (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q : Option (pairMapTM M).State)
    (i : ℕ) (hi : i ≤ x.length) (h : ℤ) (out : List Bool) :
    (mapCfg M c q ⟨i + 1, by omega⟩ h out).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- One aligned-block read remembers its first bit. Only the replay phase
emits it; the validator remains silent. -/
private lemma mapParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b emit : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairMapTM M).tm.step
      (mapCfg M c (some (.inr (.inr (emit, none)))) ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) =
      mapCfg M c (some (.inr (.inr (emit, some b))))
        ⟨pre.length + 2, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b] else []) := by
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, none))) _ _).apply _ = _
  rw [mapCfg_read M c _ pre.length (by simp [hx])]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> rfl

/-- A two-bit block either continues parsing, rejects `10`, or selects the
post-separator phase. The captured payload and its origin head are preserved. -/
private lemma mapParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b d emit : Bool)
    (hx : x = pre ++ b :: d :: rest) :
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (emit, none))))
        ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) 2 =
      mapCfg M c
        (if b = d then some (.inr (.inr (emit, none))) else if b then none
          else some (.inr (.inl (if emit then 6 else 4))))
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b, d] else []) := by
  change (pairMapTM M).tm.step ((pairMapTM M).tm.step _) = _
  rw [mapParse_first M c pre (d :: rest) out b emit hx]
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, some b))) _ _).apply _ = _
  rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> simp [SignType.cast, List.append_assoc]

/-- The silent aligned validator either halts without output or reaches the
input-rewind seam. Its total cost is at most the unread length plus one.
**Proof sketch.** Induction over aligned two-bit blocks. Equal bits recurse,
`01` validates, and `10`, a missing separator, or an incomplete block rejects. -/
private lemma mapValidate (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest), ∃ t ≤ rest.length + 1,
      if (pairDecode rest).isSome then
        ∃ p, (pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t =
          mapCfg M c (some (.inr (.inl 4))) p 0 []
      else
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).state = none ∧
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).output = [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, none))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ pre.length (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | singleton b =>
    intro pre hx
    refine ⟨2, by simp, ?_⟩
    have hd : pairDecode [b] = none := by cases b <;> rfl
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [mapParse_first M c pre [] [] b false hx]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, some b))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | cons_cons b d rest ih _ =>
    intro pre hx
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hh⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, mapParse_block M c pre rest [] b b false hx]
      simp only [↓reduceIte, List.append_nil]
      have hp : (pairDecode (b :: b :: rest)).isSome = (pairDecode rest).isSome := by
        cases b <;> simp [pairDecode]
      rw [hp]
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        show pre.length + 2 + 1 = pre.length + 3 by omega] using hh
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_some, ↓reduceIte]
        refine ⟨⟨pre.length + 3, by simp [hx] <;> omega⟩, ?_⟩
        rw [mapParse_block M c pre rest [] false true false hx]
        rfl
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rw [mapParse_block M c pre rest [] true false false hx]
        exact ⟨rfl, rfl⟩
      · exact False.elim (h rfl)

/-- Once validation has succeeded, replay precisely the encoded prefix and
separator and enter the captured-payload replay with its head still at zero.
**Proof sketch.** Induct on the decoded first component. Each doubled bit
costs two emitting steps; the final `01` costs two and switches replay tapes. -/
private lemma mapPrefix_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a b : List Bool) :
    ∀ pre out (hx : x = pre ++ pairEncode a b), ∃ p,
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (true, none))))
        ⟨pre.length + 1, by simp [hx, pairEncode]; omega⟩ 0 out) (2 * a.length + 2) =
      mapCfg M c (some (.inr (.inl 6))) p 0 (out ++ pairEncode a []) := by
  induction a with
  | nil =>
    intro pre out hx
    have hx' : x = pre ++ false :: true :: b := by simpa [pairEncode] using hx
    refine ⟨⟨pre.length + 3, by simp [hx'] <;> omega⟩, ?_⟩
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      mapParse_block M c pre b out false true true hx'
  | cons bit a ih =>
    intro pre out hx
    have hx' : x = pre ++ bit :: bit :: pairEncode a b := by
      simpa [pairEncode, List.append_assoc] using hx
    obtain ⟨p, hp⟩ := ih (pre ++ [bit, bit]) (out ++ [bit, bit])
      (by simpa [List.append_assoc] using hx')
    refine ⟨p, ?_⟩
    rw [show 2 * (bit :: a).length + 2 = 2 + (2 * a.length + 2) by simp; omega,
      MultiTapeTM.runFrom_add, mapParse_block M c pre (pairEncode a b) out bit bit true hx']
    simp only [↓reduceIte]
    simpa [pairEncode, List.append_assoc] using hp

/-- Captured-payload replay preserves the bank and emits each stored cell once.
**Proof sketch.** Induct over emitted cells, using `take_succ` and the contiguous
buffer read equation. The terminal blank supplies the final silent halt. -/
private lemma mapPayload_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ∀ j (_hj : j ≤ c.output.length),
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) j =
      mapCfg M c (some (.inr (.inl 6))) p j (out ++ c.output.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [mapCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change ((pairMapTM M).tm.tr (.inr (.inl 6)) _ _).apply _ = _
    have hw : (mapCfg M c (some (.inr (.inl 6))) p j
        (out ++ c.output.take j)).workTapeSymbols (Fin.last M.k) =
          some (c.output[j]'(by omega)) := by
      simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [pairMapTM, hw]
    rw [mapAction_apply]
    rw [moveInputPos_zero, List.take_succ,
      List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [SignType.cast, Nat.cast_add, Nat.cast_one, Option.toList_some,
      List.append_assoc]

/-- The last blank-reading step halts after the entire capture has been emitted. -/
private lemma mapPayload_finish (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).state = none ∧
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).output = out ++ c.output := by
  rw [MultiTapeTM.runFrom_succ_eq_step', mapPayload_replay M c p out _ (le_refl _)]
  simp [MultiTapeTM.step, pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols,
    mapAction, Action.apply]

/-- The complete controller retains the first component and appends the
source's captured result, rejecting malformed inputs without any emission.
**Proof sketch.** Concatenate capture/rewind, silent validation, input rewind,
encoded-prefix replay, and captured-payload replay. Source output length is
at most its running time. The two replay lengths and all input scans therefore
fit `4 (T(n) + n + 3)`; no running time is evaluated at a padded input length. -/
private lemma pairMap_computes {M : FinTM Bool} {f : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime f T) :
    (pairMapTM M).ComputesFunInTime
      (fun x => match pairDecode x with
        | some (a, _) => pairEncode a (f x)
        | none => []) (fun n => 4 * (T n + n + 3)) := by
  intro x
  have hlen : (f x).length ≤ T x.length := by
    have hout := ((computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [hout] using M.tm.output_length_le x (T x.length)
  obtain ⟨t, ht, c, ho, hstart⟩ := mapStart M x (f x) (T x.length) (hM x)
  obtain ⟨u, hu, hval⟩ := mapValidate M c x [] (by simp)
  simp only [List.length_nil, Nat.zero_add] at hval
  have hpos : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by
    apply Fin.ext
    simp
  rw [hpos] at hval
  have hclen : c.output.length = (f x).length := congrArg List.length ho
  cases hd : pairDecode x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hval ⊢
    have hc : (pairMapTM M).ComputesInTime x [] (t + u) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hstart]
      exact hval
    exact hc.mono (by omega)
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [hd, Option.isSome_some, ↓reduceIte] at hval ⊢
    obtain ⟨p, hp⟩ := hval
    obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
      (.inr (.inl 4)) (.inr (.inl 5)) (some (.inr (.inr (true, none))))
      (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
      (mapCfg M c (some (.inr (.inl 4))) p 0 []) rfl
    have hr' : (pairMapTM M).tm.runFrom
        (mapCfg M c (some (.inr (.inl 4))) p 0 []) r =
        mapCfg M c (some (.inr (.inr (true, none)))) 1 0 [] := hr
    obtain ⟨p', hp'⟩ := mapPrefix_replay M c a b [] []
      (by simpa using Turing.eq_pairEncode_of_pairDecode x a b hd)
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at hp'
    rw [hpos] at hp'
    have hprefix : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x)
        ((t + u + r) + (2 * a.length + 2)) =
        mapCfg M c (some (.inr (.inl 6))) p' 0 (pairEncode a []) := by
      rw [MultiTapeTM.runFrom_add _ _ (2 * a.length + 2),
        MultiTapeTM.runFrom_add _ _ r, MultiTapeTM.runFrom_add _ t u,
        hstart, hp, hr', hp']
    have hc : (pairMapTM M).ComputesInTime x (pairEncode a (f x))
        (((t + u + r) + (2 * a.length + 2)) + (c.output.length + 1)) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add _ _ (c.output.length + 1), hprefix]
      obtain ⟨hs, hout⟩ := mapPayload_finish M c p' (pairEncode a [])
      refine ⟨hs, ?_⟩
      simpa [ho, pairEncode, List.append_assoc] using hout
    apply hc.mono
    have hpbound := p.isLt
    change r ≤ p.val + 2 at hrle
    have hxlen : x.length = 2 * a.length + 2 + b.length := by
      rw [Turing.eq_pairEncode_of_pairDecode x a b hd, Turing.length_pairEncode]
    omega

/-- **C1, the threaded map combinator** (round-2
addition per round-1 finding 3 — the data-retaining assembly the
extractors deliberately do not provide: sequential composition yields
`g (f z)` only, never simultaneous access to a retained component). Given
a machine for `g`, transform a pair's payload while carrying its head
component unchanged; malformed inputs yield `[]`. Monotonicity of `Tg`
converts the payload-length bound `|b| ≤ |z|` into a time bound, exactly
as in `Turing.FinTM.computesFunInTime_comp`.

**Construction sketch.** Parse `pairEncode a b` onto two work tapes,
silent until the separator validates; run the `g`-machine on `b`
relocated-and-captured (the W1 discipline — its output lands on the
capture tape, with length bounded by its running time via
`Turing.MultiTapeTM.output_length_le`); then emit the re-encoded pair:
doubled `a`, separator, captured `g b`. -/
theorem computesFunInTime_pairMapSnd {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        fun n => c * (n + 1 + Tg n) := by
  have hM := pairMap_computes (catalogPayload_computes hg hTg)
  refine ⟨pairMapTM (bufferedCompTM (pairExtractTM false true) Mg), 40, fun x => ?_⟩
  have hc := hM x
  have heq : (match pairDecode x with
      | some (a, _) => pairEncode a (g ((pairDecode x).map Prod.snd |>.getD []))
      | none => []) = (match pairDecode x with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
    cases hd : pairDecode x with
    | none => rfl
    | some ab => cases ab; simp
  dsimp only at hc
  rw [heq] at hc
  exact hc.mono (by dsimp only; omega)

/-- **P8, threaded length-bound check** (new; the
original-bound re-check discipline of the Exercise-2.1 reverse verifier,
in threaded form). On `pairEncode a b`, decide `|b| ≤ C·(|a|+1)^e` — the
original input `a` travels with the payload precisely so that this bound
is checked against *it*, the audited rule being that merely fitting inside
the enlarged region does not authorize a witness. Malformed inputs answer
`false`.

**Construction sketch.** Parse the two components onto work tapes (the
extractor scans above); lay down `C·(|a|+1)^e` in unary by the
polynomial-evaluation loop; compare against `|b|` by a parallel countdown;
emit the single verdict bit. -/
theorem computesFunInTime_pairLenCheck (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_pairFst
  obtain ⟨U, b, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨G, d, hG⟩ := computesFunInTime_comp hF hU
    (by
      intro m n h
      exact Nat.mul_le_mul_left b
        (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) (e + 1)))
  refine ⟨pairCountTM G, d * (a + b * (a + 1) ^ (e + 1) + 1) + 7, fun x => ?_⟩
  have hc := pairCount_computes hG x
  have hh : (pairCountTM G).ComputesInTime x
      [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false]
      (d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        2 * x.length + 5) := by
    cases hd : pairDecode x with
    | none => simpa [hd, Function.comp_apply] using hc
    | some uv => cases uv; simpa [hd, Function.comp_apply] using hc
  apply hh.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : x.length + 1 ≤ P := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ e + 1 by omega)
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hpow : (a * (x.length + 1) + 1) ^ (e + 1) ≤ (a + 1) ^ (e + 1) * P := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hbase (e + 1)
  have hsum : a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1 ≤
      (a + b * (a + 1) ^ (e + 1) + 1) * P := by
    calc
      _ ≤ a * P + b * ((a + 1) ^ (e + 1) * P) + P :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hn)
          (Nat.mul_le_mul_left b hpow)) hp
      _ = _ := by ring
  calc
    _ = d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        (2 * x.length + 5) := by omega
    _ ≤ d * ((a + b * (a + 1) ^ (e + 1) + 1) * P) + 7 * P :=
      Nat.add_le_add (Nat.mul_le_mul_left d hsum) (by omega)
    _ = (d * (a + b * (a + 1) ^ (e + 1) + 1) + 7) * P := by ring

/-- **P9, marker strip** (harvest: the semantic layer
is the Exercise-2.1 batch's proved `stripCertificate` family; the machine
is new). On `pairEncode a v`, strip `v` at its **last** `true`
(`Turing.splitAtLastTrue`) and re-emit the threaded pair with the stripped
witness; an all-`false` region or a malformed input yields `[]` (the
rejection the downstream guard reads).

**Construction sketch.** Parse `a` and `v` onto work tapes; locate the
last `true` of `v` by one reverse sweep; then — and only then — emit the
re-encoded pair (doubled `a`, separator, the prefix of `v` before that
marker). All-`false` regions and parse failures halt with nothing
emitted. -/
theorem computesFunInTime_stripLast :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨S, a, hS⟩ := computesFunInTime_pairSnd
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE⟩ := computesFunInTime_const ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' rawStrip_computes hE
  refine ⟨M, d * (2 * b * (a + 1) + (4 + c) + 1), fun x => ?_⟩
  have hh : M.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (d * (b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) (c * (x.length + 1)) + 1)) := by
    have hm := hM x
    cases hd : pairDecode x with
    | none => simpa [hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
          exact hp _
        simpa [hd, ha, hs, hx] using hm
  apply hh.mono
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hg : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) ≤
      (2 * b * (a + 1)) * (x.length + 1) := by
    calc
      _ = (2 * b) * (a * (x.length + 1) + 1) := by ring
      _ ≤ (2 * b) * ((a + 1) * (x.length + 1)) := Nat.mul_le_mul_left _ hbase
      _ = _ := by ring
  have hm : max (4 * (x.length + 1)) (c * (x.length + 1)) ≤
      (4 + c) * (x.length + 1) := by
    apply max_le
    · exact Nat.mul_le_mul_right _ (by omega)
    · exact Nat.mul_le_mul_right _ (by omega)
  have hb : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
      max (4 * (x.length + 1)) (c * (x.length + 1)) + 1 ≤
      (2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) := by
    calc
      _ ≤ (2 * b * (a + 1)) * (x.length + 1) +
          (4 + c) * (x.length + 1) + (x.length + 1) :=
        Nat.add_le_add (Nat.add_le_add hg hm) (by omega)
      _ = _ := by ring
  have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ 2 by omega)
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) ^ 2) :=
      Nat.mul_le_mul_left d (Nat.mul_le_mul_left _ hn)
    _ = _ := by ring

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (splitStep w s).length ≤ w.length + 1 := by
  unfold splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => splitAccept C e w ((splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => splitAccept C e w ((splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((splitStep w)^[i] []).length)
          (w.drop ((splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma splitLoop_bound (c A e n : ℕ) :
    c * (A * (n + 1) ^ (e + 1) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) ^ (e + 2) := by
  have hp : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (e + 1) + 1 ≤ (A + 1) * (n + 1) ^ (e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (n + 1) ^ (e + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ]; ring

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (splitPos w j) .pos = splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [splitPos] <;> omega)]
    apply Fin.ext
    simp only [splitPos, Fin.val_mk]
    omega
  · have he : splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma splitScratch_erase (q j : ℕ) :
    Function.update (splitScratch q j) (j : ℤ) none = splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def splitRestoreTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 5 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some none, .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (if q.2 then (none, .neg) else (some (some true), .neg))
            (fun _ => (some none, .neg)), none, some (1, false)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, false)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, false)⟩
      | 2 => controlAction .neg (some (3, false))
      | 3 => match inp with
        | some _ => controlAction .neg (some (3, false))
        | none => controlAction .pos (some (4, false))
      | _ => controlAction 0 (some (4, false)) }

/-- The clearing scan has consumed `j` candidate cells and erased exactly that
prefix on each scratch tape; the physical input tracks the same count. -/
private def splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j =
      splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := splitPos_read w (splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitRestoreTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma splitRestore_append (k : ℕ) (w s : List Bool) :
    (splitRestoreTM k).tm.step (splitRestoreScan k w s s.length) =
      splitRestoreClean k w (splitStep w s) (1, false)
        (splitPos w s.length) (s.length - 1) := by
  have hw : (splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, splitRestoreClean, splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, splitRestoreScan, splitRestoreClean, splitStep, hs]
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (splitRestoreTM k).tm.runFrom
        (splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (splitRestoreTM k).tm.step
        (splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Complete rejection cleanup restores exactly the audited state-word seam.
It works for arbitrary candidate bits, and its one-past-end stall is silent.
**Proof sketch.** Scan and erase `|s|` cells, handle the final scratch cell,
rewind synchronized heads along the preserved candidate, then rewind input.
The cost is at most `2|s|+|w|+5`, and every transition is silent. -/
private lemma splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  have hlen : s.length ≤ (splitStep w s).length := by
    unfold splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := catalogRewind (splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (splitRestoreClean k w (splitStep w s) (2, false) (splitPos w s.length) 0) rfl
  have hp : (splitPos w s.length).val ≤ w.length + 1 := by simp [splitPos] <;> omega
  have hfirst : (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) (s.length + 1) =
      splitRestoreClean k w (splitStep w s) (1, false) (splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitRestore_scan k w s _ (le_refl _),
      splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, splitRestore_rewind k w (splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (splitCountCfg emb ret w s c).inputSymbol a).apply (splitCountCfg emb ret w s c) =
      splitCountCfg emb ret w s (a.apply c) := by
  have hflag := splitCount_over w (splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [splitCountAction, splitCountCfg, Action.apply, ho]
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (splitCountCfg emb ret w s c) t =
      splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (splitCountCfg emb ret w s d) = splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [splitCountCfg, hq]
      have hsource : d.inputSymbol = none := by
        unfold Cfg.inputSymbol
        split_ifs with h₀ h₁
        · rfl
        · rfl
        · have hp := d.inputPos.isLt
          simp only [Fin.ext_iff, Fin.val_zero] at h₀
          simp only [List.length_nil] at hp
          simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff, Fin.val_one] at h₁
          omega
      have hwork : (fun i => (splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact splitCount_apply emb ret w s d _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The in-file generator's loop phase ends with every unary scratch head
back at zero, ready for the restoration controller. The source input is empty;
its loop side length is supplied by the initialized work tapes.
**Proof sketch.** Run the existing exact nested-loop invariant over the full
box and then take the final halting transition. No fresh generator proof is
assumed, and the zero coefficient is included. -/
private lemma splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1) + 1) =
      {catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1)) =
      catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, catalogPolyCfg, catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]
  · simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The cleanup's return seam is absorbing, so its exact restoration can be
exported with positive duration and no earlier return-state visit. -/
private lemma splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := catalogFirstEntry (splitRestoreTM k).tm (4, false)
    (splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [splitPos_read w (splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def splitPrepareTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some (some true), .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (none, .neg) (fun _ => (some (some true), .neg)),
            none, some (1, q.2)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- During preparation, every scratch tape contains the length scanned so far. -/
private def splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) j =
      splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitPrepareTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (splitCount_over w (splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.step (splitPrepareScan k w s s.length) =
      splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, splitPrepareScan, splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (splitPrepareTM k).tm.step (splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma splitPrepare_run (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [splitPrepareScan, Cfg.ofWords, splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [catalogPolyTape]
  have hfirst : (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) (s.length + 1) =
      splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitPrepare_scan k w s _ (le_refl _), splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, splitPrepare_rewind k w s s.length (le_refl _)]

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : splitSafe tm anchor c u) (hv : splitSafe tm anchor (tm.runFrom c u) v) :
    splitSafe tm anchor c (u + v) := by
  intro j hj
  by_cases h : j ≤ u
  · exact hu j h
  · have he : j = u + (j - u) := by omega
    rw [he, MultiTapeTM.runFrom_add]
    exact hv (j - u) (by omega)

/-- Cut an absorbing source phase at its first terminal control state and
embed the entire prefix into a disjoint host phase.
**Proof sketch.** Take the least terminal visit. Absorption identifies its
configuration with the known endpoint. Induct on the prefix length using
transition agreement only before that visit; every mapped control state,
including a halted state, is different from the host anchor. -/
private lemma splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q

/-- A standalone native-input rewind, with an absorbing return at state two. -/
private def splitRewindTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ => match q.val with
      | 0 => controlAction .neg (some 1)
      | 1 => match inp with
        | some _ => controlAction .neg (some 1)
        | none => controlAction .pos (some 2)
      | _ => controlAction 0 (some 2) }

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def splitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- Each subroutine has its own finite control phase; only cleanup can
return to the anchor. The acceptance bit survives the native-input rewind. -/
private inductive SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- Preparation reaches its first return with the exact counted-source bank.
Every configuration of the embedded preparation is outside the anchor phase.
**Proof sketch.** Cut the absorbing source at its first return, map its full
configuration into the preparation phase, then take the explicit dispatch.
Check the source-bank seam field by field, including the native head and flag. -/
private lemma splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          splitCountCfg SplitBodyState.count SplitBodyState.check w s
            (splitBank M s (some start) []) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := splitEmbed_cut (splitPrepareTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (splitPrepare_run M.k w s)
  have hstep : (splitBodyTM M start).tm.step
      ((splitPrepareReady M.k w s 2 0).mapState SplitBodyState.prepare) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, splitPrepareReady, Option.map_some,
      splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, splitCountCfg, splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [splitCountCfg, splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t ≤ T, (splitBodyTM M start).tm.runFrom
      (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t := by
  classical
  let c := splitBank M s (some start) []
  let d := splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := splitCount_run M.tm (splitBodyTM M start).tm
    SplitBodyState.count SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (splitBodyTM M start).tm.runFrom (c.mapState (SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (SplitBodyState.rewind ok) ∧
      splitSafe (splitBodyTM M start).tm .anchor (c.mapState (SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := catalogRewind (splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRewindTM M.k).tm
    (splitBodyTM M start).tm (SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitBodyTM M start).tm.runFrom
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s)) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRestoreTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, splitPos w j, Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (splitEmitTM k).tm.step
        (splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hread]
    refine Cfg.ext rfl (splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 0) s.length s.length out) =
      splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg]
  · simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := splitPos_read pre (splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [splitEmitTM, controlAction, splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 3) pre.length h out) =
        splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using splitPos_succ w pre.length
      · funext i; simp [splitEmitTM, Action.apply, splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    splitEmit_double k w s hs _ (le_refl _), splitEmit_separator]
  have h := splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (splitStep w s)) := by
  let tm := (splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := splitCount_accept SplitBodyState.count SplitBodyState.check w s
      (splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := splitSafe_one tm .anchor d _ hcheck
    (by simp [d, splitCountCfg, splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, splitEmitCfg, splitPos]
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, splitEmitCfg])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have transport (j : ℕ) : tm.runFrom (ec.mapState SplitBodyState.emit) j =
        ((splitEmitTM M.k).tm.runFrom ec j).mapState SplitBodyState.emit :=
      MultiTapeTM.runFrom_mapState_of_agreeOn (splitEmitTM M.k).tm tm
        ⟨SplitBodyState.emit, by intro a b h; exact SplitBodyState.emit.inj h⟩
        (fun _ => True) (fun _ _ _ _ => rfl) ec j (by intros; trivial)
    have hemit : tm.runFrom (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState SplitBodyState.emit := by
      rw [transport]
      exact congrArg (Cfg.mapState SplitBodyState.emit) (splitEmit_run M.k w s hs)
    have hemits : splitSafe tm .anchor (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [transport]
      cases hq : ((splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState SplitBodyState.emit := by
      rw [MultiTapeTM.runFrom_add, hdepart]; exact h5
    refine ⟨1 + u, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_true, ↓reduceIte]
      change (tm.runFrom z (1 + u)).state = none ∧ _
      rw [hend]
      exact ⟨rfl, rfl⟩
  · let rc := (splitRestoreScan M.k w s 0).mapState (SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, splitRestoreScan, Cfg.mapState]
      · simp [rc, splitRestoreScan, Cfg.mapState, splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, splitRestoreScan, Cfg.mapState, splitScratch, catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, splitRestoreScan])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (splitStep w s)) := by
      change (controlAction 0 (some (SplitBodyState.anchor (S := M.State)))).apply _ = _
      rw [controlAction_apply, moveInputPos_zero]
      rfl
    refine ⟨1 + u + 1, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + u + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hdepart, h5, hreturn]

/-- Given the concrete startup and round contracts, the audited loop supplies
the frozen split-search result and exponent. No body contract is assumed as an
axiom: both are explicit arguments, including the positive silent stall.
**Proof sketch.** Enlarge the body coefficient to cover the existing binary
length machine, instantiate the proved loop, identify its unary orbit and
finite search, then apply the checked exponent calculation. -/
private lemma splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (e + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t =
        Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (e + 1) ≤ (A + a) * (n + 1) ^ (e + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (e + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (splitLoop_bound c (A + a) e w.length) using 1
  exact (splitLoop_result C e w).symm

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma splitSource_poly (c C : ℕ) (s : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (splitBank (catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      splitBank (catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [splitBank, catalogPolyCfg] using splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma splitSource_constant (C : ℕ) (s : List Bool) :
    (catalogPrefixTM (List.replicate C true)).tm.runFrom
      (splitBank (catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      splitBank (catalogPrefixTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : splitBank (catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (catalogPrefixTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, catalogPrefixTM, catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
    (hT : T ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    T + 5 * l + 3 * n + 20 ≤
      ((C + 1 + 5 * e) * 2 ^ e + 40) * (n + 1) ^ (e + 1) := by
  have hp : (l + 1) ^ e ≤ 2 ^ e * (n + 1) ^ (e + 1) := by
    calc
      (l + 1) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
      _ = 2 ^ e * (n + 1) ^ e := Nat.mul_pow _ _ _
      _ ≤ 2 ^ e * (n + 1) ^ (e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmul := Nat.mul_le_mul_left (C + 1 + 5 * e) hp
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hlin : 5 * l + 3 * n + 21 ≤ 40 * (n + 1) ^ (e + 1) := by omega
  calc
    T + 5 * l + 3 * n + 20 ≤
        (C + 1 + 5 * e) * (2 ^ e * (n + 1) ^ (e + 1)) +
          40 * (n + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Instantiate the completed controller with an exact unary-output source.
The source assumption is discharged below separately for zero and positive
exponents; startup and the full body round have already been constructed.
**Proof sketch.** Supply the exact zero-time startup and constructed round to
the existing loop closure. The common envelope bounds the actual phase times,
and the source's unary-output length identifies the checked acceptance test. -/
private lemma splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (splitBank M s (some start) []) (B s.length) =
      splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  apply splitSolve_of_body C e (splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  cases e with
  | zero =>
    apply splitSolve_source C 0 (catalogPrefixTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply splitSolve_source C (e + 1) (catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- **P10, padding split search** (new; the bounded
search both padding constructions perform, realizable as a
`Turing.FinTM.exists_loopFindTM` instance over the polynomial-evaluation
primitive — the decision loop returns only a Boolean and cannot carry the
split). Search for the unique `i ≤ |w|` with `i + C·(i+1)^e = |w|`
(`Turing.solveSplit`); on success emit the threaded split
`pairEncode (w.take i) (w.drop i)`, and on failure `[]` — rejection when
no length-equation solution exists is the audited obligation.

**Construction sketch** (round 2: an `exists_loopFindTM` instance — the
decision loop exposes only a Boolean and cannot carry the payload,
round-1 finding 3; the narrowing from the catalog's supplied-predicate
search to this fixed length-equation search is recorded in
`machine-library-design.md` §9b). Instance data: round state
`s = List.replicate i true`, the candidate in unary;
`Inv w s := s.length ≤ w.length + 1`;
`stepF w s := if s.length ≤ w.length then s ++ [true] else s` (stall past
the end keeps the invariant step-closed); `acceptF w s` holds iff
`s.length + C·(s.length + 1)^e = w.length`, evaluated by the polynomial
loop and a countdown compare;
`out w s := pairEncode (w.take s.length) (w.drop s.length)` — always
nonempty, so success is distinguishable from the `[]` exhaustion; fuel
`R n := n`, so the orbit is exactly the candidates `0, …, n` and
`List.range.find?` returns the least solution, which strict monotonicity
of `i ↦ i + C·(i+1)^e` makes unique — `Turing.solveSplit`'s own
semantics. -/
theorem computesFunInTime_splitSolve (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  exact splitSolve_closed C e

/-- **P11, fixed-width increment** (harvest: the
enumerator batch's `enumCarryTM`/`enumCarry_correct`, proved with cost at
most twice the width plus two). The little-endian fixed-width successor
(`Turing.incFixed`), with `[]` on overflow, is computable in linear time.
The in-place form of the same carry loop is the loop combinator's fuel
counter.

**Construction sketch.** Two passes: the first scan detects overflow (all
trues) — nothing may be emitted while that is unknown; on a live word the
second pass emits falses over the carry prefix, a true at the first false,
and the remainder verbatim. The harvest source's in-place variant costs at
most twice the width plus two. -/
theorem computesFunInTime_incFixed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1) := by
  exact ⟨incFixedTM, 3, incFixed_computes⟩

/-! Emitter implementation. The append-bit and unary-token contracts are
proved below with coefficients one and three. The width-parametric split
contract is proved by the native `emitterP2*` controller.

The `emitterSplit*` layer generalizes the in-file loop closure without any
monotonicity assumption on the width function. The `emitterCompare*` family
is reimplemented in this file from the A-continuation's `e3c*` templates in
`ClassNP/Nondeterminism.lean` at base d7b5b6f94d28df8095165dd4dfe82fd09ba0d414.
Those originals are unchanged and are not cited as imported privates. The
native accepting emitter is `splitEmitTM`/`splitEmit_run`. The controller below
discharges `emitterSplit_of_body`'s literal configuration and strict-interior
anchor contracts. -/

/-- Width-parametric acceptance tests the exact length equation. It makes
no monotonicity assumption on the width function. -/
private def emitterSplitAccept (f : ℕ → ℕ) (w s : List Bool) : Bool :=
  decide (s.length + f s.length = w.length)

/-- The existing unary-candidate orbit tests the very same predicate, in the
same order, as the width-parametric specification. -/
private lemma emitterSplit_find (f : ℕ → ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => emitterSplitAccept f w ((splitStep w)^[i] [])) =
        solveSplitWith f w.length := by
  apply catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [emitterSplitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- The first accepting orbit index emits the original input's split; no
accepting index yields exactly the empty word. -/
private lemma emitterSplit_result (f : ℕ → ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => emitterSplitAccept f w ((splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((splitStep w)^[i] []).length)
          (w.drop ((splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplitWith f w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [emitterSplit_find]
  cases hs : solveSplitWith f w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [splitStep_orbit w i (by omega), List.length_replicate]

/-- A linear body envelope remains linear in the evaluator deadline after
multiplication by the number of candidates, including zero-length inputs. -/
private lemma emitterSplit_loop_bound (c A n t : ℕ) :
    c * (A * (t + n + 2) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) * (t + n + 2) := by
  have hfirst : A * (t + n + 2) + 1 ≤ (A + 1) * (t + n + 2) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (t + n + 2)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by ring

/-- A concrete clean body with the indicated linear evaluator envelope closes
the width-parametric split theorem through the proved result-bearing loop.
**Proof sketch.** Enlarge the common body coefficient to cover binary fuel
generation. The existing unary orbit gives every candidate from zero through
the input length in order. The loop's first success has the specified native
payload, while exhaustion emits nothing. The displayed arithmetic absorbs
startup and the extra final candidate factor without changing the argument
at which the evaluator budget is assessed. -/
private lemma emitterSplit_of_body (f TE : ℕ → ℕ) (body : FinTM Bool)
    (anchor : body.State) (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (TE (w.length + 1) + w.length + 2),
      (∀ j < t, (body.tm.runFrom (body.tm.initCfg w) j).state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t = Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (TE (w.length + 1) + w.length + 2) ∧
        (∀ j, 0 < j → j < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) j).state
            ≠ some anchor) ∧
        if emitterSplitAccept f w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplitWith f w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) * (TE (n + 1) + n + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
  have hbody (n : ℕ) : A * (TE (n + 1) + n + 2) ≤
      (A + a) * (TE (n + 1) + n + 2) := Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (TE (n + 1) + n + 2)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (by omega : w.length + 1 ≤
      TE (w.length + 1) + w.length + 2)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (emitterSplitAccept f)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (TE (n + 1) + n + 2)) hF'
    (by intro w; simp) splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, hp, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, hp, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (emitterSplit_loop_bound c (A + a) w.length (TE (w.length + 1))) using 1
  exact (emitterSplit_result f w).symm

/-- Equality of one-longer prefixes checks the entire old prefix and the next
optional bit. In particular, a missing bit differs from a present false bit. -/
private lemma emitter_take_succ_eq (u v : List Bool) (j : ℕ) :
    u.take (j + 1) = v.take (j + 1) ↔
      u.take j = v.take j ∧ u[j]? = v[j]? := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (List.take j) h
      simpa only [List.take_take, Nat.min_eq_left (by omega : j ≤ j + 1)] using hh
    · have hh := congrArg (fun xs : List Bool => xs[j]?) h
      simpa only [List.getElem?_take, Nat.lt_succ_self, ↓reduceIte] using hh
  · rintro ⟨hpre, hbit⟩
    rw [List.take_succ, List.take_succ, hpre, hbit]

/-- Two read-only word tapes are compared through their common right blank,
then both heads are restored to zero. The returned Boolean is stored in finite
control; the phase never emits. Empty words use the same positive-time path. -/
private def emitterCompareTM : FinTM Bool where
  k := 2
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, true)
    tr := fun q _ work => match q.1.val with
      | 0 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        else
          ⟨0, fun _ => (none, .pos), none,
            some (0, q.2 && decide (work 0 = work 1))⟩
      | 1 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
        else ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- Both comparison heads are aligned; the physical input and its head are
untouched, both word tapes are preserved, and the physical output is empty. -/
private def emitterCompareCfg (w u v : List Bool) (p : Fin (w.length + 2))
    (q : Fin 3) (b : Bool) (h : ℤ) : Cfg 2 Bool emitterCompareTM.State w :=
  ⟨some (q, b), p, (fun i => if i.val = 0 then bufferTape u else bufferTape v), fun _ => h, []⟩

/-- The comparator cannot mistake an interior aligned position for the common
right blank: at least one of the two complete words still has a bit there. -/
private lemma emitter_compare_nonblank (u v : List Bool) (j : ℕ)
    (hj : j < max u.length v.length) : ¬(u[j]? = none ∧ v[j]? = none) := by
  intro h
  have hu := List.getElem?_eq_none_iff.mp h.1
  have hv := List.getElem?_eq_none_iff.mp h.2
  have : max u.length v.length ≤ j := max_le hu hv
  omega

/-- After `j` forward comparisons the register records equality of the whole
length-`j` prefixes, including any unequal-length mismatch.
**Proof sketch.** Induct on the consumed prefix length. Reading both optional bits extends
prefix equality by one and advances both heads together. -/
private lemma emitter_compare_scan (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ max u.length v.length →
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) j =
        emitterCompareCfg w u v p 0 (decide (u.take j = v.take j)) j := by
  intro j
  induction j with
  | zero => intro _; simp [emitterCompareCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread : ¬(u[j]? = none ∧ v[j]? = none) :=
      emitter_compare_nonblank u v j (by omega)
    have heq : (decide (u.take j = v.take j) && decide (u[j]? = v[j]?)) =
        decide (u.take (j + 1) = v.take (j + 1)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact (emitter_take_succ_eq u v j).symm
    simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      if_neg hread]
    refine Cfg.ext ?_ (moveInputPos_zero _) rfl ?_ rfl
    · exact congrArg (fun b => some (0, b)) heq
    · funext i; simp [Action.apply]

/-- The common rewind passes all remaining aligned word cells and their left
blank, preserving the comparison register and restoring both heads exactly.
**Proof sketch.** Induct on the aligned distance to the left blank. At least one word
still occupies each interior position; the final positive move restores zero. -/
private lemma emitter_compare_rewind (w u v : List Bool) (p : Fin (w.length + 2))
    (b : Bool) : ∀ j, j ≤ max u.length v.length →
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 1 b ((j : ℤ) - 1)) (j + 1) =
        emitterCompareCfg w u v p 2 b 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step,
      emitterCompareCfg, emitterCompareTM, Cfg.workTapeSymbols,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_left, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hread := emitter_compare_nonblank u v j (by omega : j < max u.length v.length)
    have hs : emitterCompareTM.tm.step
        (emitterCompareCfg w u v p 1 b (((j + 1 : ℕ) : ℤ) - 1)) =
          emitterCompareCfg w u v p 1 b ((j : ℤ) - 1) := by
      have hpos : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
      rw [hpos]
      simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
        Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
        if_neg hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Whole-word comparison returns silently in exactly twice the longer word's
length plus two steps, with both tapes and the physical input head unchanged.
**Proof sketch.** The forward invariant compares full prefixes, so at the
longer length its register is literal word equality. The common-right-blank
transition enters the rewind; the rewind restores both heads at the origin. -/
private lemma emitter_compare_run (w u v : List Bool) (p : Fin (w.length + 2)) :
    emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0)
      (2 * (max u.length v.length + 1)) =
        emitterCompareCfg w u v p 2 (decide (u = v)) 0 := by
  let l := max u.length v.length
  have hu : u.length ≤ l := le_max_left _ _
  have hv : v.length ≤ l := le_max_right _ _
  have hscan := emitter_compare_scan w u v p l (le_refl _)
  rw [List.take_of_length_le hu, List.take_of_length_le hv] at hscan
  have hturn : emitterCompareTM.tm.step (emitterCompareCfg w u v p 0 (decide (u = v)) l) =
      emitterCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      List.getElem?_eq_none hu, List.getElem?_eq_none hv, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, sub_eq_add_neg]
  have hfirst : emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) (l + 1) =
      emitterCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
  rw [show 2 * (max u.length v.length + 1) = (l + 1) + (l + 1) by dsimp [l]; omega,
    MultiTapeTM.runFrom_add, hfirst]
  exact emitter_compare_rewind w u v p (decide (u = v)) l (le_refl _)

/-- A phase with an absorbing return state can be cut at its actual first
return while retaining its complete configuration endpoint.
**Proof sketch.** Choose the least return-state visit. Absorption identifies
its configuration with the known bounded endpoint. The bound proves existence
and bounds the first visit; it is never used to dispatch native control. -/
private lemma emitter_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The silent comparator reaches its exact endpoint on its first visit to
either Boolean return state, after a positive number of steps.
**Proof sketch.** Use the exact bounded comparator run and cut it at the first visit to
either absorbing return state. Absorption identifies the full endpoint;
the initial scan state excludes time zero. -/
private lemma emitter_compare_first (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∃ t, 0 < t ∧ t ≤ 2 * (max u.length v.length + 1) ∧
      (∀ j < t, ∀ b, (emitterCompareTM.tm.runFrom
        (emitterCompareCfg w u v p 0 true 0) j).state ≠ some (2, b)) ∧
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) t =
        emitterCompareCfg w u v p 2 (decide (u = v)) 0 := by
  obtain ⟨t, ht, hfirst, hr⟩ := emitter_first_entry emitterCompareTM.tm
    (fun q : Fin 3 × Bool => q.1 = 2)
    (emitterCompareCfg w u v p 0 true 0) (emitterCompareCfg w u v p 2 (decide (u = v)) 0)
    (2 * (max u.length v.length + 1)) (by
      rintro z ⟨⟨q, b⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      unfold MultiTapeTM.step
      rw [hz]
      change (controlAction 0 (some (2, b))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨(2, decide (u = v)), rfl, rfl⟩ (emitter_compare_run w u v p)
  have hpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hh := congrArg Cfg.state hr
    simp [hz, emitterCompareCfg] at hh
    have hv := congrArg (fun q : Fin 3 × Bool => q.1.val) hh
    norm_num at hv
  exact ⟨t, hpos, ht, fun j hj b hb => hfirst j hj ⟨(2, b), hb, rfl⟩, hr⟩

/-- Canonical binary words represent natural numbers injectively. This is
used only to identify an already-completed whole-word comparison. -/
private lemma emitter_bits_injective : Function.Injective Nat.bits := by
  have decode (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit b n hn ih => rw [Nat.bits_append_bit n b hn, List.foldr_cons, ih]
  intro m n h
  have he := congrArg (fun w : List Bool => w.foldr Nat.bit 0) h
  simpa only [decode] using he

/-- Comparing entire canonical binary words is exactly the width equation
on every candidate within the native input. This includes two empty words. -/
private lemma emitter_binary_check (f : ℕ → ℕ) (w s : List Bool)
    (hs : s.length ≤ w.length) :
    (Nat.bits (f s.length) = Nat.bits (w.drop s.length).length) ↔
      s.length + f s.length = w.length := by
  rw [emitter_bits_injective.eq_iff, List.length_drop]
  omega

/-- The evaluator and its captured output are charged at the actual candidate
length before monotonicity enlarges the bound. No preparation-length surrogate
is supplied as the argument of the arbitrary monotone budget. -/
private lemma emitter_width_budget (f : ℕ → ℕ) (E : FinTM Bool)
    (TE : ℕ → ℕ) (hTE : Monotone TE)
    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE)
    (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    E.ComputesInTime s (Nat.bits (f s.length)) (TE s.length) ∧
      (Nat.bits (f s.length)).length ≤ TE s.length ∧ TE s.length ≤ TE (w.length + 1) := by
  have he := hE s
  have hout := ((computesInTime_iff _ _ _ _).mp he).2
  refine ⟨he, ?_, hTE hs⟩
  simpa only [hout] using E.tm.output_length_le s (TE s.length)

/-! **Emitter P2 implementation.** The controller below proves the
width-parametric split contract. Its generic relocation layer is reimplemented
from batch L's `emCall` family in `Build/Loop.lean`, per the private-harvest
policy. It preserves inactive storage and follows observed returns, including
the mandatory first action when entry equals exit. -/









/-- Clear one contiguous administrative word and restore its head. Unlike
source-bank cleanup, this phase may use blanks as word boundaries: the input
is a complete canonical word returned by a clean call. -/
private def emitterP2EraseTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q _ work => match q.val with
      | 0 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (some none, .neg), none, some 1⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 2⟩
      | _ => controlAction 0 (some 2) }

/-- The eraser keeps the physical input at its origin and emits nothing. -/
private def emitterP2EraseCfg (w u : List Bool) (q : Fin 3) (h : ℤ) :
    Cfg 1 Bool (Fin 3) w :=
  ⟨some q, 1, fun _ => bufferTape u, fun _ => h, []⟩

/-- Scan the intact administrative word to its right blank.
**Proof sketch.** Every proper prefix ends at a nonblank cell. The phase
preserves the word and advances its sole head by one. -/
private lemma emitterP2_erase_scan (w u : List Bool) : ∀ j, j ≤ u.length →
    emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) j =
      emitterP2EraseCfg w u 0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < u.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Erase right to left, then cross the left blank once to restore zero.
**Proof sketch.** Induct by removing the last bit. Erasing its cell restores
exactly the shorter buffer, including blanks outside it. The empty case
moves from minus one to zero without a write. -/
private lemma emitterP2_erase_back (w u : List Bool) :
    emitterP2EraseTM.tm.runFrom
      (emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1)) (u.length + 1) =
        emitterP2EraseCfg w [] 2 0 := by
  induction u using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nil]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | append_singleton u b ih =>
    have hs : emitterP2EraseTM.tm.step
        (emitterP2EraseCfg w (u ++ [b]) 1 (((u ++ [b]).length : ℤ) - 1)) =
          emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
      have hp : (((u ++ [b]).length : ℤ) - 1) = (u.length : ℤ) := by simp
      rw [hp]
      simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
        Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; exact catalogBuffer_erase u b
      · funext i; simp [Action.apply, sub_eq_add_neg]
    simp only [List.length_append, List.length_singleton] at hs ⊢
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih

/-- The complete administrative-word erasure costs twice its length plus two.
All cells, the head, physical output, and native input position are restored. -/
private lemma emitterP2_erase_run (w u : List Bool) :
    emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) (2 * (u.length + 1)) =
      emitterP2EraseCfg w [] 2 0 := by
  have hs := emitterP2_erase_scan w u u.length (le_refl _)
  have ht : emitterP2EraseTM.tm.step (emitterP2EraseCfg w u 0 u.length) =
      emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_length]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, sub_eq_add_neg]
  have ha : emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) (u.length + 1) =
      emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hs, ht]
  rw [show 2 * (u.length + 1) = (u.length + 1) + (u.length + 1) by omega,
    MultiTapeTM.runFrom_add, ha]
  exact emitterP2_erase_back w u

/-- Cut the eraser at its observed first return. No length is used as a
native clock, and the return is positive even when the word is empty.
**Proof sketch.** Cut the absorbing eraser exit at its least visit. Absorption preserves the full blank endpoint, and distinct initial/exit controls give positive time. -/
private lemma emitterP2_erase_first (w u : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * (u.length + 1) ∧
      (∀ j < t, (emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) j).state
        ≠ some (2 : Fin 3)) ∧
      emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) t =
        emitterP2EraseCfg w [] 2 0 := by
  obtain ⟨t, ht, hf, hr⟩ := emitter_first_entry emitterP2EraseTM.tm
    (fun q : Fin 3 => q = 2) (emitterP2EraseCfg w u 0 0) (emitterP2EraseCfg w [] 2 0)
    (2 * (u.length + 1)) (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨(2 : Fin 3), rfl, rfl⟩ (emitterP2_erase_run w u)
  refine ⟨t, ?_, ht, fun j hj h => hf j hj ⟨(2 : Fin 3), h, rfl⟩, hr⟩
  by_contra h
  have hz : t = 0 := by omega
  have he := congrArg Cfg.state hr
  simp [hz, emitterP2EraseCfg] at he
/-- Prepare the exact candidate and original native suffix on two fresh word
tapes. The candidate itself is retained, all heads are restored, and a finite
flag records only whether the candidate passed the native right boundary. -/
private def emitterP2PrepareTM : FinTM Bool where
  k := 3
  State := Fin 9 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some b => ⟨.pos, fun i =>
            (if i = 1 then some (some b) else none, if i = 2 then 0 else .pos),
            none, some (0, q.2 || inp.isNone)⟩
        | none => controlAction 0 (some (1, q.2))
      | 1 => match inp with
        | some b => ⟨.pos, fun i =>
            (if i = 2 then some (some b) else none, if i = 2 then .pos else 0),
            none, some (1, q.2)⟩
        | none => controlAction 0 (some (2, q.2))
      | 2 => ⟨0, fun i => (none, if i = 2 then 0 else .neg), none, some (3, q.2)⟩
      | 3 => match work 0 with
        | some _ => ⟨0, fun i => (none, if i = 2 then 0 else .neg), none, some (3, q.2)⟩
        | none => ⟨0, fun i => (none, if i = 2 then 0 else .pos), none, some (4, q.2)⟩
      | 4 => ⟨0, fun i => (none, if i = 2 then .neg else 0), none, some (5, q.2)⟩
      | 5 => match work 2 with
        | some _ => ⟨0, fun i => (none, if i = 2 then .neg else 0), none, some (5, q.2)⟩
        | none => ⟨0, fun i => (none, if i = 2 then .pos else 0), none, some (6, q.2)⟩
      | 6 => controlAction .neg (some (7, q.2))
      | 7 => match inp with
        | some _ => controlAction .neg (some (7, q.2))
        | none => controlAction .pos (some (8, q.2))
      | _ => controlAction 0 (some (8, q.2)) }

/-- Preparation frames keep candidate and evaluator-argument heads aligned;
the third tape contains the scanned native suffix. -/
private def emitterP2PrepareCfg (w s u v : List Bool) (q : Fin 9) (over : Bool)
    (p : Fin (w.length + 2)) (a b : ℤ) : Cfg 3 Bool emitterP2PrepareTM.State w :=
  ⟨some (q, over), p,
    (fun i => if i = 0 then bufferTape s else if i = 1 then bufferTape u else bufferTape v),
    (fun i => if i = 2 then b else a), []⟩

/-- The candidate copy uses its literal bits and length. The overflow flag is
set exactly when a nonblank candidate cell faces the native right boundary.
**Proof sketch.** Induct on the candidate prefix. The source candidate never
changes; the second tape appends the same bit; the native head advances with
saturation, and the finite flag updates the strict length comparison. -/
private lemma emitterP2_prepare_candidate (w s : List Bool) : ∀ j, j ≤ s.length →
    emitterP2PrepareTM.tm.runFrom
      (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) j =
        emitterP2PrepareCfg w s (s.take j) [] 0 (decide (w.length < j))
          (splitPos w j) j 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [emitterP2PrepareCfg, splitPos]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    let c := emitterP2PrepareCfg w s (s.take j) [] 0 (decide (w.length < j))
      (splitPos w j) j 0
    have hin := splitPos_read w c j rfl
    have hb : (decide (w.length < j) || c.inputSymbol.isNone) =
        decide (w.length < j + 1) := by
      rw [hin]
      split <;> simp_all <;> omega
    have hlen : (s.take j).length = j := List.length_take_of_le (by omega)
    have hwrite : Function.update (bufferTape (s.take j)) (j : ℤ) (some s[j]) =
        bufferTape (s.take (j + 1)) := by
      rw [List.take_succ, List.getElem?_eq_getElem (by omega : j < s.length)]
      simpa only [Option.toList_some, hlen] using (bufferTape_append (s.take j) s[j]).symm
    change emitterP2PrepareTM.tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg, emitterP2PrepareTM,
      Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < s.length)]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun b => some ((0 : Fin 9), b)) hb
    · funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, hwrite]
    · funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
/-- Copy the actual native suffix after consuming the candidate length.
**Proof sketch.** At suffix index `j`, the native head reads position
`|s|+j`; the third tape appends exactly that bit. The other tapes are fixed. -/
private lemma emitterP2_prepare_suffix (w s : List Bool) (over : Bool) :
    ∀ j, j ≤ (w.drop s.length).length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0) j =
          emitterP2PrepareCfg w s s ((w.drop s.length).take j) 1 over
            (splitPos w (s.length + j)) s.length j := by
  intro j
  induction j with
  | zero => intro _; simp [emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : s.length + j < w.length := by simp only [List.length_drop] at hj; omega
    let v := w.drop s.length
    let c := emitterP2PrepareCfg w s s (v.take j) 1 over
      (splitPos w (s.length + j)) s.length j
    have hin : c.inputSymbol = some v[j] := by
      rw [splitPos_read w c (s.length + j) rfl, dif_pos hlt]
      simp [v, List.getElem_drop]
    have hlen : (v.take j).length = j := List.length_take_of_le (by dsimp [v]; omega)
    have hwrite : Function.update (bufferTape (v.take j)) (j : ℤ) (some v[j]) =
        bufferTape (v.take (j + 1)) := by
      rw [List.take_succ, List.getElem?_eq_getElem (by dsimp [v]; omega : j < v.length)]
      simpa only [Option.toList_some, hlen] using (bufferTape_append (v.take j) v[j]).symm
    change emitterP2PrepareTM.tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg]
    change (emitterP2PrepareTM.tm.tr (1, over) c.inputSymbol c.workTapeSymbols).apply c = _
    rw [hin]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · simpa only [Nat.add_assoc] using splitPos_succ w (s.length + j)
    · funext i; fin_cases i <;> simp [emitterP2PrepareTM, Action.apply, c,
        emitterP2PrepareCfg, hwrite] <;> rfl
    · funext i; fin_cases i <;> simp [emitterP2PrepareTM, Action.apply, c,
        emitterP2PrepareCfg]

/-- Rewind the candidate and its copy together without changing either word.
The physical input and prepared suffix remain fixed.
**Proof sketch.** Induct on the distance from the left blank. Each nonblank candidate cell moves both aligned heads left; the blank transition restores both to zero. -/
private lemma emitterP2_prepare_rewind_candidate (w s v : List Bool) (over : Bool)
    (p : Fin (w.length + 2)) (b : ℤ) : ∀ j, j ≤ s.length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s v 3 over p ((j : ℤ) - 1) b) (j + 1) =
          emitterP2PrepareCfg w s s v 4 over p 0 b := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step, emitterP2PrepareCfg,
      emitterP2PrepareTM, Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    have hs : emitterP2PrepareTM.tm.step
        (emitterP2PrepareCfg w s s v 3 over p (((j + 1 : ℕ) : ℤ) - 1) b) =
          emitterP2PrepareCfg w s s v 3 over p ((j : ℤ) - 1) b := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
        Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Rewind the suffix word to zero after candidate restoration.
**Proof sketch.** Induct on the suffix head distance. The word is retained, and one final right move from the left blank restores the origin. -/
private lemma emitterP2_prepare_rewind_suffix (w s v : List Bool) (over : Bool)
    (p : Fin (w.length + 2)) : ∀ j, j ≤ v.length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s v 5 over p 0 ((j : ℤ) - 1)) (j + 1) =
          emitterP2PrepareCfg w s s v 6 over p 0 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step, emitterP2PrepareCfg,
      emitterP2PrepareTM, Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    have hs : emitterP2PrepareTM.tm.step
        (emitterP2PrepareCfg w s s v 5 over p 0 (((j + 1 : ℕ) : ℤ) - 1)) =
          emitterP2PrepareCfg w s s v 5 over p 0 ((j : ℤ) - 1) := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
        Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < v.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)
/-- Concatenate exact native phase endpoints without hiding dispatch steps. -/
private lemma emitterP2_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) {a b : ℕ} {c d e : Cfg k Bool S w}
    (ha : tm.runFrom c a = d) (hb : tm.runFrom d b = e) :
    tm.runFrom c (a + b) = e := by
  rw [MultiTapeTM.runFrom_add, ha, hb]

/-- The complete native preparation restores every head and presents the
actual candidate and actual original suffix on clean argument tapes.
**Proof sketch.** Copy the candidate, copy the remaining native input, rewind
the two aligned candidate heads, rewind the suffix head, and finally rewind
the native input. Every transition between these phases is charged. -/
private lemma emitterP2_prepare_run (w s : List Bool) :
    ∃ t ≤ 5 * (s.length + w.length + 3),
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) t =
          emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0 := by
  let tm := emitterP2PrepareTM.tm
  let v := w.drop s.length
  let over := decide (w.length < s.length)
  let p := splitPos w (s.length + v.length)
  have hp : p.val = w.length + 1 := by
    dsimp [p, splitPos, v]
    simp only [List.length_drop]
    omega
  have hcopy := emitterP2_prepare_candidate w s s.length (le_refl _)
  simp only [List.take_length] at hcopy
  have h1 : tm.runFrom (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) (s.length + 1) =
      emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0 := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcopy]
    simp only [tm, MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
      Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat, List.getElem?_length]
    rw [controlAction_apply, moveInputPos_zero]
  have hsuffix := emitterP2_prepare_suffix w s over v.length (le_refl _)
  simp only [v, List.take_length] at hsuffix
  have h2 : tm.runFrom
      (emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0) (v.length + 1) =
        emitterP2PrepareCfg w s s v 2 over p s.length v.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hsuffix]
    let c := emitterP2PrepareCfg w s s v 1 over p s.length v.length
    have hin : c.inputSymbol = none := by simp [Cfg.inputSymbol, c, emitterP2PrepareCfg, hp]
    change tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg]
    change (emitterP2PrepareTM.tm.tr (1, over) c.inputSymbol c.workTapeSymbols).apply c = _
    rw [hin]
    change (controlAction 0 (some ((2 : Fin 9), over))).apply c = _
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  have h3 : tm.runFrom (emitterP2PrepareCfg w s s v 2 over p s.length v.length)
      (1 + (s.length + 1)) = emitterP2PrepareCfg w s s v 4 over p 0 v.length := by
    have hstep : tm.step (emitterP2PrepareCfg w s s v 2 over p s.length v.length) =
        emitterP2PrepareCfg w s s v 3 over p ((s.length : ℤ) - 1) v.length := by
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, tm, emitterP2PrepareTM]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, sub_eq_add_neg]
    rw [Nat.add_comm 1 _, MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact emitterP2_prepare_rewind_candidate w s v over p v.length s.length (le_refl _)
  have h4 : tm.runFrom (emitterP2PrepareCfg w s s v 4 over p 0 v.length)
      (1 + (v.length + 1)) = emitterP2PrepareCfg w s s v 6 over p 0 0 := by
    have hstep : tm.step (emitterP2PrepareCfg w s s v 4 over p 0 v.length) =
        emitterP2PrepareCfg w s s v 5 over p 0 ((v.length : ℤ) - 1) := by
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, tm, emitterP2PrepareTM]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, sub_eq_add_neg]
    rw [Nat.add_comm 1 _, MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact emitterP2_prepare_rewind_suffix w s v over p v.length (le_refl _)
  obtain ⟨r, hr, h5⟩ := catalogRewind tm ((6 : Fin 9), over) ((7 : Fin 9), over)
    (some ((8 : Fin 9), over)) (fun _ _ => rfl) (fun _ _ => rfl)
    (emitterP2PrepareCfg w s s v 6 over p 0 0) rfl
  have hr' : r ≤ w.length + 3 := by simpa only [emitterP2PrepareCfg, hp] using hr
  have h5' : tm.runFrom (emitterP2PrepareCfg w s s v 6 over p 0 0) r =
      emitterP2PrepareCfg w s s v 8 over 1 0 0 := h5
  refine ⟨s.length + 1 + (v.length + 1) + (1 + (s.length + 1)) +
    (1 + (v.length + 1)) + r, ?_, ?_⟩
  · have hv : v.length ≤ w.length := by dsimp [v]; simp only [List.length_drop]; omega
    omega
  · exact emitterP2_join tm (emitterP2_join tm (emitterP2_join tm
      (emitterP2_join tm h1 h2) h3) h4) h5'

/-- Preparation can be dispatched on its first observed return, with a
positive duration even for empty input and an empty candidate.
**Proof sketch.** Cut the complete preparation run at its first visit to its absorbing return phase. The complete frame is unchanged by later steps, so the first visit has that same frame. -/
private lemma emitterP2_prepare_first (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 5 * (s.length + w.length + 3) ∧
      (∀ j < t, ∀ b, (emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) j).state ≠ some ((8 : Fin 9), b)) ∧
      emitterP2PrepareTM.tm.runFrom (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) t =
        emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0 := by
  obtain ⟨T, hT, hr⟩ := emitterP2_prepare_run w s
  obtain ⟨t, ht, hf, he⟩ := emitter_first_entry emitterP2PrepareTM.tm
    (fun q : Fin 9 × Bool => q.1 = 8) _ _ T (by
      rintro z ⟨⟨q, b⟩, hz, hq⟩
      change q = 8 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some ((8 : Fin 9), b))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨((8 : Fin 9), decide (w.length < s.length)), rfl, rfl⟩ hr
  refine ⟨t, ?_, ht.trans hT, fun j hj b h => hf j hj ⟨((8 : Fin 9), b), h, rfl⟩, he⟩
  by_contra h
  have hz : t = 0 := by omega
  have he' := congrArg Cfg.state he
  simp [hz, emitterP2PrepareCfg] at he'
  have hv := congrArg (fun q : Fin 9 × Bool => q.1.val) he'.symm
  norm_num at hv
/-- A tape-embedded phase reaches its source endpoint and avoids the outer
anchor throughout the trace.
**Proof sketch.** R1 identifies each embedded prefix. The public injective
state-transport theorem applies guarded agreement on the host carrier, and
the range of the state embedding excludes the anchor. -/
private lemma emitterP2_phase {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (index : Fin k ↪ Fin l) (emb : S ↪ H) (anchor : H)
    (haway : ∀ q, emb q ≠ anchor) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work,
      host.tr (emb q) inp work = ((embedEmitTM index src).tr q inp work).mapState emb)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c d : Cfg k Bool S x) (t : ℕ)
    (hguard : ∀ j < t, ∀ q, (src.runFrom c j).state = some q → good q)
    (hr : src.runFrom c t = d) :
    host.runFrom ((embedEmitCfg index tapes heads [] c).mapState emb) t =
        (embedEmitCfg index tapes heads [] d).mapState emb ∧
      splitSafe host anchor ((embedEmitCfg index tapes heads [] c).mapState emb) t := by
  have trace (j : ℕ) (hj : j ≤ t) :=
    MultiTapeTM.runFrom_mapState_of_agreeOn (embedEmitTM index src) host emb good hagree
      (embedEmitCfg index tapes heads [] c) j (by
        intro u hu q hq
        rw [embedEmitTM_runFrom] at hq
        exact hguard u (lt_of_lt_of_le hu hj) q hq)
  simp only [embedEmitTM_runFrom] at trace
  constructor
  · simpa only [hr] using trace t le_rfl
  · intro j hj
    rw [trace j hj]
    change (src.runFrom c j).state.map emb ≠ some anchor
    intro he
    obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.mp he
    exact haway q hq

/-- A clean call executes its first action at a separate entry control,
including when the source entry equals its exit.
**Proof sketch.** R1 at time one and state-map compatibility identify the
mandatory first action. Transfer the remaining source prefix as one phase;
only positive source times are then tested by the exit guard. -/
private lemma emitterP2_call_phase {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (index : Fin k ↪ Fin l) (emb : S ↪ H)
    (enter anchor : H) (henter : enter ≠ anchor) (haway : ∀ q, emb q ≠ anchor)
    (entry exit : S)
    (hstart : ∀ inp work, host.tr enter inp work =
      ((embedEmitTM index src).tr entry inp work).mapState emb)
    (hagree : ∀ q, q ≠ exit → ∀ inp work,
      host.tr (emb q) inp work = ((embedEmitTM index src).tr q inp work).mapState emb)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c d : Cfg k Bool S x) (hc : c.state = some entry) (t : ℕ) (ht : 0 < t)
    (hguard : ∀ j, 0 < j → j < t → (src.runFrom c j).state ≠ some exit)
    (hr : src.runFrom c t = d) :
    let z := {(embedEmitCfg index tapes heads [] c).mapState emb with state := some enter}
    host.runFrom z t = (embedEmitCfg index tapes heads [] d).mapState emb ∧
      splitSafe host anchor z t := by
  cases t with
  | zero => omega
  | succ t =>
    let ec := embedEmitCfg index tapes heads [] c
    let z := {ec.mapState emb with state := some enter}
    have first : host.runFrom z 1 = (embedEmitCfg index tapes heads [] (src.runFrom c 1)).mapState emb := by
      change host.step z = (embedEmitCfg index tapes heads [] (src.step c)).mapState emb
      have r1 := congrArg (Cfg.mapState emb) (embedEmitTM_runFrom index src tapes heads [] c 1)
      change ((embedEmitTM index src).step ec).mapState emb =
        (embedEmitCfg index tapes heads [] (src.step c)).mapState emb at r1
      rw [← r1]
      have control : ec.state = some entry := hc
      simp only [MultiTapeTM.step, z, control, hstart]
      exact Cfg.mapState_apply emb _ ec
    obtain ⟨endpoint, safe⟩ := emitterP2_phase src host index emb anchor haway
      (fun q => q ≠ exit) hagree tapes heads (src.runFrom c 1) d t
      (by
        intro j hj q hq he
        apply hguard (1 + j) (by omega) (by omega)
        rw [MultiTapeTM.runFrom_add, hq, he])
      (by simpa only [← MultiTapeTM.runFrom_add, Nat.add_comm 1] using hr)
    constructor
    · change host.runFrom z (t + 1) = _
      rw [Nat.add_comm t 1, MultiTapeTM.runFrom_add, first]
      exact endpoint
    · intro j hj
      cases j with
      | zero => exact fun he => henter (Option.some.inj he)
      | succ j =>
        rw [Nat.add_comm j 1, MultiTapeTM.runFrom_add, first]
        exact safe j (by omega)

/-- Layout: the preserved candidate, the complete width-call bank, then the
complete suffix-length-call bank. Only each bank's first tape carries data
at a seam; all other work tapes are blank. -/
private def emitterP2Words (k l : ℕ) (s u v : List Bool) : Fin (k + l + 1) → List Bool :=
  Fin.cases s (Fin.addCases (stateWord k u) (stateWord l v))

/-- Select the complete left call bank after the candidate tape. -/
private def emitterP2LeftIndex (k l : ℕ) : Fin k ↪ Fin (k + l + 1) :=
  (Fin.castAddEmb l).trans (Fin.succEmb (k + l))

/-- Select the complete right call bank after the candidate tape. -/
private def emitterP2RightIndex (k l : ℕ) : Fin l ↪ Fin (k + l + 1) :=
  (Fin.natAddEmb k).trans (Fin.succEmb (k + l))

/-- Selected source cells and the unselected ambient frame determine the
entire embedded configuration.
**Proof sketch.** Use the two selected-tape exports on the image and the R1
frame contract at time zero off the image. State, input and output are the
remaining three configuration fields. -/
private lemma emitterP2_frame {k l : ℕ} {S H : Type} {x : List Bool}
    (q : S) (index : Fin k ↪ Fin l) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) (d : Cfg l Bool H x)
    (hs : c.state.map emb = d.state) (hi : c.inputPos = d.inputPos)
    (ho : c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (index i) ∧
      c.workTapePos i = d.workTapePos (index i))
    (frame : ∀ j, j ∉ Set.range index → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    (embedEmitCfg index tapes heads [] c).mapState emb = d := by
  have fields (j : Fin l) :
      (embedEmitCfg index tapes heads [] c).workTapes j = d.workTapes j ∧
      (embedEmitCfg index tapes heads [] c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range index
    · obtain ⟨i, rfl⟩ := hj
      simpa only [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos] using selected i
    · obtain ⟨ht, hp⟩ := (embedEmitTM_frame index ⟨q, fun _ _ _ => controlAction 0 none⟩ tapes heads [] c 0).1 j hj
      exact ⟨ht.trans (frame j hj).1, hp.trans (frame j hj).2⟩
  exact Cfg.ext hs hi (funext fun j => (fields j).1) (funext fun j => (fields j).2) ho

/-- The left bank transport restores a complete canonical host seam.
**Proof sketch.** The selected-tape exports give the active bank. The R1
frame export preserves the candidate and the other bank. -/
private lemma emitterP2_left_frame {S H : Type} (k l : ℕ) (emb : S → H)
    (w s u v : List Bool) (q : S) :
    (embedEmitCfg (emitterP2LeftIndex k l)
      (fun i => bufferTape (emitterP2Words k l s [] v i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (stateWord k u))).mapState emb =
        Cfg.ofWords (emb q) (emitterP2Words k l s u v) := by
  apply emitterP2_frame q <;> try rfl
  · intro i
    simp [emitterP2LeftIndex, emitterP2Words, Cfg.ofWords]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h; exact False.elim (h ⟨i, rfl⟩)
      · intro _; simp [emitterP2Words, Cfg.ofWords]

/-- The right bank transport restores a complete canonical host seam.
**Proof sketch.** The selected-tape exports give the active bank. The R1
frame export preserves the candidate and the other bank. -/
private lemma emitterP2_right_frame {S H : Type} (k l : ℕ) (emb : S → H)
    (w s u v : List Bool) (q : S) :
    (embedEmitCfg (emitterP2RightIndex k l)
      (fun i => bufferTape (emitterP2Words k l s u [] i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (stateWord l v))).mapState emb =
        Cfg.ofWords (emb q) (emitterP2Words k l s u v) := by
  apply emitterP2_frame q <;> try rfl
  · intro i
    simp [emitterP2RightIndex, emitterP2Words, Cfg.ofWords]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro _; simp [emitterP2Words, Cfg.ofWords]
      · intro h; exact False.elim (h ⟨i, rfl⟩)

/-- With both argument words erased, the complete host seam is exactly the
loop's canonical state-word seam, including every inactive tape. -/
private lemma emitterP2_words_clean (k l : ℕ) (s : List Bool) :
    emitterP2Words k l s [] [] = stateWord (k + l + 1) s := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [emitterP2Words, stateWord]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [emitterP2Words, stateWord]
/-- A singleton source occupies exactly the specified physical tape. -/
private def emitterP2OneIndex {l : ℕ} (slot : Fin l) : Fin 1 ↪ Fin l where
  toFun _ := slot
  inj' := fun _ _ _ => Subsingleton.elim _ _

/-- A singleton transport changes precisely one host word. -/
private lemma emitterP2_one_frame {l : ℕ} {S H : Type} (slot : Fin l) (emb : S → H)
    (words : Fin l → List Bool) (w u : List Bool) (q : S) :
    (embedEmitCfg (emitterP2OneIndex slot) (fun i => bufferTape (words i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (fun _ : Fin 1 => u))).mapState emb =
        Cfg.ofWords (emb q) (Function.update words slot u) := by
  apply emitterP2_frame q <;> try rfl
  · intro i; simp [emitterP2OneIndex, Cfg.ofWords]
  · intro j hj
    have hne : j ≠ slot := fun h => hj ⟨0, h.symm⟩
    simp [Cfg.ofWords, Function.update_of_ne hne]

/-- Inject the 3 administrative tapes into their distinct physical slots. -/
private def emitterP2SmallIndex (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Fin 3 ↪ Fin (k + l + 1) where
  toFun i := if i = 0 then 0 else if i = 1 then emitterP2LeftIndex k l ⟨0, hk⟩
    else emitterP2RightIndex k l ⟨0, hl⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals simp [emitterP2LeftIndex, emitterP2RightIndex] at hv <;> omega

/-- The administrative transport is the complete three-word host seam.
**Proof sketch.** The selected slots carry the source words. Every other
slot is an unchanged candidate or a blank scratch tape, by the R1 frame. -/
private lemma emitterP2_small_frame {H : Type} (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (emb : Fin 9 × Bool → H) (w s u v : List Bool) (q : Fin 9) (over : Bool) :
    (embedEmitCfg (emitterP2SmallIndex k l hk hl) (fun _ _ => none) (fun _ => 0) []
      (emitterP2PrepareCfg w s u v q over 1 0 0)).mapState emb =
        Cfg.ofWords (emb (q, over)) (emitterP2Words k l s u v) := by
  apply emitterP2_frame (q, over) <;> try rfl
  · intro i
    fin_cases i <;> simp [emitterP2SmallIndex, emitterP2LeftIndex, emitterP2RightIndex,
      emitterP2Words, emitterP2PrepareCfg, Cfg.ofWords, stateWord, Fin.addCases, hk]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro h; exact False.elim (h ⟨0, rfl⟩)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hk⟩ := Fin.ext he
          subst i
          exact h ⟨1, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hl⟩ := Fin.ext he
          subst i
          exact h ⟨2, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]

/-- Inject the 2 administrative tapes into their distinct physical slots. -/
private def emitterP2PairIndex (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Fin 2 ↪ Fin (k + l + 1) where
  toFun i := if i = 0 then emitterP2LeftIndex k l ⟨0, hk⟩
    else emitterP2RightIndex k l ⟨0, hl⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals simp [emitterP2LeftIndex, emitterP2RightIndex] at hv <;> omega

/-- The administrative transport is the complete three-word host seam.
**Proof sketch.** The selected slots carry the source words. Every other
slot is an unchanged candidate or a blank scratch tape, by the R1 frame. -/
private lemma emitterP2_pair_frame {H : Type} (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (emb : Fin 3 × Bool → H) (w s u v : List Bool) (q : Fin 3) (b : Bool) :
    (embedEmitCfg (emitterP2PairIndex k l hk hl) (fun i => bufferTape (emitterP2Words k l s [] [] i)) (fun _ => 0) []
      (emitterCompareCfg w u v 1 q b 0)).mapState emb =
        Cfg.ofWords (emb (q, b)) (emitterP2Words k l s u v) := by
  apply emitterP2_frame (q, b) <;> try rfl
  · intro i
    fin_cases i <;> simp [emitterP2PairIndex, emitterP2LeftIndex, emitterP2RightIndex,
      emitterP2Words, emitterCompareCfg, Cfg.ofWords, stateWord, Fin.addCases, hk]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hk⟩ := Fin.ext he
          subst i
          exact h ⟨0, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hl⟩ := Fin.ext he
          subst i
          exact h ⟨1, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]

/-- Updating the first width-bank word leaves the entire other layout intact.
**Proof sketch.** Split the host index into its three blocks. Only the first width-bank index equals the update address; every other index is unchanged. -/
private lemma emitterP2_update_left (k l : ℕ) (hk : 0 < k) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) (emitterP2LeftIndex k l ⟨0, hk⟩) a =
      emitterP2Words k l s a v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update, emitterP2LeftIndex, emitterP2Words]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases hj : j.val = 0
      · have he : j = ⟨0, hk⟩ := Fin.ext hj
        subst j; simp [emitterP2LeftIndex, emitterP2Words, stateWord, Fin.addCases, hk]
      · have he : (Fin.castAdd l j).succ ≠ emitterP2LeftIndex k l ⟨0, hk⟩ := by
          intro h; apply hj; have hv := congrArg Fin.val h; simpa [emitterP2LeftIndex] using hv
        rw [Function.update_of_ne he]
        simp [emitterP2Words, stateWord, hj]
    · have he : (Fin.natAdd k j).succ ≠ emitterP2LeftIndex k l ⟨0, hk⟩ := by
        intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
      rw [Function.update_of_ne he]
      simp [emitterP2Words]

/-- Updating the first length-bank word preserves the candidate and width.
**Proof sketch.** Split the host index into its three blocks. Only the first length-bank index equals the update address; every other index is unchanged. -/
private lemma emitterP2_update_right (k l : ℕ) (hl : 0 < l) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) (emitterP2RightIndex k l ⟨0, hl⟩) a =
      emitterP2Words k l s u a := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update, emitterP2RightIndex, emitterP2Words]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have he : (Fin.castAdd l j).succ ≠ emitterP2RightIndex k l ⟨0, hl⟩ := by
        intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
      rw [Function.update_of_ne he]
      simp [emitterP2Words]
    · by_cases hj : j.val = 0
      · have he : j = ⟨0, hl⟩ := Fin.ext hj
        subst j; simp [emitterP2RightIndex, emitterP2Words, stateWord, Fin.addCases]
      · have he : (Fin.natAdd k j).succ ≠ emitterP2RightIndex k l ⟨0, hl⟩ := by
          intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
        rw [Function.update_of_ne he]
        simp [emitterP2Words, stateWord, hj]

/-- Updating the preserved candidate changes exactly the loop state word. -/
private lemma emitterP2_update_candidate (k l : ℕ) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) 0 a = emitterP2Words k l a u v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [emitterP2Words, Function.update]
/-- Distinct controller phases keep all proper round interiors away from the
loop anchor. Module-start states enforce the first-step release discipline. -/
private inductive EmitterP2State (S T : Type) where
  | anchor
  | prepare (q : Fin 9 × Bool)
  | widthStart
  | width (q : S)
  | lengthStart
  | length (q : T)
  | compare (q : Fin 3 × Bool)
  | eraseLeft (ok : Bool) (q : Fin 3)
  | eraseRight (ok : Bool) (q : Fin 3)
  | advance (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance emitterP2StateFintype (S T : Type) [Fintype S] [Fintype T] :
    Fintype (EmitterP2State S T) := derive_fintype% _

/-- Controller equality compares only payloads of equal finite phases. -/
private instance emitterP2StateDecidableEq (S T : Type) [DecidableEq S] [DecidableEq T] :
    DecidableEq (EmitterP2State S T) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.prepare.injEq _ _)))
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.width.injEq _ _)))
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.length.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.compare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.eraseLeft.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.eraseRight.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.advance.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.emit.injEq _ _)))

/-- Native split-search controller. Clean-call modules consume the prepared
candidate and suffix; comparison is whole-word; both result words are erased
before acceptance or rejection. The native input is never overwritten and
supplies every payload bit. A past-end preparation bypasses both evaluators.
No time bound or width function appears in the transition table. -/
private def emitterP2BodyTM (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) : FinTM Bool where
  k := C.k + D.k + 1
  State := EmitterP2State C.State D.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 8 then controlAction 0 (some (if p.2 then .eraseLeft false 0 else .widthStart))
        else ((embedEmitTM (emitterP2SmallIndex C.k D.k hk hl) emitterP2PrepareTM.tm).tr p inp work).mapState .prepare
      | .widthStart => ((embedEmitTM (emitterP2LeftIndex C.k D.k) C.tm).tr ce inp work).mapState .width
      | .width p =>
        if p = cx then controlAction 0 (some .lengthStart)
        else ((embedEmitTM (emitterP2LeftIndex C.k D.k) C.tm).tr p inp work).mapState .width
      | .lengthStart => ((embedEmitTM (emitterP2RightIndex C.k D.k) D.tm).tr de inp work).mapState .length
      | .length p =>
        if p = dx then controlAction 0 (some (.compare (0, true)))
        else ((embedEmitTM (emitterP2RightIndex C.k D.k) D.tm).tr p inp work).mapState .length
      | .compare p =>
        if p.1 = 2 then controlAction 0 (some (.eraseLeft p.2 0))
        else ((embedEmitTM (emitterP2PairIndex C.k D.k hk hl) emitterCompareTM.tm).tr p inp work).mapState .compare
      | .eraseLeft ok p =>
        if p = 2 then controlAction 0 (some (.eraseRight ok 0))
        else ((embedEmitTM (emitterP2OneIndex (emitterP2LeftIndex C.k D.k ⟨0, hk⟩))
          emitterP2EraseTM.tm).tr p inp work).mapState (.eraseLeft ok)
      | .eraseRight ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .advance (0, false)))
        else ((embedEmitTM (emitterP2OneIndex (emitterP2RightIndex C.k D.k ⟨0, hl⟩))
          emitterP2EraseTM.tm).tr p inp work).mapState (.eraseRight ok)
      | .advance p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((embedEmitTM (emitterP2OneIndex (0 : Fin (C.k + D.k + 1)))
          (splitRestoreTM 0).tm).tr p inp work).mapState .advance
      | .emit p => ((embedEmitTM (emitterP2OneIndex (0 : Fin (C.k + D.k + 1)))
          (splitEmitTM 0).tm).tr p inp work).mapState .emit }

/-- Genuine startup is already the canonical empty-candidate anchor. -/
private lemma emitterP2_body_start (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w : List Bool) :
    (emitterP2BodyTM C D hk hl ce cx de dx).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (C.k + D.k + 1) []) := by
  rw [initCfg_ofWords]
  change Cfg.ofWords (input := w) (EmitterP2State.anchor (S := C.State) (T := D.State))
    (fun _ : Fin (C.k + D.k + 1) => []) = _
  congr 1
  funext i; simp [stateWord]

/-- A silent controller dispatch preserves every component of a canonical
word seam and changes only control. -/
private lemma emitterP2_control {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S)
    (q r : S) (h : ∀ inp work, tm.tr q inp work = controlAction 0 (some r))
    (w : List Bool) (words : Fin k → List Bool) :
    tm.step (Cfg.ofWords (input := w) q words) = Cfg.ofWords r words := by
  simp only [MultiTapeTM.step, Cfg.ofWords, h]
  rw [controlAction_apply, moveInputPos_zero]
/-- Preparation embeds on exactly the three administrative tapes.
**Proof sketch.** Relocate the first-return preparation trace using the three-slot inverse law. The initial and final frame identities give literal host seams; disjoint controls give anchor exclusion. -/
private lemma emitterP2_body_prepare (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 5 * (s.length + w.length + 3),
      B.tm.runFrom (Cfg.ofWords (input := w) (.prepare (0, false))
        (emitterP2Words C.k D.k s [] [])) t =
        Cfg.ofWords (.prepare (8, decide (w.length < s.length)))
          (emitterP2Words C.k D.k s s (w.drop s.length)) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.prepare (0, false))
        (emitterP2Words C.k D.k s [] [])) t := by
  dsimp only
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_prepare_first w s
  have h := emitterP2_phase emitterP2PrepareTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2SmallIndex C.k D.k hk hl)
    ⟨EmitterP2State.prepare, by intro a b h; exact EmitterP2State.prepare.inj h⟩ .anchor
    (by intro q; simp) (fun q : Fin 9 × Bool => q.1 ≠ 8)
    (fun _ hq _ _ => if_neg hq)
    (fun _ _ => none) (fun _ => 0)
    (emitterP2PrepareCfg w s [] [] 0 false 1 0 0)
    (emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0) t
    (by intro j hj q hq he; rcases q with ⟨q, b⟩; dsimp at he; subst q; exact hf j hj b hq) hr
  erw [emitterP2_small_frame _ _ hk hl, emitterP2_small_frame _ _ hk hl] at h
  exact ⟨t, ht, h⟩

/-- The width call consumes exactly its candidate copy while retaining the
original candidate and prepared native suffix in the other blocks.
**Proof sketch.** Apply the first-action clean-call embedding to the width bank. Both endpoint frame identities preserve the surrounding candidate and suffix and restore every inactive cell and head. -/
private lemma emitterP2_body_width (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (t : ℕ) (ht : 0 < t)
    (hf : ∀ j, 0 < j → j < t → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hr : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) t =
      Cfg.ofWords cx (stateWord C.k u)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    B.tm.runFrom (Cfg.ofWords (input := w) .widthStart (emitterP2Words C.k D.k s s v)) t =
        Cfg.ofWords (.width cx) (emitterP2Words C.k D.k s u v) ∧
      splitSafe B.tm .anchor
        (Cfg.ofWords (input := w) .widthStart (emitterP2Words C.k D.k s s v)) t := by
  dsimp only
  have h := emitterP2_call_phase C.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2LeftIndex C.k D.k)
    ⟨EmitterP2State.width, by intro a b h; exact EmitterP2State.width.inj h⟩ .widthStart .anchor
    (by simp) (by intro q; simp) ce cx (fun _ _ => rfl)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s [] v i)) (fun _ => 0)
    (Cfg.ofWords ce (stateWord C.k s)) (Cfg.ofWords cx (stateWord C.k u)) rfl t ht hf hr
  dsimp only at h
  erw [emitterP2_left_frame, emitterP2_left_frame] at h
  exact h

/-- The length call consumes the actual prepared suffix; its return preserves
the original candidate and the already installed width word.
**Proof sketch.** Apply the first-action clean-call embedding to the length bank, preserving the width result and candidate. Its canonical endpoint supplies every cell and head needed by comparison. -/
private lemma emitterP2_body_length (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v z : List Bool) (t : ℕ) (ht : 0 < t)
    (hf : ∀ j, 0 < j → j < t → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k v)) j).state ≠ some dx)
    (hr : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k v)) t =
      Cfg.ofWords dx (stateWord D.k z)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    B.tm.runFrom (Cfg.ofWords (input := w) .lengthStart (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.length dx) (emitterP2Words C.k D.k s u z) ∧
      splitSafe B.tm .anchor
        (Cfg.ofWords (input := w) .lengthStart (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  have h := emitterP2_call_phase D.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2RightIndex C.k D.k)
    ⟨EmitterP2State.length, by intro a b h; exact EmitterP2State.length.inj h⟩ .lengthStart .anchor
    (by simp) (by intro q; simp) de dx (fun _ _ => rfl)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s u [] i)) (fun _ => 0)
    (Cfg.ofWords de (stateWord D.k v)) (Cfg.ofWords dx (stateWord D.k z)) rfl t ht hf hr
  dsimp only at h
  erw [emitterP2_right_frame, emitterP2_right_frame] at h
  exact h

/-- Compare both complete canonical words at head zero and retain the verdict
in finite control, without changing candidate, buffers, or module scratch.
**Proof sketch.** Relocate the comparator through its first observed return. The endpoint frame identities preserve the entire host layout and expose literal word equality in the controller. -/
private lemma emitterP2_body_compare (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (max u.length v.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.compare (0, true))
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.compare (2, decide (u = v))) (emitterP2Words C.k D.k s u v) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.compare (0, true))
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  obtain ⟨t, _, ht, hf, hr⟩ := emitter_compare_first w u v 1
  have h := emitterP2_phase emitterCompareTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2PairIndex C.k D.k hk hl)
    ⟨EmitterP2State.compare, by intro a b h; exact EmitterP2State.compare.inj h⟩ .anchor
    (by intro q; simp) (fun q : Fin 3 × Bool => q.1 ≠ 2)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s [] [] i)) (fun _ => 0)
    (emitterCompareCfg w u v 1 0 true 0) (emitterCompareCfg w u v 1 2 (decide (u = v)) 0) t
    (by intro j hj q hq he; rcases q with ⟨q, b⟩; dsimp at he; subst q; exact hf j hj b hq) hr
  erw [emitterP2_pair_frame _ _ hk hl, emitterP2_pair_frame _ _ hk hl] at h
  exact ⟨t, ht, h⟩
/-- Erase the complete installed width word, retain the verdict, and preserve
all other tapes. The module's scratch was already restored by its call.
**Proof sketch.** Relocate the contiguous-word eraser onto the first width-bank tape. A singleton-frame identity turns its exact blank return into a single word update, with the verdict retained in control. -/
private lemma emitterP2_body_erase_left (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (u.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseLeft ok 2) (emitterP2Words C.k D.k s [] v) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2LeftIndex C.k D.k ⟨0, hk⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseLeft ok, by intro a b h; exact (EmitterP2State.eraseLeft.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s [] v i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s a v) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_left]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w u
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w u 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩

/-- Erase the complete suffix-length word, retaining the verdict through the
last cleanup phase. All scratch and administrative words are now blank.
**Proof sketch.** Relocate the eraser onto the first length-bank tape. Its singleton-frame identity restores that whole word to blank and retains every other tape and the verdict. -/
private lemma emitterP2_body_erase_right (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (v.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseRight ok 2) (emitterP2Words C.k D.k s u []) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2RightIndex C.k D.k ⟨0, hl⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseRight ok, by intro a b h; exact (EmitterP2State.eraseRight.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s u [] i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s u a) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_right]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w v
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w v 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩

/-- The existing one-tape candidate advance enters at the canonical word seam. -/
private lemma emitterP2_advance_initial (w s : List Bool) :
    splitRestoreScan 0 w s 0 = Cfg.ofWords (0, false) (fun _ : Fin 1 => s) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ rfl
  · simp [splitRestoreScan, Cfg.ofWords]
  · simp [splitRestoreScan, Cfg.ofWords, splitPos]
  · funext i; fin_cases i; rfl
  · funext i; rfl

/-- Every one-tape state word is the constant word function. -/
private lemma emitterP2_stateWord_one (s : List Bool) : stateWord 1 s = fun _ => s := by
  funext i; fin_cases i; rfl

/-- The existing candidate advance is relocated onto the preserved candidate
alone. It appends exactly within the input range, and otherwise stalls.
**Proof sketch.** Use the existing restoration theorem at zero scratch tapes, then relocate its sole candidate tape. Its full returned frame is the successor state word, with the out-of-range stall included. -/
private lemma emitterP2_body_advance (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * s.length + w.length + 5,
      B.tm.runFrom (Cfg.ofWords (input := w) (.advance (0, false))
        (emitterP2Words C.k D.k s [] [])) t =
        Cfg.ofWords (.advance (4, false)) (emitterP2Words C.k D.k (splitStep w s) [] []) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.advance (0, false))
        (emitterP2Words C.k D.k s [] [])) t := by
  dsimp only
  let emb : (Fin 5 × Bool) ↪ EmitterP2State C.State D.State :=
    ⟨.advance, by intro a b h; exact EmitterP2State.advance.inj h⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k [] [] [] i)
  obtain ⟨t, _, ht, hf, hr⟩ := splitRestore_first 0 w s
  have h := emitterP2_phase (splitRestoreTM 0).tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex (0 : Fin (C.k + D.k + 1))) emb .anchor (by intro q; simp [emb])
    (fun q : Fin 5 × Bool => q ≠ (4, false))
    (by intro q hq inp work; simp [emb, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (splitRestoreScan 0 w s 0)
    (Cfg.ofWords (4, false) (stateWord 1 (splitStep w s))) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  rw [emitterP2_advance_initial, emitterP2_stateWord_one] at h
  dsimp only [tapes] at h
  erw [emitterP2_one_frame, emitterP2_one_frame,
    emitterP2_update_candidate, emitterP2_update_candidate] at h
  exact ⟨t, ht, h⟩

/-- The payload emitter's complete one-tape entry is the clean candidate seam. -/
private lemma emitterP2_emit_initial (w s : List Bool) :
    splitEmitCfg 0 w s (some 0) 0 0 [] = Cfg.ofWords 0 (fun _ : Fin 1 => s) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp [splitEmitCfg, Cfg.ofWords, splitPos]
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i; rfl

/-- Acceptance emits the split of the preserved native input, never the
candidate's bits. The exact emitter entry includes input head one and every
work head zero; unrelated banks remain blank throughout.
**Proof sketch.** Use the existing emitter at zero scratch tapes and relocate its sole candidate tape. Its full entry equality and native-input semantics give the stated payload and halt; disjoint emission control excludes the anchor. -/
private lemma emitterP2_body_emit (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) (hs : s.length ≤ w.length) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.emit 0) (emitterP2Words C.k D.k s [] [])
    (B.tm.runFrom z (s.length + w.length + 3)).state = none ∧
      (B.tm.runFrom z (s.length + w.length + 3)).output =
        pairEncode (w.take s.length) (w.drop s.length) ∧
      splitSafe B.tm .anchor z (s.length + w.length + 3) := by
  dsimp only
  let emb : Fin 4 ↪ EmitterP2State C.State D.State :=
    ⟨.emit, by intro a b h; exact EmitterP2State.emit.inj h⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k [] [] [] i)
  have h := emitterP2_phase (splitEmitTM 0).tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex (0 : Fin (C.k + D.k + 1))) emb .anchor (by intro q; simp [emb]) (fun _ => True)
    (fun _ _ _ _ => rfl) tapes (fun _ => 0)
    (splitEmitCfg 0 w s (some 0) 0 0 [])
    (splitEmitCfg 0 w s none w.length s.length (pairEncode (w.take s.length) (w.drop s.length)))
    (s.length + w.length + 3) (by intros; trivial) (splitEmit_run 0 w s hs)
  rw [emitterP2_emit_initial] at h
  dsimp only [tapes] at h
  erw [emitterP2_one_frame, emitterP2_update_candidate] at h
  exact ⟨congrArg Cfg.state h.1, congrArg Cfg.output h.1, h.2⟩
/-- Extend a safe phase by one silent dispatch to another non-anchor phase. -/
private lemma emitterP2_after {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w)
    (t : ℕ) (q r : S) (words : Fin k → List Bool)
    (hr : tm.runFrom c t = Cfg.ofWords q words) (hs : splitSafe tm anchor c t)
    (htr : ∀ inp work, tm.tr q inp work = controlAction 0 (some r))
    (hq : q ≠ anchor) (hnext : r ≠ anchor) :
    tm.runFrom c (t + 1) = Cfg.ofWords r words ∧ splitSafe tm anchor c (t + 1) := by
  obtain ⟨he, hse⟩ := splitSafe_one tm anchor (Cfg.ofWords q words) (Cfg.ofWords r words)
    (emitterP2_control tm q r htr w words)
    (by simpa only [Cfg.ofWords, ne_eq, Option.some.injEq] using hq)
    (by simpa only [Cfg.ofWords, ne_eq, Option.some.injEq] using hnext)
  exact splitSafe_join tm anchor c _ _ t 1 hr hs he hse

/-- The two clean calls and comparison form one safe testing segment. Both
calls are charged before assuming any relation between their results.
**Proof sketch.** Concatenate the unconditional first-step calls and whole-word comparison with four explicit silent dispatches. Each complete frame is the next phase entry; the sum of their bounds includes both evaluator traces before testing equality. -/
private lemma emitterP2_body_test (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hfC : ∀ j, 0 < j → j < a → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hrC : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) a =
      Cfg.ofWords cx (stateWord C.k u))
    (hfD : ∀ j, 0 < j → j < b → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) j).state ≠ some dx)
    (hrD : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) b =
      Cfg.ofWords dx (stateWord D.k v)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.prepare (8, false))
      (emitterP2Words C.k D.k s s (w.drop s.length))
    ∃ t ≤ a + b + 2 * (max u.length v.length + 1) + 4,
      B.tm.runFrom z t = Cfg.ofWords (.eraseLeft (decide (u = v)) 0)
        (emitterP2Words C.k D.k s u v) ∧ splitSafe B.tm .anchor z t := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.prepare (S := C.State) (T := D.State) (8, false))
    (emitterP2Words C.k D.k s s (w.drop s.length))
  have hzsafe : splitSafe tm .anchor z 0 := by
    intro j hj
    have hz : j = 0 := by omega
    subst j
    simp [z, Cfg.ofWords]
  obtain ⟨h0, hs0⟩ := emitterP2_after tm .anchor z 0 (.prepare (8, false)) .widthStart _ rfl hzsafe
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨hE, hsE⟩ := emitterP2_body_width C D hk hl ce cx de dx w s u (w.drop s.length) a ha hfC hrC
  obtain ⟨h1, hs1⟩ := splitSafe_join tm .anchor z _ _ 1 a h0 hs0 hE hsE
  obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor z (1 + a) (.width cx) .lengthStart _ h1 hs1
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨hL, hsL⟩ := emitterP2_body_length C D hk hl ce cx de dx w s u (w.drop s.length) v b hb hfD hrD
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor z _ _ (1 + a + 1) b h2 hs2 hL hsL
  obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (1 + a + 1 + b) (.length dx) (.compare (0, true)) _ h3 hs3
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨c, hc, hQ, hsQ⟩ := emitterP2_body_compare C D hk hl ce cx de dx w s u v
  obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor z _ _ (1 + a + 1 + b + 1) c h4 hs4 hQ hsQ
  obtain ⟨h6, hs6⟩ := emitterP2_after tm .anchor z (1 + a + 1 + b + 1 + c)
    (.compare (2, decide (u = v))) (.eraseLeft (decide (u = v)) 0) _ h5 hs5
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  exact ⟨1 + a + 1 + b + 1 + c + 1, by omega, h6, hs6⟩

/-- Cleanup and final dispatch close either branch at its literal target.
**Proof sketch.** Erase each installed word and retain the verdict in control.
Acceptance enters the complete native payload-emitter configuration. Rejection
runs the one-tape advance and makes one final silent anchor transition. Its
strict-interior exclusion includes every cleanup, rewind, and dispatch. -/
private lemma emitterP2_body_finish (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool)
    (hok : ok = true → s.length ≤ w.length) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.eraseLeft ok 0) (emitterP2Words C.k D.k s u v)
    ∃ t ≤ 2 * u.length + 2 * v.length + 2 * s.length + w.length + 12,
      (∀ j < t, (B.tm.runFrom z j).state ≠ some .anchor) ∧
      if ok then
        (B.tm.runFrom z t).state = none ∧
          (B.tm.runFrom z t).output = pairEncode (w.take s.length) (w.drop s.length)
      else B.tm.runFrom z t = Cfg.ofWords .anchor
        (emitterP2Words C.k D.k (splitStep w s) [] []) := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.eraseLeft (S := C.State) (T := D.State) ok 0)
    (emitterP2Words C.k D.k s u v)
  obtain ⟨a, ha, h1, hs1⟩ := emitterP2_body_erase_left C D hk hl ce cx de dx w s u v ok
  obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor z a (.eraseLeft ok 2) (.eraseRight ok 0) _ h1 hs1
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨b, hb, hR, hsR⟩ := emitterP2_body_erase_right C D hk hl ce cx de dx w s [] v ok
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor z _ _ (a + 1) b h2 hs2 hR hsR
  cases ok with
  | false =>
    obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (a + 1 + b)
      (.eraseRight false 2) (.advance (0, false)) _ h3 hs3
      (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨c, hc, hA, hsA⟩ := emitterP2_body_advance C D hk hl ce cx de dx w s
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor z _ _ (a + 1 + b + 1) c h4 hs4 hA hsA
    have he := emitterP2_control tm (.advance (4, false)) .anchor
      (by intro inp work; simp [tm, emitterP2BodyTM]) w
      (emitterP2Words C.k D.k (splitStep w s) [] [])
    refine ⟨a + 1 + b + 1 + c + 1, by omega, ?_, ?_⟩
    · intro j hj; exact hs5 j (by omega)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (a + 1 + b + 1 + c + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', h5, he]
  | true =>
    obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (a + 1 + b)
      (.eraseRight true 2) (.emit 0) _ h3 hs3
      (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨he, ho, hse⟩ := emitterP2_body_emit C D hk hl ce cx de dx w s (hok rfl)
    have hsall : splitSafe tm .anchor z (a + 1 + b + 1 + (s.length + w.length + 3)) := by
      apply splitSafe_add tm .anchor z (a + 1 + b + 1) (s.length + w.length + 3) hs4
      rw [h4]; exact hse
    refine ⟨a + 1 + b + 1 + (s.length + w.length + 3), by omega,
      fun j hj => hsall j (by omega), ?_⟩
    simp only [↓reduceIte]
    change (tm.runFrom z _).state = none ∧ _
    rw [MultiTapeTM.runFrom_add, h4]
    exact ⟨he, ho⟩
/-- A safe prefix followed by a strictly safe terminal segment remains away
from the anchor before its final time, even when that final time returns. -/
private lemma emitterP2_strict_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w) (a b : ℕ)
    (hr : tm.runFrom c a = d) (hs : splitSafe tm anchor c a)
    (hf : ∀ j < b, (tm.runFrom d j).state ≠ some anchor) :
    ∀ j < a + b, (tm.runFrom c j).state ≠ some anchor := by
  intro j hj
  by_cases hja : j ≤ a
  · exact hs j hja
  · rw [show j = a + (j - a) by omega, MultiTapeTM.runFrom_add, hr]
    exact hf (j - a) (by omega)

/-- Full native round, parameterized by the two actual clean-call traces.
**Proof sketch.** Depart the anchor, prepare the exact two arguments, and
branch on the observed past-end flag. The past-end branch erases preparation
and returns silently. Otherwise run both calls before comparing their entire
binary answers. The verdict survives cleanup; the finish theorem emits the
native split or advances to the exact canonical seam. Every interior phase
excludes the anchor, and the one-step departure makes every round positive. -/
private lemma emitterP2_body_round (f : ℕ → ℕ) (C D : FinTM Bool)
    (hk : 0 < C.k) (hl : 0 < D.k) (ce cx : C.State) (de dx : D.State)
    (w s : List Bool) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hfC : ∀ j, 0 < j → j < a → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hrC : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) a =
      Cfg.ofWords cx (stateWord C.k (Nat.bits (f s.length))))
    (hfD : ∀ j, 0 < j → j < b → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) j).state ≠ some dx)
    (hrD : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) b =
      Cfg.ofWords dx (stateWord D.k (Nat.bits (w.drop s.length).length))) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) .anchor (stateWord B.k s)
    ∃ t, 0 < t ∧
      t ≤ a + b + 10 * (s.length + w.length + (Nat.bits (f s.length)).length +
        (Nat.bits (w.drop s.length).length).length + 10) ∧
      (∀ j, 0 < j → j < t → (B.tm.runFrom z j).state ≠ some .anchor) ∧
      if emitterSplitAccept f w s then
        (B.tm.runFrom z t).state = none ∧
          (B.tm.runFrom z t).output = pairEncode (w.take s.length) (w.drop s.length)
      else B.tm.runFrom z t = Cfg.ofWords .anchor (stateWord B.k (splitStep w s)) := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.anchor (S := C.State) (T := D.State))
    (stateWord (C.k + D.k + 1) s)
  let p := Cfg.ofWords (input := w) (EmitterP2State.prepare (S := C.State) (T := D.State) (0, false))
    (emitterP2Words C.k D.k s [] [])
  have hdepart : tm.runFrom z 1 = p := by
    change tm.step z = p
    simpa only [z, p, emitterP2_words_clean] using emitterP2_control tm .anchor (.prepare (0, false))
      (fun _ _ => rfl) w (emitterP2Words C.k D.k s [] [])
  obtain ⟨c, hc, hp, hps⟩ := emitterP2_body_prepare C D hk hl ce cx de dx w s
  by_cases hover : w.length < s.length
  · have hp' : tm.runFrom p c = Cfg.ofWords (.prepare (8, true))
        (emitterP2Words C.k D.k s s (w.drop s.length)) := by simpa [hover] using hp
    obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor p c (.prepare (8, true)) (.eraseLeft false 0)
      _ hp' hps (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨d, hd, hds, hfinish⟩ := emitterP2_body_finish C D hk hl ce cx de dx w s s
      (w.drop s.length) false (by simp)
    have hstrict := emitterP2_strict_join tm .anchor p _ (c + 1) d h2 hs2 hds
    have hrun : tm.runFrom z (1 + (c + 1 + d)) = tm.runFrom
        (Cfg.ofWords (.eraseLeft false 0) (emitterP2Words C.k D.k s s (w.drop s.length))) d := by
      rw [MultiTapeTM.runFrom_add, hdepart, MultiTapeTM.runFrom_add, h2]
    refine ⟨1 + (c + 1 + d), by omega, ?_, ?_, ?_⟩
    · have hv : (w.drop s.length).length ≤ w.length := by simp only [List.length_drop]; omega
      omega
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hstrict (j - 1) (by omega)
    · have hn : s.length + f s.length ≠ w.length := by omega
      simp only [emitterSplitAccept, hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + (c + 1 + d)) = _
      rw [hrun]
      simpa only [Bool.false_eq_true, ↓reduceIte, emitterP2_words_clean] using hfinish
  · have hs : s.length ≤ w.length := by omega
    have hp' : tm.runFrom p c = Cfg.ofWords (.prepare (8, false))
        (emitterP2Words C.k D.k s s (w.drop s.length)) := by simpa [hover] using hp
    let u := Nat.bits (f s.length)
    let v := Nat.bits (w.drop s.length).length
    obtain ⟨d, hd, htest, htests⟩ := emitterP2_body_test C D hk hl ce cx de dx w s u v
      a b ha hb hfC hrC hfD hrD
    obtain ⟨h2, hs2⟩ := splitSafe_join tm .anchor p _ _ c d hp' hps htest htests
    obtain ⟨e, he, hes, hfinish⟩ := emitterP2_body_finish C D hk hl ce cx de dx w s u v
      (decide (u = v)) (fun _ => hs)
    have hstrict := emitterP2_strict_join tm .anchor p _ (c + d) e h2 hs2 hes
    have hrun : tm.runFrom z (1 + (c + d + e)) = tm.runFrom
        (Cfg.ofWords (.eraseLeft (decide (u = v)) 0) (emitterP2Words C.k D.k s u v)) e := by
      rw [MultiTapeTM.runFrom_add, hdepart, MultiTapeTM.runFrom_add, h2]
    have hok : decide (u = v) = emitterSplitAccept f w s := by
      apply Bool.eq_iff_iff.mpr
      simpa only [u, v, emitterSplitAccept, decide_eq_true_eq] using emitter_binary_check f w s hs
    refine ⟨1 + (c + d + e), by omega, ?_, ?_, ?_⟩
    · have hm : max u.length v.length ≤ u.length + v.length := max_le (by omega) (by omega)
      change 1 + (c + d + e) ≤ a + b + 10 * (s.length + w.length + u.length + v.length + 10)
      omega
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hstrict (j - 1) (by omega)
    · change if emitterSplitAccept f w s then
        (tm.runFrom z (1 + (c + d + e))).state = none ∧
          (tm.runFrom z (1 + (c + d + e))).output = _
        else tm.runFrom z (1 + (c + d + e)) = _
      rw [hrun]
      simpa only [hok, emitterP2_words_clean] using hfinish
/-- Extract the two clean-call modules once, fix their layout, and close the
frozen split contract through the existing result-bearing loop.
**Proof sketch.** Apply the width evaluator only to the actual candidate and
the length evaluator only to the actual native suffix. Bound each returned
word by its own evaluator deadline, then enlarge those analysis bounds to
the common input-length envelope. The concrete round theorem supplies every
canonical endpoint and strict-interior exclusion. Neither deadline occurs in
the controller; dispatch follows the proved first-positive return instead. -/
private lemma emitterP2_closed (f : ℕ → ℕ) (E : FinTM Bool) (TE : ℕ → ℕ)
    (hTE : Monotone TE) (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun w => match solveSplitWith f w.length with
        | some i => pairEncode (w.take i) (w.drop i)
        | none => [])
      (fun n => c * (n + 1) * (TE (n + 1) + n + 2)) := by
  obtain ⟨L, d, hL⟩ := computesFunInTime_lengthBits
  obtain ⟨C, ce, cx, cC, hk, hC⟩ :=
    exists_installCallTM E (fun s => Nat.bits (f s.length)) TE hE
  obtain ⟨D, de, dx, cD, hl, hD⟩ :=
    exists_installCallTM L (fun s => Nat.bits s.length) (fun n => d * (n + 1)) hL
  let B := emitterP2BodyTM C D hk hl ce cx de dx
  let A := 2 * cC + cD * (2 * d + 1) + 10 * (d + 8)
  apply emitterSplit_of_body f TE B .anchor A
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact emitterP2_body_start C D hk hl ce cx de dx w
  · intro w s hs
    let H := TE (w.length + 1) + w.length + 2
    let u := Nat.bits (f s.length)
    let v := Nat.bits (w.drop s.length).length
    obtain ⟨_, hu, hmono⟩ := emitter_width_budget f E TE hTE hE w s hs
    have hdrop : (w.drop s.length).length ≤ w.length := by simp only [List.length_drop]; omega
    have hv : v.length ≤ d * ((w.drop s.length).length + 1) := by
      have hout := ((computesInTime_iff _ _ _ _).mp (hL (w.drop s.length))).2
      simpa only [hout, v] using L.tm.output_length_le (w.drop s.length)
        (d * ((w.drop s.length).length + 1))
    obtain ⟨a, ha, hap, haf, har⟩ := hC w s
    obtain ⟨b, hb, hbp, hbf, hbr⟩ := hD w (w.drop s.length)
    obtain ⟨t, htpos, ht, hfirst, hr⟩ := emitterP2_body_round f C D hk hl ce cx de dx
      w s a b hap hbp haf har hbf hbr
    refine ⟨t, htpos, ?_, hfirst, hr⟩
    have hHs : s.length ≤ H := by dsimp [H]; omega
    have hHn : w.length ≤ H := by dsimp [H]; omega
    have hHu : u.length ≤ H := by dsimp [u, H]; omega
    have hHfive : 10 ≤ 5 * H := by dsimp [H]; omega
    have hLd : d * ((w.drop s.length).length + 1) ≤ d * H :=
      Nat.mul_le_mul_left d (by dsimp [H]; omega)
    have hHv : v.length ≤ d * H := hv.trans hLd
    have hCa : TE s.length + s.length + u.length + 1 ≤ 2 * H := by
      dsimp [u, H]; omega
    have hCa' : a ≤ (2 * cC) * H := by
      calc
        a ≤ cC * (TE s.length + s.length + u.length + 1) := ha
        _ ≤ cC * (2 * H) := Nat.mul_le_mul_left _ hCa
        _ = (2 * cC) * H := by ring
    have hDb : d * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1 ≤
        (2 * d + 1) * H := by
      calc
        _ ≤ 2 * (d * H) + H := by dsimp [H] at *; omega
        _ = (2 * d + 1) * H := by ring
    have hDb' : b ≤ (cD * (2 * d + 1)) * H := by
      calc
        b ≤ cD * (d * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1) := hb
        _ ≤ cD * ((2 * d + 1) * H) := Nat.mul_le_mul_left _ hDb
        _ = (cD * (2 * d + 1)) * H := by ring
    have hsum : s.length + w.length + u.length + v.length + 10 ≤ (d + 8) * H := by
      rw [Nat.add_mul]
      omega
    calc
      t ≤ a + b + 10 * (s.length + w.length + u.length + v.length + 10) := ht
      _ ≤ (2 * cC) * H + (cD * (2 * d + 1)) * H + 10 * ((d + 8) * H) :=
        Nat.add_le_add (Nat.add_le_add hCa' hDb') (Nat.mul_le_mul_left _ hsum)
      _ = A * (TE (w.length + 1) + w.length + 2) := by dsimp [A, H]; ring

/-- **E4′, width-parametric split search** (design
§11; customers: 3A-cont's exponential padding equation — whose bespoke
body is this contract's harvest template — and every later padding
argument, including the ch3 hierarchy theorems). The generalization of
`Turing.FinTM.computesFunInTime_splitSolve` from the hardwired polynomial
family to a hypothesis-supplied width evaluator: given a machine `E`
computing the binary representation of `f` of the input length within a
monotone budget `TE`, a machine solving `i + f i = n` by first-success
search, emitting the threaded split of the original input, and `[]` on
exhaustion, inside the loopFind envelope over `TE`. At
`f = fun i => C * (i + 1) ^ e` the computed function definitionally
recovers the catalog split's.

**Construction sketch.** The `exists_loopFindTM` engine with candidate
word as loop state: per round, run `E` on the prepared candidate prefix
with captured output (charging `TE` before any validity check), compare
whole canonical binary words against the suffix length, restore scratch,
advance by one; the one-past-end candidate takes a positive silent
stall. 3A-cont's displayed body contracts are exactly this round
discipline. -/
theorem computesFunInTime_splitSolveWith (f : ℕ → ℕ) (E : FinTM Bool)
    (TE : ℕ → ℕ) (hTE : Monotone TE)
    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplitWith f w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) * (TE (n + 1) + n + 2) := by
  exact emitterP2_closed f E TE hTE hE

/-- Double token bits in states zero, one, and two; after a false token
delimiter, emit the pair separator in states three and four, then copy the
remainder in state five. A right blank in state zero starts the separator
directly, so an unterminated token and the empty input are both retained. -/
private def emitterTokenTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some (if b then 1 else 2)⟩
          | none => ⟨0, fun j => j.elim0, some false, some 4⟩
        | 1 => ⟨.pos, fun j => j.elim0, some true, some 0⟩
        | 2 => ⟨.pos, fun j => j.elim0, some false, some 3⟩
        | 3 => ⟨0, fun j => j.elim0, some false, some 4⟩
        | 4 => ⟨0, fun j => j.elim0, some true, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 5⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Two token transitions double the next bit and advance the input once;
only a false bit ends token scanning. -/
private lemma emitterToken_double (x pre rest out : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    emitterTokenTM.tm.runFrom
      (scanCfg x (some (0 : Fin 6)) pre.length (by simp [hx]) out) 2 =
      scanCfg x (some (if b then (0 : Fin 6) else 3)) (pre ++ [b]).length
        (by simp [hx]) (out ++ [b, b]) := by
  have hlen : pre.length < x.length := by simp [hx]
  have hread : x[pre.length]? = some b := by simp [hx]
  have hfirst : emitterTokenTM.tm.step
      (scanCfg x (some (0 : Fin 6)) pre.length (by omega) out) =
      scanCfg x (some (if b then (1 : Fin 6) else 2)) pre.length (by omega)
        (out ++ [b]) := by
    unfold MultiTapeTM.step
    change (emitterTokenTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    rw [scanCfg_read, hread]
    apply Cfg.ext_zero_tapes <;> simp [emitterTokenTM, Action.apply, scanCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hfirst]
  cases b <;>
    apply Cfg.ext_zero_tapes
  all_goals first
    | rfl
    | simpa [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg] using
        moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
    | simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]

/-- The two separator transitions preserve the input position and append the
unique pair delimiter before entering the suffix copier. -/
private lemma emitterToken_separator (x out : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    emitterTokenTM.tm.runFrom (scanCfg x (some (3 : Fin 6)) i hi out) 2 =
      scanCfg x (some (5 : Fin 6)) i hi (out ++ [false, true]) := by
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]

/-- The streaming token encoder emits the exact recursive split, after any
already-consumed prefix. Its time is twice the token length plus the remainder
length plus three, including the final blank-reading halt.
**Proof sketch.** Induct on the unconsumed input. At the right blank emit just
the separator. A false bit is doubled and terminates the token, so emit the
separator and copy the suffix. A true bit is doubled and the induction
hypothesis processes the remaining token. No standalone marker is consumed. -/
private lemma emitterToken_run (x rest : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
      emitterTokenTM.tm.runFrom
        (scanCfg x (some (0 : Fin 6)) pre.length (by simp [hx]) out)
        (2 * (unaryTokenSplit rest).1.length + (unaryTokenSplit rest).2.length + 3) =
        scanCfg x none x.length (by omega)
          (out ++ pairEncode (unaryTokenSplit rest).1 (unaryTokenSplit rest).2) := by
  induction rest with
  | nil =>
    intro pre out hx
    have hlen : pre.length = x.length := by simp [hx]
    have hread : x[pre.length]? = none := by simp [hlen]
    simp only [unaryTokenSplit, List.length_nil, Nat.mul_zero, Nat.zero_add]
    have hfirst : emitterTokenTM.tm.step
        (scanCfg x (some (0 : Fin 6)) pre.length (by omega) out) =
        scanCfg x (some (4 : Fin 6)) pre.length (by omega) (out ++ [false]) := by
      unfold MultiTapeTM.step
      change (emitterTokenTM.tm.tr (0 : Fin 6) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes <;> simp [emitterTokenTM, Action.apply, scanCfg]
    have hsecond : emitterTokenTM.tm.step
        (scanCfg x (some (4 : Fin 6)) pre.length (by omega) (out ++ [false])) =
        scanCfg x (some (5 : Fin 6)) pre.length (by omega) (out ++ [false, true]) := by
      apply Cfg.ext_zero_tapes <;>
        simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]
    rw [show 3 = (0 + 1) + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hfirst, hsecond]
    unfold MultiTapeTM.step
    change (emitterTokenTM.tm.tr (5 : Fin 6) _ _).apply _ = _
    rw [scanCfg_read, hread]
    apply Cfg.ext_zero_tapes <;>
      simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, List.append_assoc, hlen]
  | cons b rest ih =>
    intro pre out hx
    cases b with
    | false =>
      simp only [unaryTokenSplit, List.length_cons, List.length_nil]
      rw [show 2 * (0 + 1) + rest.length + 3 = 2 + (2 + (rest.length + 1)) by omega,
        MultiTapeTM.runFrom_add, emitterToken_double x pre rest out false hx]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [MultiTapeTM.runFrom_add, emitterToken_separator]
      have he := scanCopy_suffix emitterTokenTM.tm (5 : Fin 6) (fun _ _ => rfl)
        x rest (pre ++ [false]) ((out ++ [false, false]) ++ [false, true])
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
      simpa [pairEncode, List.append_assoc] using he
    | true =>
      simp only [unaryTokenSplit, List.length_cons]
      rw [show 2 * ((unaryTokenSplit rest).1.length + 1) +
          (unaryTokenSplit rest).2.length + 3 =
          2 + (2 * (unaryTokenSplit rest).1.length + (unaryTokenSplit rest).2.length + 3)
          by omega,
        MultiTapeTM.runFrom_add, emitterToken_double x pre rest out true hx]
      simp only [↓reduceIte]
      have he := ih (pre ++ [true]) (out ++ [true, true])
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
      simpa [pairEncode, List.append_assoc] using he

/-- Token and remainder partition every input, including empty and
unterminated tokens, so their lengths sum to the original length. -/
private lemma emitterToken_length (x : List Bool) :
    (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp_all [unaryTokenSplit] <;> omega

/-- **P16, the unary token step** (design §11;
customers: 3B-cont's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner — the fourth re-derivation of this atom
otherwise, after 2D's parsers, 3B's `satScanTM`, and 3D's six-state
scan). Split off the leading unary token (`Turing.unaryTokenSplit`) as a
self-delimiting pair, in linear time.

**Construction sketch.** One left-to-right scan emitting the token bits
as read, the delimiter, the pair framing, and the remainder — the proved
scanner stages of the 3B and 3D deliveries are the harvest sources. -/
theorem computesFunInTime_unaryToken :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
        fun n => c * (n + 1) := by
  refine ⟨emitterTokenTM, 3, fun x => ?_⟩
  have hr := emitterToken_run x x [] [] rfl
  have hc : emitterTokenTM.ComputesInTime x
      (pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
      (2 * (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length + 3) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    have hinit : emitterTokenTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 6)) 0 (by omega) [] := by
      apply Cfg.ext_zero_tapes <;> simp [emitterTokenTM, scanCfg]
    rw [hinit]
    constructor
    · simpa only [List.length_nil, scanCfg] using congrArg Cfg.state hr
    · simpa only [List.length_nil, List.nil_append, scanCfg] using congrArg Cfg.output hr
  apply hc.mono
  change 2 * (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length + 3 ≤
    3 * (x.length + 1)
  have hl := emitterToken_length x
  omega

/-- Copy each input bit, then append the fixed bit on the right-blank
halting transition. The machine has no work tapes. -/
private def emitterAppendTM (b : Bool) : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ => match inp with
        | some a => ⟨.pos, fun j => j.elim0, some a, some ()⟩
        | none => ⟨0, fun j => j.elim0, some b, none⟩ }

/-- Before the right blank, exactly the scanned prefix has been emitted.
**Proof sketch.** Induct over the input positions. Every nonblank transition
copies its bit and advances once; the emitting halt is still ahead. -/
private lemma emitterAppend_run (b : Bool) (x : List Bool) :
    ∀ j (hj : j ≤ x.length),
      (emitterAppendTM b).tm.runFrom ((emitterAppendTM b).tm.initCfg x) j =
        scanCfg x (some ()) j hj (x.take j) := by
  intro j
  induction j with
  | zero =>
    intro hj
    apply Cfg.ext_zero_tapes <;> simp [scanCfg, emitterAppendTM]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change ((emitterAppendTM b).tm.tr ()
      (scanCfg x (some ()) j (by omega) (x.take j)).inputSymbol _).apply _ = _
    rw [scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · simp only [emitterAppendTM, Action.apply, scanCfg, Option.toList_some,
        List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length)]

/-- **P18′, append one bit** (design §11, narrowed at
spec time from the drafted accumulator row: cross-round persistence is the
loop engine's state-word mechanism, so the catalog atom is just the
append; customers: fresh-variable counters in 3B-cont and 4A, via the
loop state word). Append a single fixed bit to the input word, in linear
time.

**Construction sketch.** Copy the input verbatim, emit `b`, halt — P1's
copier with one extra emission on the halting transition. -/
theorem computesFunInTime_appendBit (b : Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => x ++ [b]) fun n => c * (n + 1) := by
  refine ⟨emitterAppendTM b, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  simp only [one_mul]
  rw [MultiTapeTM.runFrom_succ_eq_step', emitterAppend_run b x x.length (by omega)]
  unfold MultiTapeTM.step
  change let d := ((emitterAppendTM b).tm.tr ()
    (scanCfg x (some ()) x.length (by omega) (x.take x.length)).inputSymbol _).apply _
    d.Halted ∧ d.output = x ++ [b]
  rw [scanCfg_read]
  simp [emitterAppendTM, scanCfg, Action.apply, Cfg.Halted]

end Turing.FinTM
