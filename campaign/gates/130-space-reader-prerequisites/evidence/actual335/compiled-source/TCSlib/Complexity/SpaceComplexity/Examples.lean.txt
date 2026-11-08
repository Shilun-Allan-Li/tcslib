/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace examples: the parity language

[AB09, Example 4.7]: `EVEN = {x : x has an even number of 1s}` is in `L`. (The
example's second language, `MULT`, needs the campaign's number-triple encoding
conventions and is scheduled with the logspace-reduction phase — phase P4.4 of
`AroraBarakChapters3-4Plan.md` — rather than here.) A worked ARM-compiled
example of a `LOGSPACE` membership already exists in the received surface
(`Complexity.dblLang_mem`, `TCSlib.Complexity.SpaceComplexity.Machines.DblLang`);
parity is the book's own first example and gets the direct statement.

## Main definitions

* `Complexity.evenLang` — the even-parity language. [AB09, Example 4.7]
* `Complexity.evenScanTM` — the zero-work-tape parity scanner. [AB09, Example 4.7]

## Main results

* `Complexity.evenScanTM_decidesInTime` — the scanner decides parity within
  `n + 1` steps. [AB09, Example 4.7]
* `Complexity.evenLang_mem_LOGSPACE` — parity is decidable in logarithmic
  space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The parity language** `EVEN`: binary strings containing an even number of
`1`s (rendered as `true`s). [AB09, Example 4.7] -/
def evenLang : Language Bool :=
  {x | x.count true % 2 = 0}

/-- The parity scanner uses no work tapes and two live states: `true` means
that the consumed prefix has even parity. It toggles on `true`, keeps its
state on `false`, and emits its state and halts at the right blank.
[AB09, Example 4.7]

The missing catalog row is a finite-state scanner with a final verdict:
`transducer_run` halts silently, so its contract cannot emit this bit. -/
def evenScanTM : FinTM Bool where
  k := 0
  State := Bool
  tm :=
    { q₀ := true
      tr := fun q inp _ => match inp with
        | some b => FinTM.controlAction .pos (some (if b then !q else q))
        | none => ⟨0, fun i => i.elim0, some q, none⟩ }

/-- After consuming a prefix, the scanner stores its even-parity bit, points
to the next input position, and has emitted nothing.

**Proof sketch.** Induct on the prefix length. The initial state records
zero true bits. Reading the next bit preserves or toggles parity, advances
the head once, and emits nothing. The prefix-count update is the count of
an appended singleton; residues modulo two justify the toggle. -/
private theorem evenScanTM_prefix (x : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    (evenScanTM.tm.runFrom (evenScanTM.tm.initCfg x) j).state =
        some (decide ((x.take j).count true % 2 = 0)) ∧
      (evenScanTM.tm.runFrom (evenScanTM.tm.initCfg x) j).inputPos.val = j + 1 ∧
      (evenScanTM.tm.runFrom (evenScanTM.tm.initCfg x) j).output = [] := by
  induction j with
  | zero => simp [evenScanTM]
  | succ j ih =>
    obtain ⟨hq, hp, ho⟩ := ih (by omega)
    have hlt : j < x.length := by omega
    have hs := FinTM.inputSymbol_at
      (evenScanTM.tm.runFrom (evenScanTM.tm.initCfg x) j) j (by omega) hp
    rw [List.getElem?_eq_getElem hlt] at hs
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hq]
    simp only [evenScanTM, hs, FinTM.controlAction, Action.apply]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.take_succ_eq_append_getElem hlt, List.count_append]
      cases x[j] with
      | false => simp
      | true =>
        have hm := Nat.mod_lt ((x.take j).count true) (by decide : 0 < 2)
        by_cases he : (x.take j).count true % 2 = 0
        · simp [Nat.add_mod, he]
        · have he' : (x.take j).count true % 2 = 1 := by omega
          simp [Nat.add_mod, he']
    · rw [moveInputPos_pos_of_ne_right _ (by omega)]
      simpa using hp
    · simpa using ho

/-- The zero-work-tape scanner decides the even-parity language within
`n + 1` steps on every input of length `n`. [AB09, Example 4.7]

**Proof sketch.** Apply the prefix invariant to the whole input. The next
symbol is the right blank, so one more transition emits the even-parity
indicator and halts. This includes the empty input. -/
theorem evenScanTM_decidesInTime :
    evenScanTM.DecidesInTime evenLang fun n => n + 1 := by
  intro x
  obtain ⟨hq, hp, ho⟩ := evenScanTM_prefix x x.length le_rfl
  have hs := FinTM.inputSymbol_at
    (evenScanTM.tm.runFrom (evenScanTM.tm.initCfg x) x.length) x.length le_rfl hp
  simp only [List.getElem?_length] at hs
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hq, hs]
  simp only [evenScanTM, Action.apply]
  rw [ho]
  simp [MultiTapeTM.indicator, evenLang]

/-- **Parity is decidable in logarithmic space** — in fact in constant space,
which the `c · logSpace n` budget absorbs since `logSpace n ≥ 1`.
[AB09, Example 4.7]

**Proof sketch.** A direct `Turing.FinTM` with the running parity in control:
either the two-state **zero-work-tape** scanner (space `0`, the round-2 P0
witness construction — `Complexity.exists_zeroTape_parity_decider` in
`SpaceComplexity/ZeroSpace.lean` states exactly this machine, and that file
imports this one, so this proof must be **direct rather than derived from it**:
the reverse dependency would be an import cycle, P4.1 round 1, finding 4) or
the one-work-tape variant (one visited cell); either is within
`1 ≤ 1 · logSpace n`. Correctness is the left-to-right scan invariant —
parity of the consumed prefix — with the final emission
`[Turing.MultiTapeTM.indicator evenLang x]` at the input boundary, halting at
time `n + O(1)`. -/
theorem evenLang_mem_LOGSPACE : evenLang ∈ LOGSPACE := by
  refine ⟨0, evenScanTM, ?_⟩
  refine (FinTM.computesInSpace_zero_of_k_eq_zero (M := evenScanTM) rfl ?_).mono
    (fun _ => Nat.zero_le _)
  intro x
  exact ⟨x.length + 1, evenScanTM_decidesInTime x⟩

end Complexity
