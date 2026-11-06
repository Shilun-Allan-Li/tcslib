/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time pairing, projections and branching

Closure facts for the function class FP (`Complexity.PolyTimeComputable`, implicit
throughout [AB09, ch. 2]) needed when a reduction must keep its input while computing
from it: constant functions, the threaded payload map, pairing of two polynomial-time
functions through `Turing.pairEncode`, the total pair projections, concatenation,
Boolean branching and length tests, and the unary length maps `x ↦ 1^|x|` and
`x ↦ 1^{C(|x|+1)^d}` (the input of a uniformity machine, [AB09, Def 6.12]). All are
assembled from the proved machine catalog of
`TCSlib.Complexity.TuringMachine.Build.Primitives`. The closure facts for the class `P`
built on them are in `TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.pairMapSnd` — on `pairEncode a b`, output `pairEncode a (g b)`; malformed
  words go to `[]`.
* `Complexity.pairFstD`, `Complexity.pairSndD` — total pair projections (`[]` on
  malformed words).

## Main results

* `Complexity.polyTimeComputable_of_linear` — a linear-time machine contract gives a
  polynomial-time computable function.
* `Complexity.polyTimeComputable_const` — constant functions are polynomial-time.
* `Complexity.PolyTimeComputable.pairMapSnd` — the threaded payload map preserves
  polynomial time.
* `Complexity.PolyTimeComputable.pairEncode` — `x ↦ pairEncode (f x) (g x)` is
  polynomial-time when `f` and `g` are.
* `Complexity.polyTimeComputable_unary` — `x ↦ 1^|x|` is polynomial-time;
  `Complexity.polyTimeComputable_polyUnary` — so is `x ↦ 1^{C(|x|+1)^d}`.
* `Complexity.PolyTimeComputable.append` — FP is closed under concatenation.
* `Complexity.polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`,
  `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`,
  `polyTimeComputable_prepend` — projections and rearrangements of pairs.
* `Complexity.polyTimeComputable_ite`, `polyTimeComputable_and` — Boolean branching.
* `Complexity.polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` — length tests on
  pairs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2; §6.2, Definition 6.12.)
-/

namespace Complexity

open Turing

/-- A function computed by a finite binary machine within a linear bound `a · (n + 1)`
is polynomial-time computable. -/
theorem polyTimeComputable_of_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))) :
    PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Every constant function `fun _ => w` is polynomial-time computable. -/
theorem polyTimeComputable_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_const w)

/-- The threaded payload map of `g`: on a pair `pairEncode a b` it outputs
`pairEncode a (g b)` (the first component is carried unchanged), and on a word that is
not a pair it outputs `[]`. -/
def pairMapSnd (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- On a pair, the threaded payload map transforms the second component. -/
@[simp]
theorem pairMapSnd_pairEncode (g : List Bool → List Bool) (a b : List Bool) :
    pairMapSnd g (pairEncode a b) = pairEncode a (g b) := by
  simp [pairMapSnd, pairDecode_pairEncode]

/-- If `g` is polynomial-time computable, so is its threaded payload map
`Complexity.pairMapSnd g`.

**Proof sketch.** `Turing.FinTM.computesFunInTime_pairMapSnd` with the monotone
majorant `C (n+1)^c` of `g`'s bound gives a budget `K (n + 1 + C (n+1)^c)`, which is at
most `K (C + 1) (n+1)^(c+1)`. -/
theorem PolyTimeComputable.pairMapSnd {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (Complexity.pairMapSnd g) := by
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by
      intro m n h
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) c))
  refine ⟨M, K * (C + 1), c + 1, fun x => (hM x).mono ?_⟩
  have hn : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ c + 1 by omega)
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ c))
  calc
    _ ≤ K * ((x.length + 1) ^ (c + 1) + C * (x.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left K (Nat.add_le_add hn hc)
    _ = _ := by ring

/-- Appending to a pair appends to its second component. -/
private lemma pairEncode_append (a b c : List Bool) :
    pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- **Pairing two polynomial-time functions is polynomial-time**: if `f` and `g` are
polynomial-time computable, so is `x ↦ pairEncode (f x) (g x)`.

**Proof sketch.** Only the second component of a pair can be transformed in place
(`Complexity.pairMapSnd`), so the first component is built with an empty payload and
then retained. Duplicating `x` (`Turing.FinTM.computesFunInTime_pairDup`) and mapping
the payload gives `H x = pairEncode (f x) []`; duplicating `x` and mapping `H` gives
`s x = pairEncode x (H x)`; duplicating `s x` and mapping `g ∘ fst` gives
`t x = pairEncode (s x) (g x)`. Concatenating the components of `t x`
(`Turing.FinTM.computesFunInTime_pairConcat`) yields
`pairEncode x (pairEncode (f x) (g x))`, whose second component is the result. -/
theorem PolyTimeComputable.pairEncode {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => Turing.pairEncode (f x) (g x)) := by
  have hd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup
  have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  -- `H x = pairEncode (f x) []`, `s x = pairEncode x (H x)`, `t x = pairEncode (s x) (g x)`
  have hH := (((polyTimeComputable_const []).pairMapSnd).comp hd).comp hf
  have hS := hH.pairMapSnd.comp hd
  have hT := ((hg.comp hp).pairMapSnd.comp hd).comp hS
  -- concatenate, then project the second component
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairMapSnd_pairEncode, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  rw [pairEncode_append, pairEncode_append]
  simp [pairDecode_pairEncode]

/-- The last `true` of `1^(n+1)` is its last letter: stripping it leaves `1ⁿ`. -/
private lemma splitAtLastTrue_replicate_succ (n : ℕ) :
    splitAtLastTrue (List.replicate (n + 1) true) = some (List.replicate n true) := by
  rw [splitAtLastTrue, List.reverse_replicate, List.replicate_succ]
  simp [List.reverse_replicate]

/-- **The unary length map is polynomial-time**: `x ↦ 1^|x|` is polynomial-time
computable. (This is how the input `1ⁿ` of a uniformity machine [AB09, Def 6.12] is
produced from an input of length `n`.)

**Proof sketch.** Pair `x` with `1^(|x|+1)` (the unary polynomial generator at
`1 · (n + 1)¹`, `Turing.FinTM.computesFunInTime_polyUnary`), strip the last `true` of the
second component (`Turing.FinTM.computesFunInTime_stripLast`), and project the second
component (`Turing.FinTM.computesFunInTime_pairSnd`). -/
theorem polyTimeComputable_unary :
    PolyTimeComputable (fun x => List.replicate x.length true) := by
  have hu : PolyTimeComputable (fun x => List.replicate (1 * (x.length + 1) ^ 1) true) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyUnary 1 1
    exact ⟨M, c, 2, hM⟩
  have hpair := polyTimeComputable_id.pairEncode hu
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (a, v) =>
        match splitAtLastTrue v with
        | some u => Turing.pairEncode a u
        | none => []
      | none => []) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  convert hs.comp (hstrip.comp hpair) using 1
  funext x
  simp only [Function.comp_apply, id, pairDecode_pairEncode, Nat.pow_one, Nat.one_mul,
    splitAtLastTrue_replicate_succ, Option.map_some, Option.getD_some]

/-- **FP is closed under concatenation**: if `f` and `g` are polynomial-time computable,
so is `x ↦ f x ++ g x`. (Pair the two results, `PolyTimeComputable.pairEncode`, then
concatenate the components, `Turing.FinTM.computesFunInTime_pairConcat`.) -/
theorem PolyTimeComputable.append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert hc.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- `x ↦ 1^{C (|x| + 1)^d}` is polynomial-time computable. -/
theorem polyTimeComputable_polyUnary (C d : ℕ) :
    PolyTimeComputable fun x => List.replicate (C * (x.length + 1) ^ d) true := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C d
  exact ⟨M, a, d + 1, hM⟩

/-- Prepending a fixed word is polynomial-time. -/
theorem polyTimeComputable_prepend (w : List Bool) : PolyTimeComputable (fun x => w ++ x) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend w)

/-! ### Total pair projections -/

/-- The total first projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairFstD (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- The total second projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairSndD (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The defining equation of `pairFstD`: `pairFstD z = ((pairDecode z).map Prod.fst).getD []`. -/
theorem pairFstD_eq (z : List Bool) : pairFstD z = ((pairDecode z).map Prod.fst).getD [] := rfl

/-- The defining equation of `pairSndD`: `pairSndD z = ((pairDecode z).map Prod.snd).getD []`. -/
theorem pairSndD_eq (z : List Bool) : pairSndD z = ((pairDecode z).map Prod.snd).getD [] := rfl

/-- On a word that is not a pair the first projection is empty:
`pairDecode z = none → pairFstD z = []`. -/
theorem pairFstD_of_pairDecode_eq_none {z : List Bool} (h : pairDecode z = none) :
    pairFstD z = [] := by
  rw [pairFstD_eq, h]
  rfl

/-- On a word that is not a pair the second projection is empty:
`pairDecode z = none → pairSndD z = []`. -/
theorem pairSndD_of_pairDecode_eq_none {z : List Bool} (h : pairDecode z = none) :
    pairSndD z = [] := by
  rw [pairSndD_eq, h]
  rfl

/-- The first projection of a pair is its first component. -/
@[simp] theorem pairFstD_pairEncode (a b : List Bool) : pairFstD (pairEncode a b) = a := by
  simp [pairFstD, pairDecode_pairEncode]

/-- The second projection of a pair is its second component. -/
@[simp] theorem pairSndD_pairEncode (a b : List Bool) : pairSndD (pairEncode a b) = b := by
  simp [pairSndD, pairDecode_pairEncode]

/-- The first projection of a word is no longer than the word. -/
theorem length_pairFstD_le (z : List Bool) : (pairFstD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := Turing.eq_pairEncode_of_pairDecode z a b h
    subst hz
    simp [length_pairEncode]
    omega

/-- The first projection is polynomial-time computable. -/
theorem polyTimeComputable_pairFstD : PolyTimeComputable pairFstD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst

/-- The second projection is polynomial-time computable. -/
theorem polyTimeComputable_pairSndD : PolyTimeComputable pairSndD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd

/-- Iterated first projections (the root of a nested tuple) are polynomial-time. -/
theorem polyTimeComputable_iterate_pairFstD (n : ℕ) : PolyTimeComputable (pairFstD^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact polyTimeComputable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact polyTimeComputable_pairFstD.comp ih

/-- Concatenating the two components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairConcat :
    PolyTimeComputable (fun z => pairFstD z ++ pairSndD z) := by
  have h := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p => cases p; simp [pairFstD, pairSndD, hz]

/-- Swapping the components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairSwap :
    PolyTimeComputable (fun z => pairEncode (pairSndD z) (pairFstD z)) :=
  polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD

/-! ### Branching and length tests -/

/-- **Polynomial-time branching**: if the test `p` (as a one-bit output) and both branches
are polynomial-time computable, so is `x ↦ if p x then f x else g x`.

**Proof sketch.** The timed branch contract `Turing.FinTM.computesFunInTime_cond` runs
the test, then the selected branch; enlarge the three degrees to their maximum and
absorb the constants. -/
theorem polyTimeComputable_ite {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨D, A, a, hD⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hD hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have hpow (d : ℕ) (hd : d ≤ e) : (x.length + 1) ^ d ≤ (x.length + 1) ^ e :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hd
  have ha := Nat.mul_le_mul_left A (hpow a (Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B (hpow b
    ((Nat.le_max_left b c).trans (Nat.le_max_right a (max b c))))
  have hc := Nat.mul_le_mul_left C (hpow c
    ((Nat.le_max_right b c).trans (Nat.le_max_right a (max b c))))
  have hbc : max (B * (x.length + 1) ^ b) (C * (x.length + 1) ^ c) ≤
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e :=
    max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Polynomial-time Boolean conjunction of two one-bit tests. -/
theorem polyTimeComputable_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  convert polyTimeComputable_ite hp hq (polyTimeComputable_const [false]) using 1
  funext x
  cases p x <;> rfl

/-- The length test `|snd z| ≤ |fst z|` on pairs is polynomial-time.

**Proof sketch.** The catalog's threaded length check at `(C, e) = (1, 1)` decides
`|b| ≤ |a| + 1` on `⟨a, b⟩`; apply it to `⟨fst z, 1 :: snd z⟩`. -/
theorem polyTimeComputable_lenLe :
    PolyTimeComputable (fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) := by
  have hchk : PolyTimeComputable (fun x => [match pairDecode x with
      | some (a, b) => decide (b.length ≤ 1 * (a.length + 1) ^ 1)
      | none => false]) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck 1 1
    exact ⟨M, a, 2, hM⟩
  have hpair : PolyTimeComputable (fun z => pairEncode (pairFstD z) (true :: pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_prepend [true]).comp polyTimeComputable_pairSndD)
  convert hchk.comp hpair using 1
  funext z
  simp [pairDecode_pairEncode]

/-- The length-equality test `|fst z| = |snd z|` on pairs is polynomial-time. -/
theorem polyTimeComputable_lenEq :
    PolyTimeComputable (fun z => [decide ((pairFstD z).length = (pairSndD z).length)]) := by
  have h := polyTimeComputable_and polyTimeComputable_lenLe
    (polyTimeComputable_lenLe.comp polyTimeComputable_pairSwap)
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  congr 1
  by_cases h1 : (pairFstD z).length = (pairSndD z).length
  · simp [h1]
  · rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
    · simp [h1, Nat.not_le_of_lt h2]
    · simp [h1, Nat.not_le_of_lt h2]

end Complexity


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/workF/TCSlib_Complexity_ClassNP_PolyTimePairing.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
