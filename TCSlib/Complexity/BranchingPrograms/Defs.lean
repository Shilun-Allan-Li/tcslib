/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Bounded-width branching programs

The general branching-program model of [Bar89, §1]: an instruction reads one input bit and
produces a map `[w] → [w]`; a width-`w` program is a finite sequence of instructions, and it
*yields* on an input the composition of the maps its instructions produce.  A family of programs
recognizes a language through accepting sets `F_n` of maps.  Permutation programs (every map a
bijection) are the predicate `IsPermutation`.

## Main definitions

* `BranchingProgram.Instr` — an instruction `⟨var, map0, map1⟩` (BV14's order: `map0` when the
  bit is `0`), with `Instr.eval`, `Instr.IsPermutation` and `Instr.ofPerm`.
* `BranchingProgram` — a width-`w` program on `n` inputs (registered model); `length`, `append`
  (the `++` notation), `yield`, `IsPermutation`, `conj` (Lemma 1's conjugation) and
  `complementLast` (Lemma 2's change of the last instruction).
* `BranchingProgramFamily` — a family with accepting sets (registered model); `language`,
  `IsPolyLength`, `IsPermutation`.
* `Language.InBWBP`, `Language.InPBP` — the classes BWBP and `PBP_w` (polynomial length).

## Main results

All are statements of the 6a statement phase (targets admitted with `sorry`), except the readers.

* `BranchingProgram.yield_append`, `yield_nil` — the yield composes in program order (C1).
* `BranchingProgram.yield_conj`, `length_conj`, `length_append` — conjugation (C2).
* `BranchingProgram.yield_complementLast`, `length_complementLast` — Lemma 2's step (C3).
* `BranchingProgram.isPermutation_iff` (proved) and the closure lemmas of permutation
  programs, `IsPermutation.bijective_yield` (C4).

## Conventions and deviations

* **Instruction order.** [Bar89, §1] writes `⟨j, f, g⟩` with `f` used when `x_j = 1`; the fields
  here follow [BV14, §3.3]'s `(var(t), σ_{t,0}, σ_{t,1})`: `map0` is used when the bit is `0`.
* **Program order.** [Bar89] writes products left to right (the leftmost map acts first).  The
  model composes in program order: `(B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x`.  In Mathlib's
  `Equiv.Perm` product (right factor first) Bar89's word `σ₁σ₂σ₁⁻¹σ₂⁻¹` is
  `σ₂⁻¹ * σ₁⁻¹ * σ₂ * σ₁`.
* **Recognition** is by accepting sets, as in [Bar89, §1]: `x ∈ L ↔ B(x) ∈ F_n`.

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-based FHE as secure as PKE*, ITCS 2014,
  pp. 1–12; IACR ePrint 2013/541.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- An instruction `⟨var, map0, map1⟩` of width `w` over `n` inputs: read input `var`; apply
`map0 : [w] → [w]` if it is `0` and `map1` if it is `1` [Bar89, §1, p001-b002].
Deviation: Bar89 lists the `x_j = 1` map first; the fields follow BV14's
`(var(t), σ_{t,0}, σ_{t,1})` [BV14, §3.3, p013-b002]. -/
structure BranchingProgram.Instr (w n : ℕ) where
  /-- The input bit the instruction reads. -/
  var : Fin n
  /-- The map produced when the bit is `0`. -/
  map0 : Fin w → Fin w
  /-- The map produced when the bit is `1`. -/
  map1 : Fin w → Fin w

/-- A width-`w` branching program on `n` inputs: a finite sequence of instructions
`instrs = [ι₁, …, ι_l]` [Bar89, §1, p001-b002].  Registered model
(`TCSlib/ComputationalModels.lean`). -/
structure BranchingProgram (w n : ℕ) where
  /-- The instructions, in program order. -/
  instrs : List (BranchingProgram.Instr w n)

namespace BranchingProgram

variable {w n : ℕ}

/-! ### Instructions -/

/-- The map an instruction produces on input `x`: `ι.eval x = if x ι.var then ι.map1 else ι.map0`
[Bar89, §1, p001-b002: "evaluate to `f` if `x_j = 1`, otherwise evaluate to `g`"; BV14 order]. -/
def Instr.eval (ι : Instr w n) (x : Fin n → Bool) : Fin w → Fin w :=
  if x ι.var then ι.map1 else ι.map0

/-- Reader of `Instr.eval`: `ι.eval x = if x ι.var then ι.map1 else ι.map0`. -/
theorem Instr.eval_eq (ι : Instr w n) (x : Fin n → Bool) :
    ι.eval x = if x ι.var then ι.map1 else ι.map0 := rfl

/-- `ι` is a permutation instruction: both of its maps are bijections,
`Function.Bijective ι.map0 ∧ Function.Bijective ι.map1` [Bar89, §1, p002-b001]. -/
def Instr.IsPermutation (ι : Instr w n) : Prop :=
  Function.Bijective ι.map0 ∧ Function.Bijective ι.map1

/-- Reader of `Instr.IsPermutation`:
`ι.IsPermutation ↔ Function.Bijective ι.map0 ∧ Function.Bijective ι.map1`. -/
theorem Instr.isPermutation_iff (ι : Instr w n) :
    ι.IsPermutation ↔ Function.Bijective ι.map0 ∧ Function.Bijective ι.map1 := Iff.rfl

/-- The instruction `⟨i, σ₀, σ₁⟩` with permutation maps: `Instr.ofPerm i σ₀ σ₁` reads input `i`
and produces `σ₀` on `0` and `σ₁` on `1` [Bar89, §1, p002-b001; BV14, §3.3, p013-b002].  Its
field readers are `Instr.ofPerm_var`, `Instr.ofPerm_map0`, `Instr.ofPerm_map1`. -/
@[simps (config := { isSimp := false })]
def Instr.ofPerm (i : Fin n) (σ₀ σ₁ : Equiv.Perm (Fin w)) : Instr w n where
  var := i
  map0 := σ₀
  map1 := σ₁

/-- An instruction built from permutations is a permutation instruction:
`(Instr.ofPerm i σ₀ σ₁).IsPermutation`.  Glue. -/
theorem Instr.isPermutation_ofPerm (i : Fin n) (σ₀ σ₁ : Equiv.Perm (Fin w)) :
    (Instr.ofPerm i σ₀ σ₁ : Instr w n).IsPermutation :=
  ⟨σ₀.bijective, σ₁.bijective⟩

/-! ### Programs -/

/-- The length of a program, its number of instructions: `B.length = B.instrs.length`
[Bar89, §1, p001-b002]. -/
def length (B : BranchingProgram w n) : ℕ :=
  B.instrs.length

/-- Reader of `length`: `B.length = B.instrs.length`. -/
theorem length_eq (B : BranchingProgram w n) : B.length = B.instrs.length := rfl

/-- Concatenation of programs, `B₁.append B₂ = ⟨B₁.instrs ++ B₂.instrs⟩`: run `B₁`, then `B₂`
(Bar89's juxtaposition `B₁B₂`, [Bar89, Thm 1 proof, p004-b002]).  It is the `++` notation. -/
def append (B₁ B₂ : BranchingProgram w n) : BranchingProgram w n :=
  ⟨B₁.instrs ++ B₂.instrs⟩

instance : Append (BranchingProgram w n) := ⟨append⟩

/-- Reader of `append`: `B₁.append B₂ = ⟨B₁.instrs ++ B₂.instrs⟩`. -/
theorem append_eq (B₁ B₂ : BranchingProgram w n) :
    B₁.append B₂ = ⟨B₁.instrs ++ B₂.instrs⟩ := rfl

/-- Reader of the `++` notation: `(B₁ ++ B₂).instrs = B₁.instrs ++ B₂.instrs`. -/
theorem append_instrs (B₁ B₂ : BranchingProgram w n) :
    (B₁ ++ B₂).instrs = B₁.instrs ++ B₂.instrs := rfl

/-- The map `B` yields on `x`: the composition, in program order, of the maps its instructions
produce, `B.yield x = ι_l.eval x ∘ ⋯ ∘ ι₁.eval x`, computed as the left fold
`B.instrs.foldl (fun f ι => ι.eval x ∘ f) id`; `yield ⟨[]⟩ x = id` [Bar89, §1, p001-b002:
"the composition of the functions produced by each of the instructions"].
Deviation: Bar89's products read left to right; here the first instruction acts first. -/
def yield (B : BranchingProgram w n) (x : Fin n → Bool) : Fin w → Fin w :=
  B.instrs.foldl (fun f ι => ι.eval x ∘ f) id

/-- Reader of `yield`: `B.yield x = B.instrs.foldl (fun f ι => ι.eval x ∘ f) id`. -/
theorem yield_eq (B : BranchingProgram w n) (x : Fin n → Bool) :
    B.yield x = B.instrs.foldl (fun f ι => ι.eval x ∘ f) id := rfl

/-- `B` is a permutation branching program: every map of every instruction is a bijection,
`∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1`
[Bar89, §1, p002-b001]. -/
def IsPermutation (B : BranchingProgram w n) : Prop :=
  ∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1

/-- Conjugation of a program by `θ`: every map `f` of every instruction becomes `θ ∘ f ∘ θ⁻¹`,
`B.conj θ = ⟨B.instrs.map fun ι => ⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩⟩`
[Bar89, Lemma 1 proof, p003-b003: "replacing each `σ_i` and `τ_i` by `θσ_iθ⁻¹` and
`θτ_iθ⁻¹`"]. -/
def conj (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) : BranchingProgram w n :=
  ⟨B.instrs.map fun ι => ⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩⟩

/-- Reader of `conj`:
`B.conj θ = ⟨B.instrs.map fun ι => ⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩⟩`. -/
theorem conj_eq (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) :
    B.conj θ = ⟨B.instrs.map fun ι => ⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩⟩ :=
  rfl

/-- Lemma 2's change of the last instruction: the last instruction `⟨i, μ, ν⟩` becomes
`⟨i, σ⁻¹ ∘ μ, σ⁻¹ ∘ ν⟩`, every other instruction is kept, and the empty program is unchanged:
`B.complementLast σ = ⟨B.instrs.dropLast ++ [⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩` when
`ι` is the last instruction [Bar89, Lemma 2 proof, p003-b004: "`⟨i, μσ⁻¹, νσ⁻¹⟩`"].
Deviation: Bar89's `μσ⁻¹` is read left to right (first `μ`, then `σ⁻¹`), so it is the map
`σ⁻¹ ∘ μ` here; the definition is total (Bar89 assumes a last instruction). -/
def complementLast (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w)) :
    BranchingProgram w n :=
  match B.instrs.getLast? with
  | none => B
  | some ι => ⟨B.instrs.dropLast ++ [⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩

/-- Reader of `complementLast`, by cases on the last instruction:
`B.complementLast σ = match B.instrs.getLast? with | none => B | some ι => ⟨B.instrs.dropLast ++
[⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩`. -/
theorem complementLast_eq (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w)) :
    B.complementLast σ = match B.instrs.getLast? with
      | none => B
      | some ι => ⟨B.instrs.dropLast ++ [⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩ := rfl

/-- `complementLast` on the empty program: `(⟨[]⟩ : BranchingProgram w n).complementLast σ =
⟨[]⟩`. -/
theorem complementLast_nil (σ : Equiv.Perm (Fin w)) :
    (⟨[]⟩ : BranchingProgram w n).complementLast σ = ⟨[]⟩ := rfl

/-- `complementLast` on a program with last instruction `ι`:
`(⟨l ++ [ι]⟩ : BranchingProgram w n).complementLast σ =
⟨l ++ [⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩`.  With `complementLast_nil` it covers every
program (`List.eq_nil_or_concat`). -/
theorem complementLast_concat (l : List (Instr w n)) (ι : Instr w n) (σ : Equiv.Perm (Fin w)) :
    (⟨l ++ [ι]⟩ : BranchingProgram w n).complementLast σ =
      ⟨l ++ [⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩]⟩ := by
  rw [complementLast_eq]
  simp only [List.getLast?_concat, List.dropLast_concat]

/-! ### Targets C1–C4 -/

/-- The yield's fold started at a map `g` is the fold started at `id`, composed after `g`:
`l.foldl (fun f ι => ι.eval x ∘ f) g = l.foldl (fun f ι => ι.eval x ∘ f) id ∘ g`.  Glue for C1
(composition is associative); proved by induction on `l` with `g` generalized. -/
private theorem foldl_eval_comp (x : Fin n → Bool) (l : List (Instr w n)) (g : Fin w → Fin w) :
    l.foldl (fun f ι => ι.eval x ∘ f) g = l.foldl (fun f ι => ι.eval x ∘ f) id ∘ g := by
  induction l generalizing g with
  | nil => rfl
  | cons ι l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (ι.eval x ∘ g), ih (ι.eval x ∘ id)]
    rfl

/-- **C1.** The yield of a concatenation composes in program order:
`(B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x` [Bar89, §1, p001-b002: "the composition of the
functions produced by each of the instructions"].
Deviation: Bar89 writes products left to right; in Mathlib's `Equiv.Perm` product (right factor
first) the yield of `B₁B₂` on permutations is `B₂(x) * B₁(x)` (r3 §H3.6).

**Proof sketch.** Rewrite with `append_instrs` and `yield_eq`; `List.foldl_append` turns the left
side into a fold over `B₂.instrs` started at `B₁.yield x`.  An auxiliary induction on a list `l`
shows `l.foldl (fun f ι => ι.eval x ∘ f) g = l.foldl (fun f ι => ι.eval x ∘ f) id ∘ g`
(composition is associative, `Function.comp_assoc`), which with `g = B₁.yield x` closes the goal. -/
theorem yield_append (B₁ B₂ : BranchingProgram w n) (x : Fin n → Bool) :
    (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x := by
  rw [yield_eq, yield_eq B₂, yield_eq B₁, append_instrs, List.foldl_append]
  exact foldl_eval_comp x B₂.instrs _

/-- **C1.** The empty program yields the identity: `(⟨[]⟩ : BranchingProgram w n).yield x = id`
[Bar89, §1, p001-b002].

**Proof sketch.** `yield_eq` and `List.foldl_nil`. -/
theorem yield_nil (x : Fin n → Bool) : (⟨[]⟩ : BranchingProgram w n).yield x = id := by
  rw [yield_eq, List.foldl_nil]

/-- A conjugated instruction produces the conjugated map:
`⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩.eval x = θ ∘ ι.eval x ∘ θ.symm`.  Glue for C2
(split on the bit `x ι.var`). -/
private theorem eval_conjInstr (θ : Equiv.Perm (Fin w)) (ι : Instr w n) (x : Fin n → Bool) :
    (⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩ : Instr w n).eval x =
      θ ∘ ι.eval x ∘ θ.symm := by
  rw [Instr.eval_eq, Instr.eval_eq]
  dsimp only
  cases x ι.var <;> rfl

/-- The yield's fold over the conjugated instructions, started at `θ ∘ g ∘ θ⁻¹`, is the conjugate
of the fold started at `g`: with `c ι = ⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩`,
`(l.map c).foldl (fun f ι => ι.eval x ∘ f) (θ ∘ g ∘ θ.symm) =
θ ∘ l.foldl (fun f ι => ι.eval x ∘ f) g ∘ θ.symm`.  Glue for C2 [Bar89, Lemma 1 proof,
p003-b003]; induction on `l` with `g` generalized, cancelling `θ.symm ∘ θ` at each step. -/
private theorem foldl_conj (θ : Equiv.Perm (Fin w)) (x : Fin n → Bool) (l : List (Instr w n))
    (g : Fin w → Fin w) :
    (l.map fun ι => (⟨ι.var, θ ∘ ι.map0 ∘ θ.symm, θ ∘ ι.map1 ∘ θ.symm⟩ : Instr w n)).foldl
        (fun f ι => ι.eval x ∘ f) (θ ∘ g ∘ θ.symm) =
      θ ∘ l.foldl (fun f ι => ι.eval x ∘ f) g ∘ θ.symm := by
  induction l generalizing g with
  | nil => rfl
  | cons ι l ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [eval_conjInstr, ← ih (ι.eval x ∘ g)]
    congr 1
    funext y
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- **C2.** Conjugating every map by `θ` conjugates the yield:
`(B.conj θ).yield x = θ ∘ B.yield x ∘ θ.symm` [Bar89, Lemma 1 proof, p003-b003].

**Proof sketch.** Rewrite with `conj_eq` and `yield_eq` and induct on `B.instrs` with the fold
generalized to an arbitrary start map `g` (the claim becomes `foldl … (θ ∘ g ∘ θ.symm) =
θ ∘ foldl … g ∘ θ.symm`).  The step uses `Instr.eval_eq`, splits on `x ι.var`, and cancels the
inner `θ.symm ∘ θ` by `Equiv.symm_comp_self`. -/
theorem yield_conj (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) (x : Fin n → Bool) :
    (B.conj θ).yield x = θ ∘ B.yield x ∘ θ.symm := by
  rw [conj_eq, yield_eq, yield_eq]
  have h := foldl_conj θ x B.instrs id
  rw [Function.id_comp, Equiv.self_comp_symm] at h
  exact h

/-- **C2.** Conjugation keeps the length: `(B.conj θ).length = B.length`
[Bar89, Lemma 1, p003-b003: "of the same length as `B`"].

**Proof sketch.** `length_eq`, `conj_eq` and `List.length_map`. -/
theorem length_conj (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) :
    (B.conj θ).length = B.length := by
  simp only [length_eq, conj_eq, List.length_map]

/-- **C2.** Lengths add under concatenation: `(B₁ ++ B₂).length = B₁.length + B₂.length`
[Bar89, Thm 1 proof, p004-b002].

**Proof sketch.** `length_eq`, `append_instrs` and `List.length_append`. -/
theorem length_append (B₁ B₂ : BranchingProgram w n) :
    (B₁ ++ B₂).length = B₁.length + B₂.length := by
  simp only [length_eq, append_instrs, List.length_append]

/-- **C3.** Lemma 2's step post-composes the yield with `σ⁻¹`: for a nonempty program,
`(B.complementLast σ).yield x = σ.symm ∘ B.yield x` [Bar89, Lemma 2 proof, p003-b004:
"`B'(x) = e` if `x ∈ A` and `B'(x) = σ⁻¹` if `x ∉ A`"].
Deviation: Bar89's `B(x)σ⁻¹` is read left to right; in program order it is `σ⁻¹ ∘ B(x)`.

**Proof sketch.** Write `B.instrs = l ++ [ι]` (`List.eq_nil_or_concat`; the empty case contradicts
`hB` through `length_eq`).  Then `complementLast_concat`, `yield_eq` and `List.foldl_append`
reduce both sides to the last step: the new last map is `σ.symm ∘ ι.eval x` by `Instr.eval_eq`
(split on `x ι.var`), and composition is associative. -/
theorem yield_complementLast (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w))
    (hB : 0 < B.length) (x : Fin n → Bool) :
    (B.complementLast σ).yield x = σ.symm ∘ B.yield x := by
  obtain ⟨instrs⟩ := B
  rcases List.eq_nil_or_concat' instrs with rfl | ⟨l, ι, rfl⟩
  · exact absurd hB (Nat.lt_irrefl 0)
  · -- the last step: the new last map is `σ.symm ∘ ι.eval x`
    rw [complementLast_concat, yield_eq, yield_eq]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Instr.eval_eq, Instr.eval_eq]
    dsimp only
    cases x ι.var <;> rfl

/-- **C3.** Lemma 2's step keeps the length: `(B.complementLast σ).length = B.length`
[Bar89, Lemma 2, p003-b004: "in length `l`"].

**Proof sketch.** Cases by `List.eq_nil_or_concat` on `B.instrs`: `complementLast_nil` is the
identity, and `complementLast_concat` replaces one instruction (`List.length_append`). -/
theorem length_complementLast (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w)) :
    (B.complementLast σ).length = B.length := by
  obtain ⟨instrs⟩ := B
  rcases List.eq_nil_or_concat' instrs with rfl | ⟨l, ι, rfl⟩
  · rw [complementLast_nil]
  · simp only [complementLast_concat, length_eq, List.length_append, List.length_singleton]

/-- **C4.** Reader of `IsPermutation` [Bar89, §1, p002-b001]:
`B.IsPermutation ↔ ∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1`.
It is the definition's reader and is proved (`Iff.rfl`). -/
theorem isPermutation_iff (B : BranchingProgram w n) :
    B.IsPermutation ↔ ∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1 :=
  Iff.rfl

/-- **C4.** Permutation programs are closed under concatenation: if `B₁` and `B₂` are permutation
programs, so is `B₁ ++ B₂`.  Glue for [Bar89, Thm 1 proof, p004-b002].

**Proof sketch.** `isPermutation_iff`, `append_instrs` and `List.mem_append`. -/
theorem IsPermutation.append {B₁ B₂ : BranchingProgram w n} (h₁ : B₁.IsPermutation)
    (h₂ : B₂.IsPermutation) : (B₁ ++ B₂).IsPermutation := by
  rw [isPermutation_iff] at h₁ h₂ ⊢
  intro ι hι
  rw [append_instrs, List.mem_append] at hι
  exact hι.elim (h₁ ι) (h₂ ι)

/-- **C4.** Conjugation keeps a permutation program a permutation program:
`B.IsPermutation → (B.conj θ).IsPermutation`.  Glue for [Bar89, Lemma 1 proof, p003-b003].

**Proof sketch.** `isPermutation_iff`, `conj_eq`, `List.mem_map`; each new map `θ ∘ f ∘ θ.symm` is
a composition of bijections (`Function.Bijective.comp`, `Equiv.bijective`). -/
theorem IsPermutation.conj {B : BranchingProgram w n} (h : B.IsPermutation)
    (θ : Equiv.Perm (Fin w)) : (B.conj θ).IsPermutation := by
  rw [isPermutation_iff] at h ⊢
  rw [conj_eq]
  intro ι hι
  simp only [List.mem_map] at hι
  obtain ⟨ι₀, hι₀, rfl⟩ := hι
  exact ⟨θ.bijective.comp ((h ι₀ hι₀).1.comp θ.symm.bijective),
    θ.bijective.comp ((h ι₀ hι₀).2.comp θ.symm.bijective)⟩

/-- **C4.** Lemma 2's step keeps a permutation program a permutation program:
`B.IsPermutation → (B.complementLast σ).IsPermutation`.  Glue for
[Bar89, Lemma 2 proof, p003-b004].

**Proof sketch.** Cases by `List.eq_nil_or_concat`; with `complementLast_concat` the instructions of
`l` are unchanged and the new last maps `σ.symm ∘ f` are compositions of bijections
(`Function.Bijective.comp`). -/
theorem IsPermutation.complementLast {B : BranchingProgram w n} (h : B.IsPermutation)
    (σ : Equiv.Perm (Fin w)) : (B.complementLast σ).IsPermutation := by
  obtain ⟨instrs⟩ := B
  rcases List.eq_nil_or_concat' instrs with rfl | ⟨l, ι, rfl⟩
  · rw [complementLast_nil]
    exact h
  · rw [isPermutation_iff] at h
    rw [complementLast_concat, isPermutation_iff]
    intro ι' hι'
    rcases List.mem_append.1 hι' with hl | hl
    · -- an unchanged instruction of `l`
      exact h ι' (List.mem_append_left _ hl)
    · -- the new last instruction `⟨ι.var, σ.symm ∘ ι.map0, σ.symm ∘ ι.map1⟩`
      rw [List.mem_singleton] at hl
      subst hl
      have hι := h ι (List.mem_append_right _ (List.mem_singleton.2 rfl))
      exact ⟨σ.symm.bijective.comp hι.1, σ.symm.bijective.comp hι.2⟩

/-- An instruction with bijective maps produces a bijection on every input:
`Function.Bijective ι.map0 ∧ Function.Bijective ι.map1 → Function.Bijective (ι.eval x)`.  Glue
for C4 (split on the bit `x ι.var`). -/
private theorem Instr.bijective_eval {ι : Instr w n}
    (hι : Function.Bijective ι.map0 ∧ Function.Bijective ι.map1) (x : Fin n → Bool) :
    Function.Bijective (ι.eval x) := by
  rw [Instr.eval_eq]
  split
  · exact hι.2
  · exact hι.1

/-- The yield's fold over instructions with bijective maps, started at a bijection `g`, is a
bijection: `(∀ ι ∈ l, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1) →
Function.Bijective g → Function.Bijective (l.foldl (fun f ι => ι.eval x ∘ f) g)`.  Glue for C4;
induction on `l` with `g` generalized (`Function.Bijective.comp`). -/
private theorem foldl_bijective (x : Fin n → Bool) (l : List (Instr w n))
    (hl : ∀ ι ∈ l, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1) (g : Fin w → Fin w)
    (hg : Function.Bijective g) :
    Function.Bijective (l.foldl (fun f ι => ι.eval x ∘ f) g) := by
  induction l generalizing g with
  | nil => exact hg
  | cons ι l ih =>
    rw [List.foldl_cons]
    exact ih (fun ι' h => hl ι' (List.mem_cons_of_mem _ h)) _
      ((Instr.bijective_eval (hl ι (List.mem_cons.2 (Or.inl rfl))) x).comp hg)

/-- **C4.** A permutation program yields a bijection on every input:
`B.IsPermutation → Function.Bijective (B.yield x)`.  Glue for [Bar89, §1, p002-b001].

**Proof sketch.** Induction on `B.instrs` with the fold generalized to a bijective start map:
`yield_eq`, and at each step `Instr.eval_eq` picks `map0` or `map1`, bijective by
`isPermutation_iff`, so the composite stays bijective (`Function.Bijective.comp`). -/
theorem IsPermutation.bijective_yield {B : BranchingProgram w n} (h : B.IsPermutation)
    (x : Fin n → Bool) : Function.Bijective (B.yield x) := by
  rw [isPermutation_iff] at h
  rw [yield_eq]
  exact foldl_bijective x B.instrs h id Function.bijective_id

end BranchingProgram

/-! ### Families and classes -/

/-- A family of width-`w` branching programs with accepting sets: `program n` takes `n` inputs and
`accept n ⊆ ([w] → [w])` is its accepting set; the family recognizes
`{u | (program |u|).yield u.get ∈ accept |u|}` [Bar89, §1, p001-b002: "`x ∈ L` iff
`B(x) ∈ F_n`"].  Registered model (`TCSlib/ComputationalModels.lean`). -/
structure BranchingProgramFamily (w : ℕ) where
  /-- The program for inputs of length `n`. -/
  program : (n : ℕ) → BranchingProgram w n
  /-- The accepting set `F_n` for inputs of length `n`. -/
  accept : (n : ℕ) → Finset (Fin w → Fin w)

namespace BranchingProgramFamily

variable {w : ℕ} (P : BranchingProgramFamily w)

/-- The language a family recognizes:
`P.language = {u | (P.program u.length).yield u.get ∈ P.accept u.length}`
[Bar89, §1, p001-b002]. -/
def language : Language Bool :=
  {u | (P.program u.length).yield u.get ∈ P.accept u.length}

/-- Reader of `language`:
`u ∈ P.language ↔ (P.program u.length).yield u.get ∈ P.accept u.length`. -/
theorem mem_language_iff (u : List Bool) :
    u ∈ P.language ↔ (P.program u.length).yield u.get ∈ P.accept u.length :=
  Iff.rfl

/-- The language unfolded:
`P.language = {u | (P.program u.length).yield u.get ∈ P.accept u.length}`. -/
theorem language_eq :
    P.language = {u | (P.program u.length).yield u.get ∈ P.accept u.length} := rfl

/-- The family has polynomial length: `∃ a k, ∀ n, (P.program n).length ≤ a * (n + 1) ^ k`
[Bar89, §1, p002-b001] (the `(n + 1)` form of `PPoly.lean`'s polynomial size). -/
def IsPolyLength : Prop :=
  ∃ a k : ℕ, ∀ n, (P.program n).length ≤ a * (n + 1) ^ k

/-- Reader of `IsPolyLength`:
`P.IsPolyLength ↔ ∃ a k, ∀ n, (P.program n).length ≤ a * (n + 1) ^ k`. -/
theorem isPolyLength_iff :
    P.IsPolyLength ↔ ∃ a k : ℕ, ∀ n, (P.program n).length ≤ a * (n + 1) ^ k :=
  Iff.rfl

/-- Every program of the family is a permutation program: `∀ n, (P.program n).IsPermutation`
[Bar89, §1, p002-b001]. -/
def IsPermutation : Prop :=
  ∀ n, (P.program n).IsPermutation

/-- Reader of `IsPermutation`: `P.IsPermutation ↔ ∀ n, (P.program n).IsPermutation`. -/
theorem isPermutation_iff : P.IsPermutation ↔ ∀ n, (P.program n).IsPermutation :=
  Iff.rfl

end BranchingProgramFamily

/-- `L ∈ BWBP`: for some width `w`, a family of width-`w` programs of polynomial length
(`length ≤ a·(n+1)^k`) recognizes `L`,
`∃ w (P : BranchingProgramFamily w), P.IsPolyLength ∧ P.language = L` [Bar89, §1, p002-b001]. -/
def Language.InBWBP (L : Language Bool) : Prop :=
  ∃ (w : ℕ) (P : BranchingProgramFamily w), P.IsPolyLength ∧ P.language = L

/-- Reader of `Language.InBWBP`:
`L.InBWBP ↔ ∃ w (P : BranchingProgramFamily w), P.IsPolyLength ∧ P.language = L`. -/
theorem Language.inBWBP_iff (L : Language Bool) :
    L.InBWBP ↔ ∃ (w : ℕ) (P : BranchingProgramFamily w), P.IsPolyLength ∧ P.language = L :=
  Iff.rfl

/-- `L ∈ PBP_w`: a family of width-`w` permutation programs of polynomial length
(`length ≤ a·(n+1)^k`) recognizes `L`,
`∃ P : BranchingProgramFamily w, P.IsPermutation ∧ P.IsPolyLength ∧ P.language = L`
[Bar89, §1, p002-b001; Corollary, p004-b004: "polynomial-length 5-PBPs"]. -/
def Language.InPBP (w : ℕ) (L : Language Bool) : Prop :=
  ∃ P : BranchingProgramFamily w, P.IsPermutation ∧ P.IsPolyLength ∧ P.language = L

/-- Reader of `Language.InPBP`:
`L.InPBP w ↔ ∃ P : BranchingProgramFamily w, P.IsPermutation ∧ P.IsPolyLength ∧
P.language = L`. -/
theorem Language.inPBP_iff (w : ℕ) (L : Language Bool) :
    L.InPBP w ↔
      ∃ P : BranchingProgramFamily w, P.IsPermutation ∧ P.IsPolyLength ∧ P.language = L :=
  Iff.rfl
