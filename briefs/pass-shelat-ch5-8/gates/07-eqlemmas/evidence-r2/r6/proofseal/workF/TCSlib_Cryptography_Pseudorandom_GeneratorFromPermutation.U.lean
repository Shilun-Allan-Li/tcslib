/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A pseudorandom generator from a one-way permutation

The concrete layer of [Gar26, §3.3.2]. For a permutation `f` and a bit `B(x, r)`, the
generator `G(x, r) = f(x) ‖ r ‖ B(x, r)` stretches its seed by one bit. If `B` is a
hard-concentrate bit for `g(x, r) = f(x) ‖ r`, then `G` is a pseudorandom generator
[Gar26, Theorem 3.2]. The concrete form: from any distinguisher `D` for `G` with
advantage `ε` we build an explicit predictor of `B(x, r)` from `f(x) ‖ r` that succeeds
with probability exactly `1/2 + ε`.

The bit `B` is arbitrary here: the theorem is the reduction, and hardness of `B` is an
assumption of the asymptotic statement. The inner-product bit of Goldreich–Levin
([Gar26, Theorem 2.3], Remark 3.1) is one instance. The domain of `f` and the type of `r`
are arbitrary finite types; `owpGenBits` and `exists_owpPredictorBits` specialize to bit
strings `{0,1}^n` and the output `{0,1}^{2n+1}`.

## Main definitions

* `owpGen f B`: the generator `G(x, r) = f(x) ‖ r ‖ B(x, r)` [Gar26, Construction 3.2].
* `owpPair f`: the function `g(x, r) = f(x) ‖ r` for which `B` is hard-concentrate.
* `owpGenNot f B`: the distribution `H_1' = f(x) ‖ r ‖ (1 - B(x, r))` of the proof.
* `owpPredictor D flip`: the predictor built from a distinguisher `D`.
* `owpGenBits`, `owpPredictorBits`: the bit-string versions.

## Main results

* `acceptProb_id_owp`: the uniform distribution is the even mixture of `H_0` and `H_1'`.
* `predProb_owpPredictor_false`, `predProb_owpPredictor_true`: the exact success
  probabilities of the predictor and of its flip.
* `exists_owpPredictor`: [Gar26, Theorem 3.2], a predictor with success `1/2 + ε`.
* `exists_owpPredictorBits`: the same on bit strings.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.2 (Construction 3.2, Remark 3.1, Theorem 3.2) and
  Definition 2.3 (hard-concentrate bits).
-/

namespace TCSlib.Cryptography

open Finset

variable {α β ρ : Type*} [Fintype α] [Fintype β] [Fintype ρ]

/-- The probability of an event on `Bool × γ` is the average of the probabilities of its
two sections. -/
theorem uprob_bool_prod {γ : Type*} [Fintype γ] (p : Bool × γ → Prop) :
    uprob p = (uprob (fun c => p (false, c)) + uprob (fun c => p (true, c))) / 2 := by
  rw [uprob_prod, uexp, Fintype.sum_bool, Fintype.card_bool]
  push_cast
  ring

/-- The generator of [Gar26, Construction 3.2]: `G(x, r) = f(x) ‖ r ‖ B(x, r)`, for a
permutation `f` of `α` and a bit `B` of `(x, r)`. -/
def owpGen (f : α ≃ α) (B : α × β → Bool) : α × β → α × β × Bool :=
  fun w => (f w.1, w.2, B w)

/-- The function `g(x, r) = f(x) ‖ r` of [Gar26, Construction 3.2], for which `B` is
assumed to be a hard-concentrate bit. -/
def owpPair (f : α ≃ α) : α × β → α × β :=
  fun w => (f w.1, w.2)

/-- The distribution `H_1' = f(x) ‖ r ‖ (1 - B(x, r))` of [Gar26, proof of Theorem 3.2]:
the generator with its last bit flipped. -/
def owpGenNot (f : α ≃ α) (B : α × β → Bool) : α × β → α × β × Bool :=
  fun w => (f w.1, w.2, !B w)

/-- The predictor of [Gar26, proof of Theorem 3.2] built from a distinguisher `D`: on
input `y = f(x) ‖ r`, draw a uniform bit `σ` and coins for `D`; output `σ` if
`D(y ‖ σ) = 1` and `1 - σ` otherwise. With `flip = true` the output is negated. It calls
`D` once and draws one extra uniform bit.

Deviation: [Gar26] assumes without loss of generality that
`Pr[D(H_0) = 1] - Pr[D(H_1') = 1]` is positive. The sign is not known to a uniform
reduction; here it is the parameter `flip` (non-uniform advice in the asymptotic layer),
and `predProb_owpPredictor_true` covers the negative sign. -/
def owpPredictor (D : α × β × Bool → ρ → Bool) (flip : Bool) : α × β → Bool × ρ → Bool :=
  fun y c => xor (if D (y.1, y.2, c.1) c.2 then c.1 else !c.1) flip

/-- The defining equation of `owpPredictor`:
`owpPredictor D flip y c = (if D(y, c₁; c₂) then c₁ else ¬c₁) ⊕ flip`. -/
theorem owpPredictor_apply (D : α × β × Bool → ρ → Bool) (flip : Bool) (y : α × β)
    (c : Bool × ρ) :
    owpPredictor D flip y c = xor (if D (y.1, y.2, c.1) c.2 then c.1 else !c.1) flip := rfl

/-- The uniform distribution on `α × β × Bool` is the even mixture of the generator's
output `H_0` and its flipped version `H_1'`: `Pr[D(U) = 1]` is the average of
`Pr[D(H_0) = 1]` and `Pr[D(H_1') = 1]`. [Gar26, proof of Theorem 3.2], the identities
`H_1 ≡ H_2` (because `f` is a permutation) and
`Pr[A(H_1) = 1] = ½ Pr[A(H_0) = 1] + ½ Pr[A(H_1') = 1]`.

**Proof sketch.** The map `(τ, x, r) ↦ (f(x), r, τ ⊕ B(x, r))` is a bijection, so the
uniform string is the image of uniform `(τ, x, r)`; split on the bit `τ`. -/
theorem acceptProb_id_owp [Nonempty ρ] (f : α ≃ α) (B : α × β → Bool)
    (D : α × β × Bool → ρ → Bool) :
    acceptProb (id : α × β × Bool → _) D =
      (acceptProb (owpGen f B) D + acceptProb (owpGenNot f B) D) / 2 := by
  let e : Bool × ((α × β) × ρ) ≃ (α × β × Bool) × ρ :=
    { toFun := fun v => ((f v.2.1.1, v.2.1.2, xor v.1 (B v.2.1)), v.2.2)
      invFun := fun z =>
        (xor z.1.2.2 (B (f.symm z.1.1, z.1.2.1)), ((f.symm z.1.1, z.1.2.1), z.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  unfold acceptProb
  refine (uprob_eq_of_equiv e
    (p := fun v : Bool × ((α × β) × ρ) => D (f v.2.1.1, v.2.1.2, xor v.1 (B v.2.1)) v.2.2 = true)
    (q := fun z : (α × β × Bool) × ρ => D (id z.1) z.2 = true) fun _ => Iff.rfl).symm.trans ?_
  rw [uprob_bool_prod]
  simp only [Bool.false_xor, Bool.true_xor]
  rfl

/-- The predictor `owpPredictor D false` predicts `B(x, r)` from `f(x) ‖ r` with
probability exactly `1/2 + (Pr[D(H_0) = 1] - Pr[D(H_1') = 1]) / 2`. [Gar26, proof of
Theorem 3.2].

**Proof sketch.** Split on whether the random bit `σ` equals `B(x, r)`, each with
probability `1/2`: if it does, the predictor is right when `D(H_0)` accepts; if not, it
is right when `D(H_1')` rejects. -/
theorem predProb_owpPredictor_false [Nonempty ρ] [Nonempty α] [Nonempty β] (f : α ≃ α)
    (B : α × β → Bool) (D : α × β × Bool → ρ → Bool) :
    predProb (owpPair f) B (owpPredictor D false) =
      1 / 2 + (acceptProb (owpGen f B) D - acceptProb (owpGenNot f B) D) / 2 := by
  let e : Bool × ((α × β) × ρ) ≃ (α × β) × (Bool × ρ) :=
    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  unfold predProb
  refine (uprob_eq_of_equiv e
    (p := fun v => owpPredictor D false (owpPair f (e v).1) (e v).2 = B (e v).1)
    (q := fun z : (α × β) × (Bool × ρ) => owpPredictor D false (owpPair f z.1) z.2 = B z.1)
    fun _ => Iff.rfl).symm.trans ?_
  rw [uprob_bool_prod, show ∀ a b : ℝ, 1 / 2 + (a - b) / 2 = (a + (1 - b)) / 2 by
    intro a b; ring]
  congr 2
  · -- the random bit equals `B(x, r)`: the predictor is right when `D(H_0)` accepts
    unfold acceptProb
    congr 1
    funext c
    apply propext
    simp only [e, owpPredictor, owpPair, owpGen, Equiv.coe_fn_mk, Bool.false_xor,
      Bool.xor_false]
    cases D (f c.1.1, c.1.2, B c.1) c.2 <;> cases B c.1 <;> simp
  · -- the random bit is `1 - B(x, r)`: the predictor is right when `D(H_1')` rejects
    unfold acceptProb
    rw [← uprob_not]
    congr 1
    funext c
    apply propext
    simp only [e, owpPredictor, owpPair, owpGenNot, Equiv.coe_fn_mk, Bool.true_xor,
      Bool.xor_false]
    cases D (f c.1.1, c.1.2, !B c.1) c.2 <;> cases B c.1 <;> simp

/-- The flipped predictor `owpPredictor D true` predicts `B(x, r)` with probability
exactly `1/2 - (Pr[D(H_0) = 1] - Pr[D(H_1') = 1]) / 2`, the case of [Gar26, proof of
Theorem 3.2] that the source discards by symmetry.

**Proof sketch.** Its output is the negation of that of `owpPredictor D false`, so its
success probability is one minus that of `predProb_owpPredictor_false`. -/
theorem predProb_owpPredictor_true [Nonempty ρ] [Nonempty α] [Nonempty β] (f : α ≃ α)
    (B : α × β → Bool) (D : α × β × Bool → ρ → Bool) :
    predProb (owpPair f) B (owpPredictor D true) =
      1 / 2 - (acceptProb (owpGen f B) D - acceptProb (owpGenNot f B) D) / 2 := by
  have h : predProb (owpPair f) B (owpPredictor D true) =
      1 - predProb (owpPair f) B (owpPredictor D false) := by
    unfold predProb
    rw [← uprob_not]
    congr 1
    funext z
    apply propext
    simp only [owpPredictor, Bool.xor_true, Bool.xor_false]
    cases (if D ((owpPair f z.1).1, (owpPair f z.1).2, z.2.1) z.2.2 then z.2.1 else !z.2.1) <;>
      cases B z.1 <;> simp
  rw [h, predProb_owpPredictor_false]
  ring

/-- PRG from a one-way permutation, concrete form [Gar26, Theorem 3.2]: if `D`
distinguishes `G(x, r) = f(x) ‖ r ‖ B(x, r)` from uniform with advantage `ε`, then for one
choice of `flip` the predictor `owpPredictor D flip` predicts `B(x, r)` from
`f(x) ‖ r` with probability exactly `1/2 + ε`. So if `B` is a hard-concentrate bit for
`g(x, r) = f(x) ‖ r`, then `G` is a pseudorandom generator. Only bijectivity of `f` is
used, not its one-wayness (which is what makes hard-concentrate bits for `g` possible).

**Proof sketch.** By `acceptProb_id_owp`, `Pr[D(G) = 1] - Pr[D(U) = 1]` is half of
`Pr[D(H_0) = 1] - Pr[D(H_1') = 1]`. Take `flip = false` if this is nonnegative and
`flip = true` otherwise, and apply `predProb_owpPredictor_false` or
`predProb_owpPredictor_true`. -/
theorem exists_owpPredictor [Nonempty ρ] [Nonempty α] [Nonempty β] (f : α ≃ α)
    (B : α × β → Bool) (D : α × β × Bool → ρ → Bool) :
    ∃ flip : Bool, predProb (owpPair f) B (owpPredictor D flip) =
      1 / 2 + prgAdv (owpGen f B) D := by
  have hU := acceptProb_id_owp f B D
  unfold prgAdv distAdv
  rcases le_total 0 (acceptProb (owpGen f B) D - acceptProb (owpGenNot f B) D) with h | h
  · refine ⟨false, ?_⟩
    rw [predProb_owpPredictor_false, hU, abs_of_nonneg (by linarith)]
    ring
  · refine ⟨true, ?_⟩
    rw [predProb_owpPredictor_true, hU, abs_of_nonpos (by linarith)]
    ring

/-! ### Bit strings -/

/-- The encoding of `f(x) ‖ r ‖ b` as a string of length `2n + 1`, written `n + n + 1`. -/
def owpBitsEquiv (n : ℕ) : (Fin n → Bool) × (Fin n → Bool) × Bool ≃ (Fin (n + n + 1) → Bool) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (((Fin.appendEquiv n n).prodCongr (Equiv.refl Bool)).trans (Fin.succFunEquiv Bool _).symm)

/-- The generator of [Gar26, Construction 3.2] on bit strings:
`G : {0,1}^{2n} → {0,1}^{2n+1}`, `G(x, r) = f(x) ‖ r ‖ B(x, r)`, for a permutation `f` of
`{0,1}^n`, with the seed given as the pair `(x, r)`. -/
def owpGenBits {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (B : (Fin n → Bool) × (Fin n → Bool) → Bool) :
    (Fin n → Bool) × (Fin n → Bool) → Fin (n + n + 1) → Bool :=
  fun w => owpBitsEquiv n (owpGen f B w)

/-- The predictor of [Gar26, proof of Theorem 3.2] for a distinguisher of `owpGenBits`:
`owpPredictor` run against `D` composed with the encoding of strings. Its cost is that of
`owpPredictor`. -/
def owpPredictorBits {n : ℕ} (D : (Fin (n + n + 1) → Bool) → ρ → Bool) (flip : Bool) :
    (Fin n → Bool) × (Fin n → Bool) → Bool × ρ → Bool :=
  owpPredictor (fun z r => D (owpBitsEquiv n z) r) flip

/-- PRG from a one-way permutation on bit strings [Gar26, Theorem 3.2]: a distinguisher
for `G(x, r) = f(x) ‖ r ‖ B(x, r) ∈ {0,1}^{2n+1}` with advantage `ε` yields, for one
choice of `flip`, a predictor of `B(x, r)` from `f(x) ‖ r` with success probability
exactly `1/2 + ε`. -/
theorem exists_owpPredictorBits [Nonempty ρ] {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (B : (Fin n → Bool) × (Fin n → Bool) → Bool) (D : (Fin (n + n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb (owpPair f) B (owpPredictorBits D flip) =
      1 / 2 + prgAdv (owpGenBits f B) D := by
  have h : prgAdv (owpGenBits f B) D = prgAdv (owpGen f B) (fun z r => D (owpBitsEquiv n z) r) :=
    prgAdv_comp_equiv (owpBitsEquiv n) (owpGen f B) D
  rw [h]
  exact exists_owpPredictor f B _

end TCSlib.Cryptography


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
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/workF/TCSlib_Cryptography_Pseudorandom_GeneratorFromPermutation.coll"
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
