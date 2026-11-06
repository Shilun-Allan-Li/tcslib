/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete claims of the proof of the Goldreich–Levin theorem

The concrete claims of the proof of [PS10, Theorem 87.3] (§3.4.3): the oversimplified case,
the `3/4 + ε` case, the good set, Fact 88.4, the pairwise-independence and union-bound
claims about Algorithm 89.6, and the final bound — each a re-export of the corresponding
concrete lemma of the Garg layer (`TCSlib/Cryptography/HardcoreBit/*`). The claims about
the prediction and inversion experiments of `g` (`thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`,
`thm_87_3_9`) are stated at the family level (`FunFamily.glPad`, `FunFamily.glBit`,
`FunFamily.glInverter` of `TCSlib.Cryptography.Asymptotic.HardCore`), through the bridges
`FunFamily.predProb_glPad` and `FunFamily.invProb_glInverter`; the claims about the inner
product and the samples of Algorithm 89.6 (`fact_88_4`, `thm_87_3_6`, `thm_87_3_7`,
`thm_87_3_8`) do not involve the family and are stated concretely, for an arbitrary
`f : {0,1}^n → β` (gate 03c, finding 7). The declaration names encode the inventory ids
(Thm-87.3.x), not [PS10] numbers. (Moved out of `Asymptotic/HardCore.lean` for size; the
statements are those of the audited statement phase.)

## Main definitions

None.

## Main results

* `TCSlib.Cryptography.fact_88_4` — `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` [PS10, Fact 88.4].
* `TCSlib.Cryptography.thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3` — the oversimplified case, the
  `3/4 + ε` case (Algorithm 88.5) and the good set [PS10, §3.4.3].
* `TCSlib.Cryptography.thm_87_3_6`, `thm_87_3_7`, `thm_87_3_8`, `thm_87_3_9` — pairwise
  independent samples, subset sums, the guessing step and the final bound of
  Algorithm 89.6 [PS10, §3.4.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithms 88.5, 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The concrete claims of the proof of Theorem 87.3 [PS10, §3.4.3]

The setting (inventory Thm-87.3.c) is `FunFamily.glPad`, `FunFamily.glBit`,
`FunFamily.glInverter` over the concrete `HardcoreBit.ip`, `glPad`, `glBit`, `glInverter`,
`secProb` (`Pr_r[A(f(x), r) = ⟨x, r⟩]` for a fixed `x`). Algorithm 88.5 is
`HardcoreBit.majorityInverter` (`majorityRecover`, `trialBit`); Algorithm 89.6 is
`HardcoreBit.guessInverter` (`guessRecover`, the subroutine `C` realised by guessing the
`k = log m` bits `b'_j` and forming subset sums). Each claim below re-exports the
corresponding concrete lemma: at the family level for the claims about `g`, concretely for
`fact_88_4` and `thm_87_3_6/7/8`. -/

/-- **Fact 88.4** [PS10]: `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` (bit strings as a Boolean ring, `+` is
XOR); the concrete `HardcoreBit.ip_add`. -/
theorem fact_88_4 {n : ℕ} (a b c : Fin n → Bool) :
    HardcoreBit.ip a (b + c) = HardcoreBit.ip a b + HardcoreBit.ip a c :=
  HardcoreBit.ip_add a b c

/-- **The oversimplified case** [PS10, §3.4.3; inventory Thm-87.3.1]: if `A` predicts `⟨x, r⟩`
from `g(x, r)` with probability one, the inverter querying `e_1, …, e_n` (the concrete
`perfectRecover`, `⟨x, e_i⟩ = x_i`) inverts `g` with probability one. -/
theorem thm_87_3_1 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool)
    (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover
      fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r)) = 1 := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  rw [← HardcoreBit.perfectInverter_eq]
  exact HardcoreBit.invProb_perfectInverter _ _ h

/-- **The less simplified case** [PS10, §3.4.3, Algorithm 88.5; inventory Thm-87.3.2]: if `A`
predicts `⟨x, r⟩` with probability `3/4 + ε` and `n ≤ 2ε²T`, the inverter taking the majority
of `T` guesses `A(y, r) ⊕ A(y, r ⊕ e_i)` per bit inverts `g` with probability at least `ε/4`
(the text's Chernoff bound is Chebyshev with pairwise independence). -/
theorem thm_87_3_2 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hT : (𝓕.inLen.eval n : ℝ) ≤ 2 * ε ^ 2 * T)
    (h : 3 / 4 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 4 ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.majorityRecover
      (fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) T)) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  rw [← HardcoreBit.majorityInverter_eq]
  exact HardcoreBit.invProb_majorityInverter _ _ hε hT h

/-- **The good set is large** [PS10, §3.4.3; inventory Thm-87.3.3]: if `A` predicts `⟨x, r⟩`
with probability `c + ε` (`c = 3/4` or `1/2`), then `Pr_x[Pr_r[A(f(x), r) = ⟨x, r⟩] ≥ c + ε/2] ≥ ε/2`
(the text's displayed chain `< ε/2 + (1 − ε/2)(c + ε/2) < c + ε`). -/
theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (h : c + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 2 ≤ uprob fun x => c + ε / 2 ≤ HardcoreBit.secProb (𝓕.f n)
      (fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) x := by
  rw [FunFamily.predProb_glPad] at h
  exact HardcoreBit.half_le_uprob_good _ _ hc hε h

/-- **Pairwise-independent samples suffice** [PS10, §3.4.3; inventory Thm-87.3.6]: for a good
`x` (`secProb ≥ 1/2 + ε/2`) and `k ≥ 1`, each bit of the ideal recovery procedure (correct
guesses `b_L = ⟨x, S_L⟩`) is wrong with probability at most `1/(ε²(2^k − 1))`, by the
pairwise-independent sampling inequality (`chebyshev_pairwise`); the concrete
`uprob_idealRecover_ne_le`, stated for an arbitrary `f`. The text bounds this probability by
`(1 − 4ε'²)/(4mε'²) ≤ 1/(mε'²)` with `ε' = ε/2`; the formal `1/(ε²(2^k − 1)) = 1/(4mε'²)` lies
between the two, with `m` read as the number `2^k − 1` of samples, one per nonempty `L ⊆ [k]`
(the text draws the `m − 1` samples `r_1, …, r_{m−1}` from `log m` seeds and writes `m`; its
`m` is the `2^k` of `thm_87_3_8`). -/
theorem thm_87_3_6 {n : ℕ} {β ρ : Type*} [Fintype ρ] [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (hk : 0 < k) (x : Fin n → Bool) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) (hx : 1 / 2 + ε / 2 ≤ HardcoreBit.secProb f A x) :
    uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → HardcoreBit.NESubset k → ρ) =>
      HardcoreBit.idealRecover f A x ω.1 ω.2 i ≠ x i) ≤ 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
  HardcoreBit.uprob_idealRecover_ne_le f A hk x i hε hx

/-- **Subset sums are pairwise independent and uniform** [PS10, §3.4.3, "show this!";
inventory Thm-87.3.7]: for uniform `s_1, …, s_k ∈ {0,1}^n`, the `2^k − 1` strings
`r_L = ⊕_{j ∈ L} s_j` over nonempty `L ⊆ [k]` are each uniform and pairwise independent
(the concrete `pairwiseUniform_subsetSum`; `card_nonempty_finset` counts them). -/
theorem thm_87_3_7 {n k : ℕ} :
    HardcoreBit.PairwiseUniform fun (L : HardcoreBit.NESubset k) (s : Fin k → Fin n → Bool) =>
      HardcoreBit.subsetSum L.1 s :=
  HardcoreBit.pairwiseUniform_subsetSum

/-- **All guesses are right with probability `1/m = 2^{−k}`, and then every `b_L` is right**
[PS10, §3.4.3; inventory Thm-87.3.8]: the guessed bits `b'_1 ⋯ b'_k` equal `⟨x, s_1⟩ ⋯ ⟨x, s_k⟩`
with probability `1/2^k` (`uprob_guess_eq`), and under that event the recovery procedure
computes `b_L = ⟨x, S_L⟩` for every `L`, i.e. it is the ideal procedure
(`guessRecover_correct_guess`); stated for an arbitrary `f`. Here `m = 2^k` is the text's `m`
(`log m` guessed bits), while `thm_87_3_6` counts the `2^k − 1` samples. -/
theorem thm_87_3_8 {n : ℕ} {β ρ : Type*} [Fintype ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (x : Fin n → Bool) (s : Fin k → Fin n → Bool)
    (cs : Fin n → HardcoreBit.NESubset k → ρ) :
    uprob (fun b : Fin k → Bool => b = fun j => HardcoreBit.ip x (s j)) = 1 / 2 ^ k ∧
      HardcoreBit.guessRecover A k (f x) (s, fun j => HardcoreBit.ip x (s j), cs) =
        HardcoreBit.idealRecover f A x s cs :=
  ⟨HardcoreBit.uprob_guess_eq _, HardcoreBit.guessRecover_correct_guess f A x s cs⟩

/-- **The final bound of the general case** [PS10, §3.4.3, Algorithm 89.6; inventory
Thm-87.3.9]: if `A` predicts `⟨x, r⟩` from `g(x, r)` with probability `1/2 + ε` and
`2n ≤ ε²(2^k − 1)`, the inverter of Algorithm 89.6 with `k` guessed bits inverts `g` with
probability at least `ε/(4·2^k)`; with `ε² 2^k ≤ 4n` this is at least `ε³/(16n)`.

**Deviation:** the text's constant is `ε'/(2m) = ε³/(32n)` with `ε' = ε/2`, `m = 2n/ε'²`
(source error 37); the concrete bound is stronger. -/
theorem thm_87_3_9 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 2 * (𝓕.inLen.eval n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / (4 * 2 ^ k) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover
      (fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) k)) ∧
    (ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * 𝓕.inLen.eval n →
      ε ^ 3 / (16 * 𝓕.inLen.eval n) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n
        (HardcoreBit.guessRecover
          (fun y r => A ((𝓕.glPad_outEquiv n).symm
              (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r) k))) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  rw [← HardcoreBit.guessInverter_eq]
  exact ⟨HardcoreBit.invProb_guessInverter _ _ hε hk h,
    fun hk' => HardcoreBit.invProb_guessInverter_cubic _ _ hε hk hk' h⟩

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
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/workF/TCSlib_Cryptography_Asymptotic_HardCoreClaims.coll"
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
