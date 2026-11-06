/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.CircuitComplexity.Advice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-uniform PPT: the two formulations of Definition 26.8

[PS10, Definition 26.8] defines a non-uniform probabilistic polynomial-time machine in two
ways. **Machine-sequence form:** a sequence `A = {A₁, A₂, …}` of probabilistic machines with
a polynomial `d` such that `|Aᵢ| < d(i)` and the running time of `Aᵢ` is less than `d(i)`;
`A(x)` denotes the distribution obtained by running `A_{|x|}(x)`. **Advice form** ("alternatively"):
a uniform p.p.t. machine `A` that receives an advice string for each input length. The text
adds that "any adversarial algorithm `A` will implicitly be a non-uniform PPT", the standing
convention governing Definitions 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and the hardness
assumptions.

The frozen definition is the advice form, `Complexity.NUPPT` of
`TCSlib.Complexity.Randomized.PPT` (foundation decision D4): `advice n` of length
`≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
`A_{|y|}(y)` of the text is `NUPPT.runLit y r := runAt |y| y r` — the prefix `1^{|y|}` carries
no information — and it is the layout of the literal forms of Definition 26.1
(`WorstCaseOneWay`, `inverterLit`) and Definition 69.4 (`Ensemble.IndistLit`). The
machine-sequence form is reflected only as a sanity statement here: at every parameter `n`
the activation is a deterministic polynomial-time function of `(y, r)`
(`NUPPT.polyTimeComputable_runAtL`). The machine of that statement hard-wires `1^n` and
`advice n`, so its size and its time constants depend on `n`: the lemma bounds neither the
size of "`A_n`" nor its running time uniformly in `n` (it would hold equally with
exponentially long advice). The polynomial size of Definition 26.8's `A_n` comes from
`|advice n| ≤ adv.eval n` (the field `NUPPT.advice_length`), not from this lemma.

**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). The equivalence of the two forms (`NUPPTSeq`, `nuppt_seq_iff_advice`, with
`Turing.CodeTM.serialize` as the description size, `⇒` through `Turing.timed_universal`) is
the optional module `Randomized/Sequence.lean` with one named admission; no theorem of
chapters 2–4 depends on it.

This file also holds the uniformity lemmas (a PPT is an `NUPPT` with empty advice,
`Complexity.PPT` the subtype) and the **optional** sanity bridge to the library's
advice-taking machines `Turing.FinTM.DecidesWithAdviceInTime` [AB09, Definition 6.16]
(`NUPPT.decides_of_decidesWithAdviceInTime`, stated with its sketch; it needs the clocking
construction `NUPPT.ofPartial` and is off every critical path).

## Main definitions

* `Complexity.PPT.toNUPPT`, `Complexity.PPT.ofPolyTime` — the subtype API of PPTs.

## Main results

* `Complexity.NUPPT.runLit_eq_runAt`, `NUPPT.runLit_eq_runAtL` — the literal activation
  unfolds to the activation at parameter `|y|`.
* `Complexity.NUPPT.Uniform.runAtL_eq`, `NUPPT.Uniform.runAt_eq`, `NUPPT.ofPolyTime_uniform` —
  uniform machines run on `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (the readings `NUPPT.uniform_iff` and
  `NUPPT.Uniform.advice_eq` are beside `NUPPT.Uniform` in `Randomized/PPT.lean`).
* `Complexity.NUPPT.polyTimeComputable_runAtL` — at a fixed parameter the activation is a
  deterministic polynomial-time function of `(y, r)`, with constants that depend on `n` (not a
  uniform size bound on the "`A_n`" of the machine-sequence form).
* `Complexity.NUPPT.decides_of_decidesWithAdviceInTime` — (optional, sorried) a language
  decided with polynomial advice in polynomial time [AB09, Definition 6.16] is decided by an
  `NUPPT` at the input length.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1.3, Definition 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.3, Definition 6.16, machines with advice.)
-/

namespace Complexity

open Turing

namespace NUPPT

variable (A : NUPPT)

/-- The literal activation `A_{|y|}(y)` is the activation at parameter `|y|`
[PS10, Definition 26.8, "`A(x)` denotes `A_{|x|}(x)`"]. -/
theorem runLit_eq_runAt (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAt y.length y r := rfl

/-- The literal activation with the coins as a list. -/
theorem runLit_eq_runAtL (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAtL y.length y (List.ofFn r) := rfl

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩`: the advice slot is empty. -/
theorem Uniform.runAtL_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, h n]

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (typed coins). -/
theorem Uniform.runAt_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.output (pairEncode (pairEncode (advInput n y) []) (List.ofFn r)) := by
  rw [NUPPT.runAt_eq, h.runAtL_eq]

/-- `ofPolyTime` with an everywhere-empty advice function is uniform. -/
theorem ofPolyTime_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (h : ∀ n, advice n = []) : (ofPolyTime hf coins adv advice hα).Uniform :=
  (uniform_iff _).2 fun n => (congrFun (advice_ofPolyTime hf coins adv advice hα) n).trans (h n)

/-- The literal activation of a uniform polynomial-time machine is `f` on
`⟨⟨⟨1^{|y|}, y⟩, []⟩, r⟩`. -/
theorem runLit_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (y : List Bool) (r : (ofPolyTimeUniform hf coins).Coins y.length) :
    (ofPolyTimeUniform hf coins).runLit y r =
      f (pairEncode (pairEncode (advInput y.length y) []) (List.ofFn r)) := by
  rw [runLit_eq_runAtL, runAtL_ofPolyTimeUniform]

/-- **The machine-sequence view, sanity direction.** At each fixed parameter `n`, the
activation of `A` is a deterministic polynomial-time function of the pair `⟨y, r⟩`
[PS10, Definition 26.8, first formulation, the "`A_n`"]. The machine hard-wires `1^n` and
`advice n`, so its size and its time constants depend on `n`: the statement is per `n` and
would hold equally with exponentially long advice. It is **not** the polynomial-size half of
Definition 26.8; that half comes from `|advice n| ≤ adv.eval n` (`NUPPT.advice_length`), not
from this lemma.

**Proof sketch.** The raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` is assembled from `⟨y, r⟩` by
`PolyTimeComputable.pairEncode` with the constant strings `1^n` and `advice n`
(`polyTimeComputable_const`) and the projections `pairFstD`/`pairSndD`; then
`NUPPT.polyTimeComputable_output`. -/
theorem polyTimeComputable_runAtL (n : ℕ) :
    PolyTimeComputable fun z => A.runAtL n (pairFstD z) (pairSndD z) := by
  have h := A.polyTimeComputable_output.comp
    ((((polyTimeComputable_const (List.replicate n true)).pairEncode
      polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_const (A.advice n))).pairEncode
      polyTimeComputable_pairSndD)
  convert h using 1

/-- **Optional sanity bridge** (not on the critical path): a language decided by a machine
with polynomial-length advice within polynomial time [AB09, Definition 6.16]
(`Turing.FinTM.DecidesWithAdviceInTime`) is decided by an `NUPPT` activated at the input
length, i.e. by a non-uniform PPT in the sense of [PS10, Definition 26.8]. The two advice
notions agree: `α n` becomes the advice at parameter `n` and the time bound in `|x|` becomes
a bound in the machine-input length.

**Proof sketch.** The hypothesis bounds `M` only on the well-formed inputs
`pairEncode x (α |x|)`; the `NUPPT` must halt on every input, so `M` is first clocked:
`Turing.timed_universal` run on `⟨⟨bits (C (m+1)^c), code M⟩, w⟩` halts on every `w`
within a polynomial of `|w|` and agrees with `M` whenever `M` halts within the clock
(this is the optional lemma `NUPPT.ofPartial`). The `NUPPT` `A` has advice `α n` (length
`Ca (n+1)^ca = (normal Ca ca).eval n`, so `adv := normal Ca ca`), no coins (`coins := const 0`),
and output function `z ↦ clockedM (pairEncode (inArg z) (inAdvice z))` where `inArg`/`inAdvice`
are the projections of the raw layout (FP by the pairing calculus). On the raw input
`⟨⟨⟨1^{|x|}, x⟩, α |x|⟩, r⟩` the re-pairing is `pairEncode x (α |x|)`, on which `M` halts within
`C (|x|+1)^c` with output `[indicator L x]` (hypothesis `h x`), so the clocked machine returns
the same by determinism (`NUPPT.output_eq_of_computesInTime`). -/
theorem decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  sorry

end NUPPT

namespace PPT

/-- The underlying non-uniform machine of a PPT. -/
def toNUPPT (A : PPT) : NUPPT := A.1

/-- A PPT has empty advice. -/
theorem uniform (A : PPT) : A.toNUPPT.Uniform := A.2

/-- The PPT with output function `f` and coin polynomial `coins`
(`Complexity.NUPPT.ofPolyTimeUniform`). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : PPT :=
  ⟨NUPPT.ofPolyTimeUniform hf coins, NUPPT.ofPolyTimeUniform_uniform hf coins⟩

/-- The underlying machine of `PPT.ofPolyTime hf coins` is `NUPPT.ofPolyTimeUniform hf coins`. -/
theorem toNUPPT_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTime hf coins).toNUPPT = NUPPT.ofPolyTimeUniform hf coins := rfl

end PPT

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
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/work/TCSlib_Complexity_Randomized_NonUniform.coll"
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
