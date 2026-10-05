/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.DNF
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.CookLevin.Hardness
import TCSlib.Complexity.TuringMachine.Build.Primitives
import Mathlib.Data.Sigma.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TAUTOLOGY and coNP-completeness

[AB09, §2.6.1, Example 2.21]: `TAUTOLOGY` — formulas satisfied by every
assignment — is `coNP`-complete. This module defines `coNP`-hardness and
completeness (mirroring the audited `NP` notions), the language `TAUTOLOGY`
over the **DNF fragment**, and states Example 2.21.

## Design and deviations from [AB09]

* **`TAUTOLOGY` is rendered on the DNF fragment, and says so** ([AB09] states
  it for general Boolean formulas): the phase-3 round-1 audit verified both
  that the *CNF*-restricted tautology language is polynomial-time decidable —
  a CNF is a tautology iff every clause contains a complementary pair, so it
  is **not** [AB09]'s language — and that Example 2.21's own reduction
  produces exactly a DNF, the De Morgan dual of the Cook-Levin CNF. The
  fragment rendering therefore carries the example's full mathematical
  content (its hardness *is* Example 2.21's argument), while general Boolean
  formulas remain unformalized, per the audit's do-not-silently-identify
  guidance. Strings are read through the **shared** audited serialization
  (`Std.Sat.CNF.decode`), evaluated dually. **Seeded design question (e) for
  the phase-4 audit.**
* **The fallback flips sides**: the empty formula is a CNF tautology but the
  empty *disjunction* is false, so under the DNF reading non-well-formed
  strings are **not** in `TAUTOLOGY` — each language's malformed branch
  follows its own predicate on the fallback (the phase-3 finding-5
  discipline).
* `Complexity.coNPHard`/`coNPComplete` are new definitions on the audited
  phase-1 notions (`coNP`, `≤ₚ`), stated here rather than in the frozen
  `CoNP.lean`/`Reductions.lean`, per standing practice. **Seeded design
  question (f).**

## Main definitions

* `Complexity.coNPHard`, `Complexity.coNPComplete` — [AB09, §2.6.1]
  (Karp-reduction form).
* `Complexity.TAUTOLOGY` — [AB09, §2.6.1, Example 2.21], DNF fragment.

## Main results

* `Complexity.TAUTOLOGY_mem_coNP` — the falsifying assignment certifies the
  complement. [AB09, §2.6.1]
* `Complexity.TAUTOLOGY_coNPComplete` — [AB09, Example 2.21].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20 and
  Example 2.21, pp. 55-56.)
-/

namespace Complexity

open Std.Sat (CNF)

/-- **`coNP`-hardness** [AB09, §2.6.1]: every `coNP` language Karp-reduces to
`L` — the mirror of the audited `Complexity.NPHard`. -/
def coNPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ coNP, L' ≤ₚ L

/-- **`coNP`-completeness** [AB09, §2.6.1]: membership in `coNP` together
with `coNP`-hardness. -/
def coNPComplete (L : Language Bool) : Prop :=
  L ∈ coNP ∧ coNPHard L

/-- **The language `TAUTOLOGY`** [AB09, §2.6.1, Example 2.21], on the DNF
fragment: binary strings whose decoded formula — the shared audited
serialization, **read dually** as an OR of ANDs — is satisfied by every
assignment. Under the DNF reading the fallback (the empty formula, an empty
disjunction) is *not* a tautology, so non-well-formed strings lie outside
`TAUTOLOGY` (see the deviations list). -/
def TAUTOLOGY : Language Bool :=
  {x | (CNF.decode x).DNFTautology}

/-! **Epoch-3 fill addition.** Private certificate and verifier machinery for
the audited membership proof. No concurrent SAT fill is used. -/

/-- Negating the literal polarities twice restores the syntax. -/
private lemma taut_dual_dual (φ : CNF ℕ) : CNF.dual (CNF.dual φ) = φ := by
  delta CNF.dual
  simp [List.map_map, Function.comp_def]

/-- Changing literal polarities preserves the mentioned-variable bound. -/
private lemma taut_numVars_dual (φ : CNF ℕ) : (CNF.dual φ).numVars = φ.numVars := by
  delta CNF.numVars CNF.dual
  simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- DNF evaluation depends only on the mentioned variables.

**Proof sketch.** Apply CNF evaluation congruence to the literal-negated
formula. The proved De Morgan identity negates both values; involutivity
and preservation of the variable bound transfer the equality back. -/
private lemma taut_eval_congr {φ : CNF ℕ} {a b : ℕ → Bool}
    (h : ∀ v < φ.numVars, a v = b v) : φ.evalDNF a = φ.evalDNF b := by
  have he := eval_congr_of_lt_numVars (φ := CNF.dual φ)
    (a := a) (b := b) (by simpa only [taut_numVars_dual] using h)
  rw [← taut_dual_dual φ, CNF.evalDNF_dual, CNF.evalDNF_dual, he]

/-- A finite certificate supplies false outside its explicitly stored bits. -/
private def tautAssignment (u : List Bool) : ℕ → Bool := fun v => u.getD v false

/-- The finite certificate condition is exactly complement membership.

**Proof sketch.** Negate the universal definition of DNF tautology. Restrict
a falsifying assignment to the first input-length-plus-one positions using
`List.ofFn`. The decoded-variable bound and `taut_eval_congr` preserve the
value. Conversely the total extension of a certificate is itself a
falsifying assignment. This includes malformed strings and the empty input. -/
private lemma taut_certificate_equiv (x : List Bool) :
    x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧
        (CNF.decode x).evalDNF (tautAssignment u) = false := by
  classical
  have hn : x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
      ∃ a : ℕ → Bool, (CNF.decode x).evalDNF a = false := by
    change (¬ ∀ a : ℕ → Bool, (CNF.decode x).evalDNF a = true) ↔ _
    simp only [not_forall, Bool.not_eq_true]
  rw [hn]
  constructor
  · rintro ⟨a, ha⟩
    let u := List.ofFn (fun i : Fin (x.length + 1) => a i.val)
    refine ⟨u, List.length_ofFn, ?_⟩
    have he : (CNF.decode x).evalDNF (tautAssignment u) =
        (CNF.decode x).evalDNF a := by
      apply taut_eval_congr
      intro v hv
      have hv' : v < x.length + 1 := lt_of_lt_of_le hv
        (Nat.le_trans (CNF.numVars_decode_le x) (Nat.le_succ _))
      simp only [tautAssignment, u, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        dif_pos hv', Option.getD_some]
    exact he.trans ha
  · rintro ⟨u, _, hu⟩
    exact ⟨tautAssignment u, hu⟩

/-- P10 at coefficient and degree one solves exactly the odd-length equation. -/
private lemma taut_split_some (N i : ℕ) (h : Turing.solveSplit 1 1 N = some i) :
    i + (i + 1) = N := by
  simpa [Nat.pow_one] using List.find?_some h

/-- Strict increase of the split equation makes its bounded solution unique. -/
private lemma taut_split_exists (N i : ℕ) (h : i + (i + 1) = N) :
    Turing.solveSplit 1 1 N = some i := by
  cases hs : Turing.solveSplit 1 1 N with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp; omega)
    simp [h] at hn
  | some j =>
    have hj := taut_split_some N j hs
    congr 1
    omega

/-- The total verifier specification rejects every failed odd split and
negates the decoded DNF only after that split has succeeded. -/
private def tautVerifierBit (z : List Bool) : Bool :=
  match Turing.solveSplit 1 1 z.length with
  | none => false
  | some i => !((CNF.decode (z.take i)).evalDNF (tautAssignment (z.drop i)))

/-- The verifier language is the accepting set of its single buffered bit. -/
private def tautVerifier : Language Bool := {z | tautVerifierBit z = true}

/-- Correctly sized certificates recover their own split and evaluation. -/
private lemma taut_verifier_append (x u : List Bool) (hu : u.length = x.length + 1) :
    x ++ u ∈ tautVerifier ↔ (CNF.decode x).evalDNF (tautAssignment u) = false := by
  have hs := taut_split_exists (x ++ u).length x.length (by simp [hu])
  change tautVerifierBit (x ++ u) = true ↔ _
  simp only [tautVerifierBit, hs, List.take_left, List.drop_left, Bool.not_eq_true']

/-- Even total input lengths are explicitly rejected, including length zero. -/
private lemma taut_verifier_even (z : List Bool) (hz : z.length % 2 = 0) :
    tautVerifierBit z = false := by
  unfold tautVerifierBit
  cases hs : Turing.solveSplit 1 1 z.length with
  | none => rfl
  | some i =>
    have hi := taut_split_some z.length i hs
    omega

/-- Parse failure accepts every correctly sized certificate: the empty
fallback has false DNF value, so it belongs to the complement. -/
private lemma taut_malformed (x u : List Bool) (hx : CNF.parse x = none)
    (hu : u.length = x.length + 1) :
    x ∈ (TAUTOLOGYᶜ : Language Bool) ∧ x ++ u ∈ tautVerifier := by
  have hv : (CNF.decode x).evalDNF (tautAssignment u) = false := by
    simp only [CNF.decode, hx, Option.getD_none]
    rfl
  exact ⟨(taut_certificate_equiv x).mpr ⟨u, hu, hv⟩,
    (taut_verifier_append x u hu).mpr hv⟩

/-- Once the concrete verifier is polynomial-time, the audited parameters
`(1,1)` close the original membership statement without any SAT dependency. -/
private lemma taut_membership_of_verifier (hV : tautVerifier ∈ P) :
    TAUTOLOGY ∈ coNP := by
  refine ⟨1, 1, tautVerifier, hV, fun x => ?_⟩
  simp only [Nat.pow_one, Nat.one_mul]
  rw [taut_certificate_equiv]
  exact exists_congr fun u => and_congr_right fun hu => (taut_verifier_append x u hu).symm

/-- The six states of the syntax-only LL(1) pass. `done` accepts only at
the end of the formula half; any trailing bit moves permanently to `bad`. -/
private inductive TautSyntax where
  | formula | clause | unary | polarity | done | bad

/-- Syntax-state equality stays a private implementation detail. -/
private instance tautSyntaxDecidableEq : DecidableEq TautSyntax :=
  (proxy_equiv% TautSyntax).symm.decidableEq

/-- A finite enumeration of the syntax control. -/
private instance tautSyntaxFintype : Fintype TautSyntax := derive_fintype% _

/-- One syntax step, independent of all assignment values. -/
private def tautSyntaxStep : TautSyntax → Bool → TautSyntax
  | .formula, true => .clause
  | .formula, false => .done
  | .clause, true => .unary
  | .clause, false => .formula
  | .unary, true => .unary
  | .unary, false => .polarity
  | .polarity, _ => .clause
  | .done, _ => .bad
  | .bad, _ => .bad

/-- Complete the syntax scan and require exact consumption. -/
private def tautSyntaxAccept (q : TautSyntax) (x : List Bool) : Bool :=
  x.foldl tautSyntaxStep q == TautSyntax.done

/-- Unfold a single syntax transition. -/
private lemma taut_syntax_cons (q : TautSyntax) (b : Bool) (x : List Bool) :
    tautSyntaxAccept q (b :: x) = tautSyntaxAccept (tautSyntaxStep q b) x := rfl

/-- A bad prefix cannot recover on a later suffix. -/
private lemma taut_syntax_bad (x : List Bool) : tautSyntaxAccept .bad x = false := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [taut_syntax_cons, tautSyntaxStep] using ih

/-- Finishing the formula requires no trailing input. -/
private lemma taut_syntax_done (x : List Bool) :
    tautSyntaxAccept .done x = x.isEmpty := by
  cases x with
  | nil => rfl
  | cons b x => exact taut_syntax_bad x

/-- The unary scanner preserves precisely the suffix after the leading run. -/
private lemma taut_takeTrues_shape (x : List Bool) :
    x = List.replicate (CNF.takeTrues x).1 true ++ (CNF.takeTrues x).2 := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => rfl
    | true => simpa [CNF.takeTrues, List.replicate_succ] using congrArg (true :: ·) ih

/-- A successful literal parse consumes exactly the serialized literal. -/
private lemma taut_parseLit_shape {x r : List Bool} {ℓ : Std.Sat.Literal ℕ}
    (h : CNF.parseLit x = some (ℓ, r)) : x = CNF.serializeLit ℓ ++ r := by
  have hs := taut_takeTrues_shape x
  unfold CNF.parseLit at h
  split at h
  · cases h
  · rename_i k b rest ht
    cases h
    simpa only [ht, CNF.serializeLit, List.append_assoc,
      List.cons_append, List.nil_append] using hs
  · cases h

/-- Successful clause parsing accounts for every consumed input bit.

**Proof sketch.** Induct on parser fuel. The closing marker is the empty
clause. Otherwise a successful literal parse consumes its exact serialization
and the induction hypothesis accounts for the remaining clause body. -/
private lemma taut_parseClause_shape {fuel : ℕ} {x r : List Bool} {C : CNF.Clause ℕ}
    (h : CNF.parseClause fuel x = some (C, r)) : x = CNF.serializeClause C ++ r := by
  induction fuel generalizing x C r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b x =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b x =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hl : CNF.parseLit (true :: x) with
        | none => simp only [CNF.parseClause, hl] at h; cases h
        | some p =>
          obtain ⟨ℓ, s⟩ := p
          cases hc : CNF.parseClause fuel s with
          | none => simp only [CNF.parseClause, hl, hc] at h; cases h
          | some p =>
            obtain ⟨D, t⟩ := p
            simp only [CNF.parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [taut_parseLit_shape hl, ih hc]
            simp [CNF.serializeClause, List.append_assoc]

/-- Successful formula parsing accounts for every consumed input bit. -/
private lemma taut_parseClauses_shape {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : CNF.parseClauses fuel x = some (φ, r)) : x = CNF.serialize φ ++ r := by
  induction fuel generalizing x φ r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b x =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b x =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hc : CNF.parseClause fuel x with
        | none => simp only [CNF.parseClauses, hc] at h; cases h
        | some p =>
          obtain ⟨C, s⟩ := p
          cases hp : CNF.parseClauses fuel s with
          | none => simp only [CNF.parseClauses, hc, hp] at h; cases h
          | some p =>
            obtain ⟨ψ, t⟩ := p
            simp only [CNF.parseClauses, hc, hp, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [taut_parseClause_shape hc, ih hp]
            simp [CNF.serialize, List.append_assoc]

/-- Every accepted string is the serialization of its exact parsed formula. -/
private lemma taut_parse_shape {x : List Bool} {φ : CNF ℕ}
    (h : CNF.parse x = some φ) : x = CNF.serialize φ := by
  unfold CNF.parse at h
  split at h
  · rename_i ψ hp
    cases h
    simpa only [List.append_nil] using taut_parseClauses_shape hp
  · cases h

/-- The syntax-only unary pass is the parser's leading-run scan followed by
its terminator and polarity requirements. -/
private lemma taut_syntax_unary (x : List Bool) :
    tautSyntaxAccept .unary x =
      match (CNF.takeTrues x).2 with
      | false :: _ :: rest => tautSyntaxAccept .clause rest
      | _ => false := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | true => simpa only [taut_syntax_cons, tautSyntaxStep, CNF.takeTrues] using ih
    | false => cases x <;> rfl

/-- From a literal-start marker the syntax scan and literal parser agree. -/
private lemma taut_syntax_literal (x : List Bool) :
    tautSyntaxAccept .clause (true :: x) =
      match CNF.parseLit (true :: x) with
      | some (_, r) => tautSyntaxAccept .clause r
      | none => false := by
  rw [taut_syntax_cons, tautSyntaxStep, taut_syntax_unary]
  simp only [CNF.parseLit, CNF.takeTrues]
  generalize CNF.takeTrues x = p
  obtain ⟨k, r⟩ := p
  cases r with
  | nil => rfl
  | cons b r => cases b <;> cases r <;> rfl

/-- The clause pass agrees with the audited parser whenever its fuel covers
the remaining input. It returns control to the formula state at the clause
terminator, and rejects every incomplete literal. -/
private lemma taut_syntax_clause (fuel : ℕ) (x : List Bool) (hf : x.length ≤ fuel) :
    tautSyntaxAccept .clause x =
      match CNF.parseClause fuel x with
      | some (_, r) => tautSyntaxAccept .formula r
      | none => false := by
  induction fuel generalizing x with
  | zero => have hx : x = [] := List.length_eq_zero_iff.mp (by omega); subst x; rfl
  | succ fuel ih =>
    cases x with
    | nil => rfl
    | cons b x =>
      cases b with
      | false => rfl
      | true =>
        rw [taut_syntax_literal]
        cases hl : CNF.parseLit (true :: x) with
        | none => simp [CNF.parseClause, hl]
        | some p =>
          obtain ⟨ℓ, r⟩ := p
          have hs := congrArg List.length (taut_parseLit_shape hl)
          simp only [List.length_cons, List.length_append, CNF.serializeLit,
            List.length_replicate, List.length_nil] at hs
          have hr : r.length ≤ fuel := by simp only [List.length_cons] at hf; omega
          cases hc : CNF.parseClause fuel r with
          | none => simpa only [CNF.parseClause, hl, hc] using ih r hr
          | some p =>
            obtain ⟨D, s⟩ := p
            simpa only [CNF.parseClause, hl, hc] using ih r hr

/-- The complete syntax pass succeeds exactly when `CNF.parse` does.

**Proof sketch.** Induct on formula-parser fuel. A clause-start bit invokes
the clause lemma and then the induction hypothesis on its strictly shorter
remainder. A formula terminator succeeds only at the end of the string.
Thus malformed suffixes cannot be hidden by an earlier semantic value. -/
private lemma taut_syntax_formula (fuel : ℕ) (x : List Bool) (hf : x.length ≤ fuel) :
    tautSyntaxAccept .formula x =
      match CNF.parseClauses fuel x with
      | some (_, r) => r.isEmpty
      | none => false := by
  induction fuel generalizing x with
  | zero => have hx : x = [] := List.length_eq_zero_iff.mp (by omega); subst x; rfl
  | succ fuel ih =>
    cases x with
    | nil => rfl
    | cons b x =>
      cases b with
      | false => exact taut_syntax_done x
      | true =>
        have hx : x.length ≤ fuel := by simp only [List.length_cons] at hf; omega
        rw [taut_syntax_cons, tautSyntaxStep, taut_syntax_clause fuel x hx]
        cases hc : CNF.parseClause fuel x with
        | none => simp [CNF.parseClauses, hc]
        | some p =>
          obtain ⟨C, r⟩ := p
          have hs := congrArg List.length (taut_parseClause_shape hc)
          simp only [List.length_append] at hs
          have hr : r.length ≤ fuel := by omega
          cases hp : CNF.parseClauses fuel r with
          | none => simpa only [CNF.parseClauses, hc, hp] using ih r hr
          | some p =>
            obtain ⟨ψ, s⟩ := p
            simpa only [CNF.parseClauses, hc, hp] using ih r hr

/-- The syntax machine's bit is exactly the audited parser's success bit. -/
private lemma taut_syntax_parse (x : List Bool) :
    tautSyntaxAccept .formula x = (CNF.parse x).isSome := by
  rw [taut_syntax_formula x.length x (Nat.le_refl _)]
  unfold CNF.parse
  cases CNF.parseClauses x.length x with
  | none => rfl
  | some p => obtain ⟨φ, r⟩ := p; cases r <;> rfl

open Turing

/-- Evaluation control stores only a conjunction accumulator. A satisfied
term rejects the complement; exhausting all failed terms accepts it. -/
private inductive TautEval where
  | formula | clause (c : Bool) | unary (c : Bool) | polarity (c : Bool)

/-- Evaluation-state equality stays private. -/
private instance tautEvalDecidableEq : DecidableEq TautEval :=
  (proxy_equiv% TautEval).symm.decidableEq

/-- The evaluation controller is finite. -/
private instance tautEvalFintype : Fintype TautEval := derive_fintype% _

/-- Separate syntax, certificate-copy, rewind, evaluation, and verdict phases.
Each paired formula bit is read in two transitions. Only `verdict` emits. -/
private inductive TautControl where
  | syntaxFirst (q : TautSyntax) | syntaxSecond (q : TautSyntax) (b : Bool)
  | copy | copyBack | rewindStart | rewind
  | evalFirst (q : TautEval) | evalSecond (q : TautEval) (b : Bool)
  | evalBack (c : Bool) | verdict (b : Bool)

/-- Whole-controller equality stays private. The local synthesis allowance
accommodates the ten-constructor sum representation; it changes no semantics. -/
private instance tautControlDecidableEq : DecidableEq TautControl := by
  set_option synthInstance.maxSize 4096 in
    exact (proxy_equiv% TautControl).symm.decidableEq

/-- The complete verifier control is finite, with no input-sized state. -/
private instance tautControlFintype : Fintype TautControl := derive_fintype% _

/-- A silent movement of the native head and the single certificate head. -/
private def tautMove (d e : SignType) (q : TautControl) : Action 1 Bool TautControl :=
  ⟨d, fun _ => (none, e), none, some q⟩

/-- Processing a decoded formula bit. The first unary bit leaves the
certificate head at zero; each additional unary bit advances it once.
After the polarity comparison the head returns to the left blank, then zero. -/
private def tautEvalAction (q : TautEval) (b : Bool) (w : Option Bool) :
    Action 1 Bool TautControl :=
  match q, b with
  | .formula, true => tautMove 1 0 (.evalFirst (.clause true))
  | .formula, false => tautMove 1 0 (.verdict true)
  | .clause c, true => tautMove 1 0 (.evalFirst (.unary c))
  | .clause c, false => tautMove 1 0 (if c then .verdict false else .evalFirst .formula)
  | .unary c, true => tautMove 1 1 (.evalFirst (.unary c))
  | .unary c, false => tautMove 1 0 (.evalFirst (.polarity c))
  | .polarity c, b => tautMove 1 (-1) (.evalBack (c && (w.getD false == b)))

/-- The independent native falsifying-assignment machine. It is used on the
constructed output of P10: either `[]` or `pairEncode x u` with
`|u| = |x|+1`. Syntax is validated completely before any assignment bit is
read. On a malformed formula the machine accepts without evaluating it;
on a valid formula it copies the certificate, rewinds, and evaluates.
All transitions before the final verdict have empty physical output. -/
private def tautTM : FinTM Bool where
  k := 1
  State := TautControl
  tm := { q₀ := .syntaxFirst .formula, tr := fun q inp w =>
    match q with
    | .syntaxFirst s => match inp with
      | some b => tautMove 1 0 (.syntaxSecond s b)
      | none => tautMove 0 0 (.verdict false)
    | .syntaxSecond s b => match inp with
      | some b' =>
        if b = b' then tautMove 1 0 (.syntaxFirst (tautSyntaxStep s b))
        else if b then tautMove 0 0 (.verdict false)
        else tautMove 1 0 (if s = .done then .copy else .verdict true)
      | none => tautMove 0 0 (.verdict false)
    | .copy => match inp with
      | some b => ⟨1, fun _ => (some (some b), 1), none, some .copy⟩
      | none => tautMove 0 (-1) .copyBack
    | .copyBack => match w 0 with
      | some _ => tautMove 0 (-1) .copyBack
      | none => tautMove 0 1 .rewindStart
    | .rewindStart => tautMove (-1) 0 .rewind
    | .rewind => match inp with
      | some _ => tautMove (-1) 0 .rewind
      | none => tautMove 1 0 (.evalFirst .formula)
    | .evalFirst s => match inp with
      | some b => tautMove 1 0 (.evalSecond s b)
      | none => tautMove 0 0 (.verdict false)
    | .evalSecond s b => tautEvalAction s b (w 0)
    | .evalBack c => match w 0 with
      | some _ => tautMove 0 (-1) (.evalBack c)
      | none => tautMove 0 1 (.evalFirst (.clause c))
    | .verdict b => ⟨0, fun _ => (none, 0), some b, none⟩ }

/-- Indexed configurations use an exact certificate word and an integer head;
the native position is one plus the number of consumed input bits. -/
private def tautCfg (x : List Bool) (q : Option TautControl)
    (i : ℕ) (hi : i ≤ x.length) (u : List Bool) (h : ℤ) (out : List Bool := []) :
    Cfg 1 Bool TautControl x :=
  ⟨q, ⟨i+1, by omega⟩, fun _ => FinTM.bufferTape u, fun _ => h, out⟩

/-- Exact native input lookup at an indexed configuration. -/
private lemma taut_read (x : List Bool) (q : Option TautControl)
    (i : ℕ) (hi : i ≤ x.length) (u : List Bool) (h : ℤ) (out : List Bool) :
    (tautCfg x q i hi u h out).inputSymbol = x[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- A silent right move advances the native index and the prescribed work
head while preserving both the stored word and the output. -/
private lemma taut_move_right (x : List Bool) (q : Option TautControl)
    (q' : TautControl) (i : ℕ) (hi : i+1 ≤ x.length)
    (u : List Bool) (h : ℤ) (out : List Bool) (e : SignType) :
    (tautMove 1 e q').apply (tautCfg x q i (by omega) u h out) =
      tautCfg x (some q') (i+1) hi u (h + (e : ℤ)) out := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by dsimp [tautCfg]; omega)
  · rfl
  · rfl
  · simp [tautMove, Action.apply, tautCfg]

/-- A stationary native transition can move the work head silently. -/
private lemma taut_move_stay (x : List Bool) (q : Option TautControl)
    (q' : TautControl) (i : ℕ) (hi : i ≤ x.length)
    (u : List Bool) (h : ℤ) (out : List Bool) (e : SignType) :
    (tautMove 0 e q').apply (tautCfg x q i hi u h out) =
      tautCfg x (some q') i hi u (h + (e : ℤ)) out := by
  apply Cfg.ext <;> simp [tautMove, Action.apply, tautCfg]

/-- Two equal native bits implement exactly one syntax step. -/
private lemma taut_syntax_double (x : List Bool) (s : TautSyntax) (i : ℕ)
    (hi : i+2 ≤ x.length) (b : Bool)
    (h₀ : x[i]? = some b) (h₁ : x[i+1]? = some b) :
    tautTM.tm.runFrom (tautCfg x (some (.syntaxFirst s)) i (by omega) [] 0) 2 =
      tautCfg x (some (.syntaxFirst (tautSyntaxStep s b))) (i+2) hi [] 0 := by
  have hs : tautTM.tm.step (tautCfg x (some (.syntaxFirst s)) i (by omega) [] 0) =
      tautCfg x (some (.syntaxSecond s b)) (i+1) (by omega) [] 0 := by
    change (tautTM.tm.tr (.syntaxFirst s) _ _).apply _ = _
    rw [taut_read, h₀]
    exact taut_move_right x _ _ i (by omega) [] 0 [] 0
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tautTM.tm.tr (.syntaxSecond s b) _ _).apply _ = _
  rw [taut_read, h₁]
  simp only [tautTM]
  exact taut_move_right x _ _ (i+1) hi [] 0 [] 0

/-- The pair separator finishes the syntax pass. Only the exact terminal
syntax state proceeds to certificate copying; every other state accepts
the malformed formula. -/
private lemma taut_syntax_separator (x : List Bool) (s : TautSyntax) (i : ℕ)
    (hi : i+2 ≤ x.length) (h₀ : x[i]? = some false) (h₁ : x[i+1]? = some true) :
    tautTM.tm.runFrom (tautCfg x (some (.syntaxFirst s)) i (by omega) [] 0) 2 =
      tautCfg x (some (if s = .done then .copy else .verdict true)) (i+2) hi [] 0 := by
  have hs : tautTM.tm.step (tautCfg x (some (.syntaxFirst s)) i (by omega) [] 0) =
      tautCfg x (some (.syntaxSecond s false)) (i+1) (by omega) [] 0 := by
    change (tautTM.tm.tr (.syntaxFirst s) _ _).apply _ = _
    rw [taut_read, h₀]
    exact taut_move_right x _ _ i (by omega) [] 0 [] 0
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tautTM.tm.tr (.syntaxSecond s false) _ _).apply _ = _
  rw [taut_read, h₁]
  exact taut_move_right x _ _ (i+1) hi [] 0 [] 0

/-- A whole doubled formula prefix is scanned in exactly twice its length
plus the two separator steps. The work tape and physical output stay empty.

**Proof sketch.** Induct on the unconsumed formula bits, accumulating their
syntax state and an arbitrary already-consumed native prefix. The final
separator distinguishes exact syntax success from every malformed case. -/
private lemma taut_syntax_run (a u : List Bool) :
    ∀ (x pre : List Bool) (s : TautSyntax) (hx : x = pre ++ pairEncode a u),
    tautTM.tm.runFrom
      (tautCfg x (some (.syntaxFirst s)) pre.length (by simp [hx, pairEncode]) [] 0)
      (2*a.length+2) =
    tautCfg x
      (some (if a.foldl tautSyntaxStep s = .done then .copy else .verdict true))
      (pre.length+2*a.length+2) (by simp [hx, universal_pair_length]; omega) [] 0 := by
  induction a with
  | nil =>
    intro x pre s hx
    simpa using taut_syntax_separator x s pre.length (by simp [hx, pairEncode])
      (by simp [hx, pairEncode]) (by simp [hx, pairEncode])
  | cons b a ih =>
    intro x pre s hx
    have hx' : x = (pre ++ [b,b]) ++ pairEncode a u := by
      simpa [pairEncode, List.append_assoc] using hx
    have hs := taut_syntax_double x s pre.length
      (by simp [hx', List.length_append]) b
      (by simp [hx', List.append_assoc]) (by simp [hx', List.append_assoc])
    conv_lhs => arg 2; rw [show 2*(b::a).length+2 = 2+(2*a.length+2) by simp; omega]
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [List.foldl_cons, List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_add, Nat.mul_one, Nat.reduceAdd] using
      ih x (pre ++ [b,b]) (tautSyntaxStep s b) hx'

/-- The machine's real initial configuration is the empty indexed one. -/
private lemma taut_init (x : List Bool) : tautTM.tm.initCfg x =
    tautCfg x (some (.syntaxFirst .formula)) 0 (Nat.zero_le _) [] 0 := by
  apply Cfg.ext <;> simp [tautTM, tautCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The unique output transition appends the single verdict and halts. -/
private lemma taut_verdict (x : List Bool) (b : Bool) (i : ℕ) (hi : i ≤ x.length)
    (u : List Bool) (h : ℤ) :
    tautTM.tm.step (tautCfg x (some (.verdict b)) i hi u h) =
      tautCfg x none i hi u h [b] := by
  apply Cfg.ext <;> simp [tautTM, tautCfg, MultiTapeTM.step, Action.apply]

/-- Parse failure has a complete native accepting run, after the syntax pass
and before any semantic phase, for every certificate. -/
private lemma taut_machine_malformed (x u : List Bool) (hx : CNF.parse x = none) :
    tautTM.ComputesInTime (pairEncode x u) [true] (2*x.length+3) := by
  have hp := taut_syntax_parse x
  rw [hx] at hp
  have hn : x.foldl tautSyntaxStep .formula ≠ .done := by
    intro h
    simp [tautSyntaxAccept, h] at hp
  have hs := taut_syntax_run x u (pairEncode x u) [] .formula rfl
  simp only [List.length_nil, Nat.zero_add, if_neg hn] at hs
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  rw [show 2*x.length+3 = (2*x.length+2)+1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', taut_init, hs, taut_verdict]
  exact ⟨rfl, rfl⟩

/-- The failed split's empty output is explicitly rejected in two steps. -/
private lemma taut_machine_empty : tautTM.ComputesInTime [] [false] 2 := by
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  decide

/-- Copying the certificate preserves exactly its scanned prefix and emits
nothing. Both heads advance once per copied bit. -/
private lemma taut_copy_run (x pre u : List Bool) (hx : x = pre ++ u) :
    ∀ j (hj : j ≤ u.length),
    tautTM.tm.runFrom
      (tautCfg x (some .copy) pre.length (by simp [hx]) [] 0) j =
    tautCfg x (some .copy) (pre.length+j) (by simp [hx]; omega) (u.take j) j := by
  intro j
  induction j with
  | zero => intro hj; simp [tautCfg]
  | succ j ih =>
    intro hj
    have hj' : j < u.length := by omega
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change (tautTM.tm.tr .copy _ _).apply _ = _
    rw [taut_read]
    have hr : x[pre.length+j]? = some u[j] := by
      simp only [hx, List.getElem?_append_right (by omega : pre.length ≤ pre.length+j),
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj']
    rw [hr]
    change (⟨1, fun _ => (some (some u[j]), 1), none, some .copy⟩ :
      Action 1 Bool TautControl).apply _ = _
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tautCfg]; simp only [hx, List.length_append]; omega)
    · funext k
      simp only [Action.apply, tautCfg, List.take_succ, List.getElem?_eq_getElem hj',
        FinTM.bufferTape_append, Option.toList_some]
      congr 1
      simp [Nat.le_of_lt hj']
    · funext k; simp [Action.apply, tautCfg]
    · rfl

/-- Rewind a contiguous certificate to its left blank and return to cell
zero, preserving all data and output.

**Proof sketch.** Starting one cell before position `n`, each of the `n`
nonblank cells costs one left move; the final blank costs one right move.
The bound is worst-case per call, with no amortization assumption. -/
private lemma taut_work_rewind (q dest : TautControl)
    (htr : ∀ (inp : Option Bool) (w : Fin 1 → Option Bool), tautTM.tm.tr q inp w =
      match w 0 with
      | some _ => tautMove 0 (-1) q
      | none => tautMove 0 1 dest)
    (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (u : List Bool) :
    ∀ n (_hn : n ≤ u.length),
    tautTM.tm.runFrom (tautCfg x (some q) i hi u ((n : ℤ)-1)) (n+1) =
      tautCfg x (some dest) i hi u 0 := by
  intro n
  induction n with
  | zero =>
    intro _hn
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (tautTM.tm.tr q _ _).apply _ = _
    rw [htr]
    have hw : (tautCfg x (some q) i hi u ((0 : ℕ)-1 : ℤ)).workTapeSymbols 0 = none := by
      simp [Cfg.workTapeSymbols, tautCfg]
    rw [hw]
    simpa only [Nat.cast_zero, zero_sub, SignType.coe_one, neg_add_cancel] using
      taut_move_stay x (some q) dest i hi u (-1) [] 1
  | succ n ih =>
    intro hn
    have hn' : n < u.length := by omega
    have hs : tautTM.tm.step (tautCfg x (some q) i hi u (((n+1 : ℕ) : ℤ)-1)) =
        tautCfg x (some q) i hi u ((n : ℤ)-1) := by
      change (tautTM.tm.tr q _ _).apply _ = _
      rw [htr]
      have hw : (tautCfg x (some q) i hi u (((n+1 : ℕ) : ℤ)-1)).workTapeSymbols 0 =
          some u[n] := by
        simp [Cfg.workTapeSymbols, tautCfg, List.getElem?_eq_getElem hn']
      rw [hw]
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        SignType.coe_neg, SignType.coe_one, sub_eq_add_neg, add_neg_cancel_right] using
        taut_move_stay x (some q) q i hi u n [] (-1)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- After a successful syntax pass, copy and rewind install the exact
certificate at the evaluation entry, with empty physical output.

**Proof sketch.** Compose the exact syntax and copy runs, one transition
to the last copied cell, the bounded work rewind, and the audited native
input rewind. Charge every phase at its own actual configuration and input
length; no time function is evaluated at an inflated composition bound. -/
private lemma taut_evaluation_start (x u : List Bool) (hx : (CNF.parse x).isSome = true) :
    ∃ t ≤ 4*((pairEncode x u).length+2),
      tautTM.tm.runFrom (tautTM.tm.initCfg (pairEncode x u)) t =
        tautCfg (pairEncode x u) (some (.evalFirst .formula)) 0 (Nat.zero_le _) u 0 := by
  let z := pairEncode x u
  let pre := (x.flatMap fun b => [b,b]) ++ [false,true]
  have hz : z = pre ++ u := rfl
  have hpre : pre.length = 2*x.length+2 := by
    simpa [pre, pairEncode] using universal_pair_length x ([] : List Bool)
  have hlen : z.length = pre.length + u.length := by rw [hz, List.length_append]
  have hgood : x.foldl tautSyntaxStep .formula = .done := by
    have hp := taut_syntax_parse x
    rw [hx] at hp
    exact of_decide_eq_true hp
  have hs := taut_syntax_run x u z [] .formula rfl
  simp only [List.length_nil, Nat.zero_add, if_pos hgood] at hs
  have hc := taut_copy_run z pre u hz u.length (Nat.le_refl _)
  simp only [List.take_length] at hc
  have hcopy : tautTM.tm.runFrom (tautTM.tm.initCfg z)
      (2*x.length+2+u.length) =
      tautCfg z (some .copy) z.length (Nat.le_refl _) u u.length := by
    rw [MultiTapeTM.runFrom_add, taut_init, hs]
    simpa only [hpre, z, universal_pair_length] using hc
  have hback : tautTM.tm.step (tautCfg z (some .copy) z.length (Nat.le_refl _) u u.length) =
      tautCfg z (some .copyBack) z.length (Nat.le_refl _) u ((u.length : ℤ)-1) := by
    change (tautTM.tm.tr .copy _ _).apply _ = _
    rw [taut_read, List.getElem?_length]
    simpa [sub_eq_add_neg] using taut_move_stay z (some .copy) .copyBack z.length
      (Nat.le_refl _) u u.length [] (-1)
  have hw := taut_work_rewind .copyBack .rewindStart (by intros; rfl)
    z z.length (Nat.le_refl _) u u.length (Nat.le_refl _)
  obtain ⟨r, hr, hrew⟩ := FinTM.timed_rewind tautTM.tm .rewindStart .rewind
    (some (.evalFirst .formula)) (by intros; rfl)
    (by intro inp w; cases inp <;> rfl)
    (tautCfg z (some .rewindStart) z.length (Nat.le_refl _) u 0) rfl
  have hstart : tautTM.tm.runFrom (tautTM.tm.initCfg z)
      (2*x.length+2+u.length+1) =
      tautCfg z (some .copyBack) z.length (Nat.le_refl _) u ((u.length : ℤ)-1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcopy, hback]
  have hnext : tautTM.tm.runFrom (tautTM.tm.initCfg z)
      ((2*x.length+2+u.length+1)+(u.length+1)) =
      tautCfg z (some .rewindStart) z.length (Nat.le_refl _) u 0 := by
    rw [MultiTapeTM.runFrom_add, hstart, hw]
  refine ⟨(2*x.length+2+u.length+1)+(u.length+1)+r, ?_, ?_⟩
  · dsimp only [tautCfg] at hr
    dsimp only [z]
    rw [universal_pair_length]
    have hzlen := universal_pair_length x u
    dsimp only [z] at hr
    rw [hzlen] at hr
    omega
  · rw [MultiTapeTM.runFrom_add, hnext, hrew]
    rfl

/-- Two native cells process one decoded evaluation bit, with its prescribed
silent work-head move. The second cell is a duplicate on the constructed
pair inputs used below. -/
private lemma taut_eval_double (x : List Bool) (q : TautEval) (q' : TautControl)
    (i : ℕ) (hi : i+2 ≤ x.length) (u : List Bool) (h : ℤ) (b : Bool) (e : SignType)
    (hr : x[i]? = some b)
    (ha : tautEvalAction q b (FinTM.bufferTape u h) = tautMove 1 e q') :
    tautTM.tm.runFrom (tautCfg x (some (.evalFirst q)) i (by omega) u h) 2 =
      tautCfg x (some q') (i+2) hi u (h+(e : ℤ)) := by
  have hs : tautTM.tm.step (tautCfg x (some (.evalFirst q)) i (by omega) u h) =
      tautCfg x (some (.evalSecond q b)) (i+1) (by omega) u h := by
    change (tautTM.tm.tr (.evalFirst q) _ _).apply _ = _
    rw [taut_read, hr]
    simpa only [SignType.coe_zero, add_zero] using
      taut_move_right x _ _ i (by omega) u h [] 0
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tautEvalAction q b (FinTM.bufferTape u h)).apply _ = _
  rw [ha]
  exact taut_move_right x _ _ (i+1) hi u h [] e

/-- Paired concatenation retains the native suffix after the doubled prefix. -/
private lemma taut_pair_append (a b u : List Bool) :
    pairEncode (a ++ b) u = (a.flatMap fun v => [v,v]) ++ pairEncode b u := by
  simp [pairEncode, List.flatMap_append, List.append_assoc]

/-- The doubled prefix has precisely twice its original length. -/
private lemma taut_double_length (a : List Bool) :
    (a.flatMap fun v => [v,v]).length = 2*a.length := by
  have h := universal_pair_length a ([] : List Bool)
  simp only [pairEncode, List.length_append, List.length_cons, List.length_nil] at h
  omega

/-- Each additional unary-index bit advances the certificate head once.
Native input and certificate head movement are synchronized, with no random
access hidden in the time accounting. -/
private lemma taut_unary_run (k : ℕ) (r u : List Bool) :
    ∀ (x pre : List Bool) (c : Bool) (h : ℤ)
      (hx : x = pre ++ pairEncode (List.replicate k true ++ r) u),
    tautTM.tm.runFrom
      (tautCfg x (some (.evalFirst (.unary c))) pre.length
        (by simp [hx, universal_pair_length]) u h) (2*k) =
      tautCfg x (some (.evalFirst (.unary c))) (pre.length+2*k)
        (by simp [hx, universal_pair_length]; omega) u (h+k) := by
  induction k with
  | zero => intro x pre c h hx; simp
  | succ k ih =>
    intro x pre c h hx
    have hx' : x = (pre ++ [true,true]) ++ pairEncode (List.replicate k true ++ r) u := by
      simpa [List.replicate_succ, pairEncode, List.append_assoc] using hx
    have hs := taut_eval_double x (.unary c) (.evalFirst (.unary c)) pre.length
      (by simp [hx', List.length_append]) u h true 1
      (by simp [hx', List.append_assoc]) rfl
    conv_lhs => arg 2; rw [show 2*(k+1) = 2+2*k by omega]
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.zero_add, Nat.mul_add, Nat.mul_one, Nat.reduceAdd, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.cast_add, Nat.cast_one, SignType.coe_one,
      add_assoc, add_comm, add_left_comm] using ih x (pre ++ [true,true]) c (h+1) hx'

/-- One complete serialized literal has an exact native run. The time is
`3*v+7`: two steps per serialized bit, and `v+1` steps to reset the
certificate head after comparing its `v`-th bit with the polarity.

**Proof sketch.** Read the first unary bit without moving the certificate
head, walk over the remaining unary bits, read the delimiter and polarity,
then apply the work-rewind lemma. The certificate bound guarantees the
entire rewind interval is nonblank. -/
private lemma taut_literal_run (ℓ : Std.Sat.Literal ℕ) (r u : List Bool)
    (hu : ℓ.1 < u.length) (x pre : List Bool) (c : Bool)
    (hx : x = pre ++ pairEncode (CNF.serializeLit ℓ ++ r) u) :
    tautTM.tm.runFrom
      (tautCfg x (some (.evalFirst (.clause c))) pre.length
        (by simp [hx, universal_pair_length]) u 0) (3*ℓ.1+7) =
      tautCfg x (some (.evalFirst (.clause (c && (tautAssignment u ℓ.1 == ℓ.2)))))
        (pre.length+2*(CNF.serializeLit ℓ).length)
        (by simp [hx, universal_pair_length]; omega) u 0 := by
  let pre₁ := pre ++ [true,true]
  let pre₂ := pre₁ ++ (List.replicate ℓ.1 true).flatMap (fun b => [b,b])
  let pre₃ := pre₂ ++ [false,false]
  have hx₁ : x = pre₁ ++ pairEncode (List.replicate ℓ.1 true ++ false :: ℓ.2 :: r) u := by
    simpa [pre₁, CNF.serializeLit, List.replicate_succ, pairEncode, List.append_assoc] using hx
  have hx₂ : x = pre₂ ++ pairEncode (false :: ℓ.2 :: r) u := by
    simpa only [taut_pair_append, List.append_assoc, pre₂] using hx₁
  have hx₃ : x = pre₃ ++ pairEncode (ℓ.2 :: r) u := by
    simpa [pre₃, pairEncode, List.append_assoc] using hx₂
  have hp₁ : pre₁.length = pre.length+2 := by simp [pre₁]
  have hp₂ : pre₂.length = pre.length+2+2*ℓ.1 := by
    simp only [pre₂, List.length_append, taut_double_length, List.length_replicate, hp₁]
  have hp₃ : pre₃.length = pre.length+2+2*ℓ.1+2 := by simp [pre₃, hp₂]
  have hs₁ := taut_eval_double x (.clause c) (.evalFirst (.unary c)) pre.length
    (by simp [hx₁, pre₁]) u 0 true 0
    (by simp [hx₁, pre₁, List.append_assoc]) rfl
  have hs₂ := taut_unary_run ℓ.1 (false :: ℓ.2 :: r) u x pre₁ c 0 hx₁
  have hs₃ := taut_eval_double x (.unary c) (.evalFirst (.polarity c)) pre₂.length
    (by simp [hx₂, universal_pair_length] ; omega) u ℓ.1 false 0
    (by simp [hx₂, pairEncode]) rfl
  have hs₄ := taut_eval_double x (.polarity c)
    (.evalBack (c && (tautAssignment u ℓ.1 == ℓ.2))) pre₃.length
    (by simp [hx₃, universal_pair_length] ; omega) u ℓ.1 ℓ.2 (-1)
    (by simp [hx₃, pairEncode])
    (by simp only [tautEvalAction, FinTM.bufferTape_nat, tautAssignment,
      List.getD_eq_getElem?_getD])
  have hs₅ := taut_work_rewind
    (.evalBack (c && (tautAssignment u ℓ.1 == ℓ.2)))
    (.evalFirst (.clause (c && (tautAssignment u ℓ.1 == ℓ.2))))
    (by intros; rfl) x (pre₃.length+2)
    (by simp [hx₃, universal_pair_length] ; omega) u ℓ.1 (Nat.le_of_lt hu)
  have h₂ : tautTM.tm.runFrom
      (tautCfg x (some (.evalFirst (.clause c))) pre.length
        (by simp [hx, universal_pair_length]) u 0) (2+2*ℓ.1) =
      tautCfg x (some (.evalFirst (.unary c))) pre₂.length
        (by simp [hx₂, universal_pair_length]) u ℓ.1 := by
    rw [MultiTapeTM.runFrom_add, hs₁]
    simpa only [hp₁, hp₂, SignType.coe_zero, zero_add] using hs₂
  have h₃ : tautTM.tm.runFrom
      (tautCfg x (some (.evalFirst (.clause c))) pre.length
        (by simp [hx, universal_pair_length]) u 0) (2+2*ℓ.1+2) =
      tautCfg x (some (.evalFirst (.polarity c))) pre₃.length
        (by simp [hx₃, universal_pair_length]) u ℓ.1 := by
    rw [MultiTapeTM.runFrom_add, h₂]
    simpa only [hp₂, hp₃, SignType.coe_zero, add_zero] using hs₃
  have h₄ : tautTM.tm.runFrom
      (tautCfg x (some (.evalFirst (.clause c))) pre.length
        (by simp [hx, universal_pair_length]) u 0) (2+2*ℓ.1+2+2) =
      tautCfg x (some (.evalBack (c && (tautAssignment u ℓ.1 == ℓ.2))))
        (pre₃.length+2) (by simp [hx₃, universal_pair_length] ; omega) u ((ℓ.1 : ℤ)-1) := by
    rw [MultiTapeTM.runFrom_add, h₃]
    simpa only [SignType.coe_neg_one, sub_eq_add_neg] using hs₄
  rw [show 3*ℓ.1+7 = (2+2*ℓ.1+2+2)+(ℓ.1+1) by omega,
    MultiTapeTM.runFrom_add, h₄, hs₅]
  apply Cfg.ext <;> simp [tautCfg, hp₃, CNF.serializeLit] ; omega

/-- A term scan computes the conjunction of all its literal values before
deciding whether to reject the complement or continue to the next term.
The empty term has value true and therefore rejects, as required.

**Proof sketch.** Induct on the term. Each literal has the exact run proved
above and restores the certificate head to zero; the final clause marker
uses the accumulated conjunction. The literal cost is bounded by three
times its serialized length, so the bound adds without hidden access costs. -/
private lemma taut_clause_run (C : CNF.Clause ℕ) (r u : List Bool)
    (hu : ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ (x pre : List Bool) (c : Bool)
      (hx : x = pre ++ pairEncode (CNF.serializeClause C ++ r) u),
    ∃ t ≤ 3*(CNF.serializeClause C).length,
      tautTM.tm.runFrom
        (tautCfg x (some (.evalFirst (.clause c))) pre.length
          (by simp [hx, universal_pair_length]) u 0) t =
      tautCfg x
        (some (if c && C.all (fun ℓ => tautAssignment u ℓ.1 == ℓ.2)
          then .verdict false else .evalFirst .formula))
        (pre.length+2*(CNF.serializeClause C).length)
        (by simp [hx, universal_pair_length]; omega) u 0 := by
  induction C with
  | nil =>
    intro x pre c hx
    have hz : x = pre ++ pairEncode (false :: r) u := by simpa [CNF.serializeClause] using hx
    have hs := taut_eval_double x (.clause c) (if c then .verdict false else .evalFirst .formula)
      pre.length (by simp [hz, universal_pair_length] ; omega) u 0 false 0
      (by simp [hz, pairEncode]) rfl
    refine ⟨2, by simp [CNF.serializeClause], ?_⟩
    simpa [CNF.serializeClause] using hs
  | cons ℓ C ih =>
    intro x pre c hx
    have hℓ := hu ℓ List.mem_cons_self
    have hC : ∀ l ∈ C, l.1 < u.length := fun l hl => hu l (List.mem_cons_of_mem ℓ hl)
    have hs : CNF.serializeClause (ℓ :: C) = CNF.serializeLit ℓ ++ CNF.serializeClause C := by
      simp [CNF.serializeClause, List.append_assoc]
    have hx' : x = pre ++ pairEncode (CNF.serializeLit ℓ ++ (CNF.serializeClause C ++ r)) u := by
      simpa only [hs, List.append_assoc] using hx
    let pre' := pre ++ (CNF.serializeLit ℓ).flatMap (fun b => [b,b])
    have hp : pre'.length = pre.length+2*(CNF.serializeLit ℓ).length := by
      simp only [pre', List.length_append, taut_double_length]
    have hx'' : x = pre' ++ pairEncode (CNF.serializeClause C ++ r) u := by
      simpa only [taut_pair_append, List.append_assoc, pre'] using hx'
    have hl := taut_literal_run ℓ (CNF.serializeClause C ++ r) u hℓ x pre c hx'
    obtain ⟨t, ht, hr⟩ := ih hC x pre' (c && (tautAssignment u ℓ.1 == ℓ.2)) hx''
    refine ⟨3*ℓ.1+7+t, ?_, ?_⟩
    · simp only [hs, List.length_append, CNF.serializeLit, List.length_replicate,
        List.length_cons, List.length_nil] at ⊢
      omega
    · rw [MultiTapeTM.runFrom_add, hl]
      simpa only [hp, hs, List.length_append, List.all_cons, Bool.and_assoc,
        Nat.mul_add, Nat.add_assoc] using hr

/-- The formula evaluation run halts with exactly the negated DNF value.

**Proof sketch.** The empty disjunction accepts. For a nonempty formula,
enter the first term and use the term-run contract. A true term ends with
the rejecting verdict; a false term restores the formula-entry state for
the induction hypothesis. Syntax has already been validated, so this
semantic short-circuit cannot hide malformed trailing input. -/
private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
    (hu : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ (x pre : List Bool) (hx : x = pre ++ pairEncode (CNF.serialize φ) u),
    ∃ t ≤ 3*(CNF.serialize φ).length+1, ∃ (i : ℕ) (hi : i ≤ x.length),
      tautTM.tm.runFrom
        (tautCfg x (some (.evalFirst .formula)) pre.length
          (by simp [hx, universal_pair_length]) u 0) t =
      tautCfg x none i hi u 0 [!(φ.evalDNF (tautAssignment u))] := by
  induction φ with
  | nil =>
    intro x pre hx
    have hz : x = pre ++ pairEncode [false] u := by simpa [CNF.serialize] using hx
    have hs := taut_eval_double x .formula (.verdict true) pre.length
      (by simp [hz, universal_pair_length] ; omega) u 0 false 0
      (by simp [hz, pairEncode]) rfl
    refine ⟨3, by simp [CNF.serialize], pre.length+2,
      by simp [hz, universal_pair_length] ; omega, ?_⟩
    rw [show 3 = 2+1 from rfl, MultiTapeTM.runFrom_succ_eq_step', hs]
    simpa only [SignType.coe_zero, zero_add] using taut_verdict x true (pre.length+2)
      (by simp [hz, universal_pair_length] ; omega) u 0
  | cons C φ ih =>
    intro x pre hx
    have hC := hu C List.mem_cons_self
    have hφ : ∀ D ∈ φ, ∀ ℓ ∈ D, ℓ.1 < u.length :=
      fun D hD => hu D (List.mem_cons_of_mem C hD)
    have hs : CNF.serialize (C :: φ) = true :: (CNF.serializeClause C ++ CNF.serialize φ) := by
      simp [CNF.serialize, List.append_assoc]
    let pre₁ := pre ++ [true,true]
    let pre₂ := pre₁ ++ (CNF.serializeClause C).flatMap (fun b => [b,b])
    have hp₁ : pre₁.length = pre.length+2 := by simp [pre₁]
    have hp₂ : pre₂.length = pre.length+2+2*(CNF.serializeClause C).length := by
      simp only [pre₂, List.length_append, taut_double_length, hp₁]
    have hx₁ : x = pre₁ ++ pairEncode (CNF.serializeClause C ++ CNF.serialize φ) u := by
      simpa [hs, pre₁, pairEncode, List.append_assoc] using hx
    have hx₂ : x = pre₂ ++ pairEncode (CNF.serialize φ) u := by
      simpa only [taut_pair_append, List.append_assoc, pre₂] using hx₁
    have hfirst := taut_eval_double x .formula (.evalFirst (.clause true)) pre.length
      (by simp [hx₁, pre₁]) u 0 true 0
      (by simp [hx₁, pre₁, List.append_assoc]) rfl
    obtain ⟨t, ht, hterm⟩ := taut_clause_run C (CNF.serialize φ) u hC x pre₁ true hx₁
    have hprefix : tautTM.tm.runFrom
        (tautCfg x (some (.evalFirst .formula)) pre.length
          (by simp [hx, universal_pair_length]) u 0) (2+t) =
        tautCfg x
          (some (if C.all (fun ℓ => tautAssignment u ℓ.1 == ℓ.2)
            then .verdict false else .evalFirst .formula)) pre₂.length
          (by simp [hx₂, universal_pair_length]) u 0 := by
      rw [MultiTapeTM.runFrom_add, hfirst]
      simpa only [hp₁, hp₂, Bool.true_and, SignType.coe_zero, zero_add] using hterm
    cases hv : C.all (fun ℓ => tautAssignment u ℓ.1 == ℓ.2) with
    | true =>
      simp only [hv, ↓reduceIte] at hprefix
      refine ⟨2+t+1, ?_, pre₂.length, by simp [hx₂, universal_pair_length], ?_⟩
      · simp only [hs, List.length_cons, List.length_append]
        omega
      · rw [MultiTapeTM.runFrom_succ_eq_step', hprefix, taut_verdict]
        delta CNF.evalDNF
        simp [hv]
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at hprefix
      obtain ⟨s, hs', i, hi, htail⟩ := ih hφ x pre₂ hx₂
      refine ⟨2+t+s, ?_, i, hi, ?_⟩
      · simp only [hs, List.length_cons, List.length_append]
        omega
      · rw [MultiTapeTM.runFrom_add, hprefix, htail]
        delta CNF.evalDNF
        simp [hv]

/-- Every member of the variable-contribution list is bounded by its maximum. -/
private lemma taut_le_max {n : ℕ} {s : List ℕ} (h : n ∈ s) : n ≤ s.foldr max 0 := by
  induction s with
  | nil => cases h
  | cons m s ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Every literal index is below the formula's declared variable bound. -/
private lemma taut_literal_lt {φ : CNF ℕ} {C : CNF.Clause ℕ} {ℓ : Std.Sat.Literal ℕ}
    (hC : C ∈ φ) (hℓ : ℓ ∈ C) : ℓ.1 < φ.numVars := by
  apply Nat.lt_of_succ_le
  apply taut_le_max
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩⟩

/-- The native verifier computes the negated decoded DNF on every correctly
sized pair, including parse failures, within a linear paired-input budget.

**Proof sketch.** On parse failure use the completed syntax-pass run. On
success reconstruct the exact serialization, establish that every literal
index fits inside the certificate, and compose the syntax/copy/rewind startup
with the formula run. Empty terms and the empty disjunction are covered by
the two structural base cases; only the final verdict emits a bit. -/
private lemma taut_machine_pair (x u : List Bool) (hu : u.length = x.length+1) :
    tautTM.ComputesInTime (pairEncode x u)
      [!((CNF.decode x).evalDNF (tautAssignment u))] (10*((pairEncode x u).length+1)) := by
  cases hp : CNF.parse x with
  | none =>
    have h := taut_machine_malformed x u hp
    have hm := h.mono (show 2*x.length+3 ≤ 10*((pairEncode x u).length+1) by
      rw [universal_pair_length]; omega)
    simpa only [CNF.decode, hp, Option.getD_none] using hm
  | some φ =>
    have hx := taut_parse_shape hp
    subst x
    have hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length := by
      intro C hC ℓ hℓ
      have hv := taut_literal_lt hC hℓ
      have hn := CNF.numVars_decode_le (CNF.serialize φ)
      rw [CNF.decode_serialize] at hn
      omega
    obtain ⟨a, ha, hstart⟩ := taut_evaluation_start (CNF.serialize φ) u
      (by simp [CNF.parse_serialize])
    obtain ⟨b, hb, i, hi, heval⟩ := taut_formula_run φ u hvars
      (pairEncode (CNF.serialize φ) u) [] rfl
    simp only [List.length_nil] at heval
    have hcomp : tautTM.ComputesInTime (pairEncode (CNF.serialize φ) u)
        [!(φ.evalDNF (tautAssignment u))] (a+b) := by
      apply (FinTM.computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hstart, heval]
      exact ⟨rfl, rfl⟩
    rw [CNF.decode_serialize]
    apply hcomp.mono
    rw [universal_pair_length] at ha ⊢
    omega

/-- The audited split primitive's exact string function. An even length has
no solution and produces the empty request, which the verifier rejects. -/
private def tautSplit (z : List Bool) : List Bool :=
  match solveSplit 1 1 z.length with
  | none => []
  | some i => pairEncode (z.take i) (z.drop i)

/-- Every output of the split primitive is handled by the native verifier,
with time charged to the original input length. -/
private lemma taut_machine_split (z : List Bool) :
    tautTM.ComputesInTime (tautSplit z) [tautVerifierBit z] (40*(z.length+1)) := by
  unfold tautSplit tautVerifierBit
  cases hs : solveSplit 1 1 z.length with
  | none => exact taut_machine_empty.mono (by omega)
  | some i =>
    have hi := taut_split_some z.length i hs
    have hib : i ≤ z.length := by omega
    have hu : (z.drop i).length = (z.take i).length+1 := by
      simp only [List.length_drop, List.length_take, Nat.min_eq_left hib]
      omega
    apply (taut_machine_pair (z.take i) (z.drop i) hu).mono
    rw [universal_pair_length]
    simp only [List.length_take, List.length_drop, Nat.min_eq_left hib]
    omega

/-- Quantitative buffered composition with a second-stage contract only on
the actual first-stage image (the proved epoch-2 TMSAT precedent).

**Proof sketch.** Capture the first stage's complete output, rewind it, and
relocate the second run through the public simulation contract. At most one
bit is captured per first-stage step. The second budget remains a function
of the original input, exactly as supplied by its image contract. -/
private lemma taut_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2*T₁ n+T₂ n+2) := by
  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
  intro x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a+T₂ x.length) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- The verifier is polynomial-time: P10's cubic split followed by the
linear syntax/evaluation machine, combined with buffered output.

**Proof sketch.** Let the library split constant be `A`. The image contract
costs at most `40*(n+1)`, and buffered composition costs at most
`2*A*(n+1)^3+40*(n+1)+2`, bounded by `(2*A+42)*(n+1)^3`.
The singleton output is exactly the verifier-language indicator. -/
private lemma taut_verifier_mem_P : tautVerifier ∈ P := by
  classical
  obtain ⟨S, A, hS⟩ := FinTM.computesFunInTime_splitSolve 1 1
  have hsplit : S.ComputesFunInTime tautSplit (fun n => A*(n+1)^3) := by
    convert hS using 1
    funext z
    unfold tautSplit
    cases solveSplit 1 1 z.length <;> rfl
  obtain ⟨N, hN⟩ := taut_comp_on_image S tautTM tautSplit (fun z => [tautVerifierBit z])
    (fun n => A*(n+1)^3) (fun n => 40*(n+1)) hsplit taut_machine_split
  have hind (z : List Bool) : MultiTapeTM.indicator tautVerifier z = tautVerifierBit z := by
    unfold MultiTapeTM.indicator
    split
    · rename_i h
      exact (show tautVerifierBit z = true from h).symm
    · rename_i h
      have hb : tautVerifierBit z ≠ true := h
      exact (Bool.eq_false_iff.mpr hb).symm
  refine mem_P_iff.mpr ⟨2*A+42, 3, N, fun z => ?_⟩
  change N.ComputesInTime z [MultiTapeTM.indicator tautVerifier z] _
  rw [hind]
  apply (hN z).mono
  have hlin : z.length+1 ≤ (z.length+1)^3 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos z.length)
      (show 1 ≤ 3 by omega)
  have hone : 1 ≤ (z.length+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  change 2*(A*(z.length+1)^3)+40*(z.length+1)+2 ≤ (2*A+42)*(z.length+1)^3
  calc
    _ ≤ 2*(A*(z.length+1)^3)+40*(z.length+1)^3+2*(z.length+1)^3 := by omega
    _ = _ := by ring

/-- **`TAUTOLOGY ∈ coNP`** [AB09, §2.6.1]: a falsifying assignment certifies
the complement.

**Proof sketch.** By the definition of `Complexity.coNP`, exhibit
`TAUTOLOGYᶜ ∈ NP`: `x ∈ TAUTOLOGYᶜ` iff some assignment falsifies the DNF
reading of `CNF.decode x`. Certificate parameters `(1, 1)` exactly as in
`Complexity.SAT_mem_NP` — a certificate of length `|x| + 1` carries the
assignment on the mentioned variables (`Std.Sat.CNF.numVars_decode_le`
bounds them by `|x|`; the evaluation-congruence bridge transfers to `evalDNF`
by the same mentioned-variable argument, a named obligation mirroring
`Complexity.eval_congr_of_lt_numVars`). The verifier machine reuses the
`SAT_mem_NP` obligations — odd-length split with explicit even rejection,
the shared parsing machine, the assignment walk — with the **dual**
evaluation loop: accept iff **every** term contains an unsatisfied literal,
i.e. evaluate `evalDNF` and answer its negation (an empty term forces
rejection, the empty formula forces acceptance — round-1 audit, finding 2,
correcting the drafted some-term phrasing) — and the buffered verdict. Malformed
strings: the fallback is not a DNF tautology, so they lie in `TAUTOLOGYᶜ`,
and the verifier accepts them with any certificate (`evalDNF` of `[]` is
`false` — consistent on both sides). -/
theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
  exact taut_membership_of_verifier taut_verifier_mem_P

/-- **Example 2.21** [AB09]: `TAUTOLOGY` is `coNP`-complete (DNF fragment).

**Proof sketch.** Membership is `Complexity.TAUTOLOGY_mem_coNP`. Hardness:
let `L ∈ coNP`, so `Lᶜ ∈ NP`, and `Complexity.SAT_NPHard` (Lemma 2.11)
supplies `f` with `z ∈ Lᶜ ↔ f z ∈ SAT`. Set
`g z := Std.Sat.CNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
the Cook-Levin output, take the De Morgan dual, re-serialize. Then for every
`z`: `z ∈ L` iff `f z ∉ SAT` iff `CNF.decode (f z)` is unsatisfiable iff its
dual is a DNF tautology (`Std.Sat.CNF.dnfTautology_dual_iff`) iff
`g z ∈ TAUTOLOGY` (`Std.Sat.CNF.decode_serialize` re-reads the emitted
string; the decode-dual-serialize round trip is exact on every string since
decoding is total). `Complexity.PolyTimeComputable g`: compose `f`'s machine
(`Complexity.PolyTimeComputable.comp`) with the parse-dual-serialize
transducer — the parsing machine and serializer shared with the Lemma-2.14
transform, the dual being a literal-polarity flip emitted in-stream (the
polarity bit is the last bit of each literal record). Conclude
`Complexity.coNPHard` and assemble `Complexity.coNPComplete`. -/
theorem TAUTOLOGY_coNPComplete : coNPComplete TAUTOLOGY := by
  sorry

end Complexity
