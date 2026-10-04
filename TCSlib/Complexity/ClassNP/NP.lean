/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class NP

[AB09, §2.1, Definition 2.1]: a language `L` is in `NP` when membership has
polynomial-length certificates verifiable in polynomial time — `x ∈ L` iff some
certificate `u` of the prescribed polynomial length makes the verifier accept.

## Design and deviations from [AB09]

* **The certificate length is an explicit polynomial formula**, exactly
  `C · (|x| + 1)^c` bits: the definition quantifies over the *coefficient and
  degree*, not over an abstract length function. This is the phase-1 audit's
  repair (findings 1-2, Argument A): a length function constrained only by a
  numerical bound can itself smuggle undecidable information through length
  arithmetic — certificate *content* never enters — putting every
  length-determined language in the class. An explicit formula is computable,
  monotone, and information-free by construction. The numerical helper
  `Complexity.PolyBound` survives for bound bookkeeping only; it never appears
  in a class definition.
* **The verifier is a language, not a machine.** We render "polynomial-time TM
  `M` with `M(x, u) = 1`" as membership of the concatenation `x ++ u` in a
  verifier language `V ∈ P` — reusing the audited Chapter-1 class. The phase-1
  audit certified this abstraction sound (finding 10): `V ∈ P` supplies one
  uniform total decider, and for a fixed length formula, `V`'s values off the
  constrained strings change no membership statement.
* **Pairing is concatenation in the exact-length form** ([AB09], footnote 4):
  the definition never splits `x ++ u` — the membership equivalence quantifies
  over `x` and `u` separately, and with the explicit formula, any consumer
  that must recover the split can (`n + n·formula` arithmetic is computable
  and `n ↦ n + C(n+1)^c` is strictly increasing). The **bounded-length**
  variant ([AB09, Exercise 2.1]) is different: with `∃ u, |u| ≤ …` and plain
  concatenation, the empty certificate forces `V ⊆ L`, which collapses every
  prefix-free language to its verifier (audit finding 2, Argument B) — so the
  bounded form below pairs its inputs with the audited self-delimiting
  `Turing.pairEncode` instead.
* **Certificates have length exactly `C(|x|+1)^c`** (Definition 2.1 verbatim,
  with the formula for [AB09]'s "polynomial `p`").

## Main definitions

* `Complexity.NP` — the class NP. [AB09, Definition 2.1]

## Main results

* `Complexity.P_subset_NP` — `P ⊆ NP` (empty certificates). [AB09, §2.1]
* `Complexity.mem_NP_iff_exists_length_le` — bounded-length *paired*
  certificates define the same class. [AB09, Exercise 2.1, repaired per the
  phase-1 audit]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1, Definition 2.1, pp. 39-41;
  Exercise 2.1.)
-/

namespace Complexity

open Turing

/-- **The class NP** [AB09, Definition 2.1]: `L ∈ NP` iff there are a certificate
coefficient `C`, degree `c`, and a polynomial-time-decidable verifier language
`V ∈ P` such that `x ∈ L` exactly when some certificate `u` of length exactly
`C · (|x| + 1)^c` makes the concatenation `x ++ u` a member of `V`. The
certificate length is an explicit formula in `|x|` — never an abstract
function — so it is computable and carries no information beyond `|x|`
(phase-1 audit, finding 1). -/
def NP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ NP`** [AB09, §2.1, after Definition 2.1]: a language decidable in
polynomial time is verifiable with empty certificates.

**Proof sketch.** Take `C = 0` (certificate length `0 · (n+1)^0 = 0`) and
`V = L`: the only certificate of length `0` is `[]`, and `x ++ [] = x`, so the
membership equivalence is the identity. The audit confirmed this covers
`L = ∅`, `L = univ`, and `x = []` (finding table, question 2). -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, 0, L, hL, fun x => ?_⟩
  simp only [zero_mul, List.length_eq_zero_iff, exists_eq_left, List.append_nil]


/-- Remove the last `true` marker and the following false suffix. No marker
means failure, so stripping cannot cross the certificate boundary. -/
private def stripCertificate : List Bool → Option (List Bool)
  | [] => none
  | b :: v => match stripCertificate v with
    | some u => some (b :: u)
    | none => if b then some [] else none

/-- An all-false certificate region contains no marker. -/
private lemma stripCertificate_false (k : ℕ) :
    stripCertificate (List.replicate k false) = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, stripCertificate, ih]

/-- Stripping a padded certificate recovers the original certificate, including
the empty certificate and certificates that themselves contain `true`. -/
private lemma stripCertificate_pad (u : List Bool) (k : ℕ) :
    stripCertificate (u ++ true :: List.replicate k false) = some u := by
  induction u with
  | nil => simp [stripCertificate, stripCertificate_false]
  | cons b u ih => simp [stripCertificate, ih]

/-- Successful stripping identifies precisely the last-true decomposition.

**Proof sketch.** Induct from the right through the recursive call. A marker in
the tail survives, with the head prepended; otherwise the head must be `true`
and the tail must be all false. The simultaneous no-marker assertion supplies
that latter fact. -/
private lemma stripCertificate_spec (v : List Bool) :
    (stripCertificate v = none ↔ v = List.replicate v.length false) ∧
    (∀ u, stripCertificate v = some u ↔
      ∃ k, v = u ++ true :: List.replicate k false) := by
  induction v with
  | nil => simp [stripCertificate]
  | cons b v ih =>
    cases hv : stripCertificate v with
    | none =>
      have hfalse := ih.1.mp hv
      constructor
      · constructor
        · intro h
          cases b with
          | false => simpa [List.replicate_succ] using congrArg (false :: ·) hfalse
          | true => simp [stripCertificate, hv] at h
        · intro h
          rw [h]
          exact stripCertificate_false _
      · intro u
        constructor
        · intro h
          cases b with
          | false => simp [stripCertificate, hv] at h
          | true =>
            have hu : u = [] := by simpa [stripCertificate, hv] using h.symm
            subst u
            exact ⟨v.length, by simpa using congrArg (true :: ·) hfalse⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j
    | some w =>
      obtain ⟨k, hk⟩ := (ih.2 w).mp hv
      constructor
      · constructor
        · simp [stripCertificate, hv]
        · intro heq
          have : stripCertificate (b :: v) = none := by
            rw [heq]; exact stripCertificate_false _
          simp [stripCertificate, hv] at this
      · intro u
        constructor
        · intro h
          have hu : b :: w = u := by simpa [stripCertificate, hv] using h
          subst u
          exact ⟨k, by simp [hk]⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j

/-- The padded total length is strictly increasing, even at degree zero. -/
private lemma certificateTotal_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + (C + 1) * (n + 1) ^ c) := by
  intro m n h
  dsimp only
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_of_lt h) 1) c
  have hmul := Nat.mul_le_mul_left (C + 1) hpow
  omega

/-- The repaired exact width leaves room for the mandatory marker. -/
private lemma certificate_room (C c n : ℕ) :
    C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ c := by
  have h := Nat.one_le_pow c (n + 1) (Nat.succ_pos n)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Bounded search for the unique legal split. Failure remains `none`. -/
private def certificateSplit (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? fun n => n + (C + 1) * (n + 1) ^ c == m

/-- The bounded search succeeds exactly at a solution of the length equation.

**Proof sketch.** Any solution is at most the total length, hence lies in the
search range. A failed search would reject that very solution; a successful
search returns a solution, and strict monotonicity makes it unique. -/
private lemma certificateSplit_spec (C c m n : ℕ) :
    certificateSplit C c m = some n ↔ n + (C + 1) * (n + 1) ^ c = m := by
  constructor
  · intro h
    have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) h
    simpa only [beq_iff_eq] using hh
  · intro h
    have hn : n ∈ List.range (m + 1) := by simp only [List.mem_range]; omega
    cases hs : certificateSplit C c m with
    | none =>
      have hf := (List.find?_eq_none.mp hs) n hn
      simp [h] at hf
    | some j =>
      have hj : j + (C + 1) * (j + 1) ^ c = m :=
        by
          have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) hs
          simpa only [beq_iff_eq] using hh
      have : j = n := (certificateTotal_strictMono C c).injective (hj.trans h.symm)
      simp [this]

/-- In particular the empty input has no legal split. -/
private lemma certificateSplit_zero (C c : ℕ) : certificateSplit C c 0 = none := by
  cases h : certificateSplit C c 0 with
  | none => rfl
  | some n =>
    have hn := (certificateSplit_spec C c 0 n).mp h
    have hr := certificate_room C c n
    omega

/-- The forward verifier parses the audited pairing, enforces the original
exact width, and consults the old verifier on the concatenated word. -/
private def pairedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ x u, pairDecode y = some (x, u) ∧
    u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- On an encoded pair, the forward verifier imposes exactly the prescribed
length test and the old verification condition. -/
private lemma pairedVerifier_pair (C c : ℕ) (V : Language Bool) (x u : List Bool) :
    pairEncode x u ∈ pairedVerifier C c V ↔
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := by
  change (∃ a b, pairDecode (pairEncode x u) = some (a, b) ∧
    b.length = C * (a.length + 1) ^ c ∧ a ++ b ∈ V) ↔ _
  simp [pairDecode_pairEncode]

/-- A malformed pair is rejected before consulting the old verifier. -/
private lemma pairedVerifier_malformed (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : pairDecode y = none) : y ∉ pairedVerifier C c V := by
  rintro ⟨x, u, hp, -⟩
  rw [h] at hp
  cases hp

/-- The reverse verifier rejects a missing length split or marker, rechecks the
original bound after stripping, and consults the old paired verifier. -/
private def paddedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ n u, certificateSplit C c y.length = some n ∧
    stripCertificate (y.drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode (y.take n) u ∈ V}

/-- A missing solution of the length equation is rejection, not a default
split. In particular this covers the empty input by `certificateSplit_zero`. -/
private lemma paddedVerifier_no_split (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : certificateSplit C c y.length = none) : y ∉ paddedVerifier C c V := by
  rintro ⟨n, u, hn, -⟩
  rw [h] at hn
  cases hn

/-- For the prescribed exact width the search recovers precisely the input
boundary; no marker in the input can be mistaken for a certificate marker. -/
private lemma paddedVerifier_append (C c : ℕ) (V : Language Bool) (x v : List Bool)
    (hv : v.length = (C + 1) * (x.length + 1) ^ c) :
    x ++ v ∈ paddedVerifier C c V ↔ ∃ u, stripCertificate v = some u ∧
      u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  have hs : certificateSplit C c (x ++ v).length = some x.length := by
    apply (certificateSplit_spec _ _ _ _).mpr
    simp only [List.length_append, hv]
  change (∃ n u, certificateSplit C c (x ++ v).length = some n ∧
    stripCertificate ((x ++ v).drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode ((x ++ v).take n) u ∈ V) ↔ _
  rw [hs]
  simp

/-- An all-false region is rejected even when the input itself contains true
bits: the strip function is applied only after the recovered boundary. -/
private lemma paddedVerifier_no_marker (C c : ℕ) (V : Language Bool) (x : List Bool) :
    x ++ List.replicate ((C + 1) * (x.length + 1) ^ c) false ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ (List.length_replicate ..)]
  simp only [stripCertificate_false, reduceCtorEq, false_and, exists_false, not_false_eq_true]

/-- Even a correctly marked certificate that fits in the enlarged exact
region is rejected if its stripped witness exceeds the original bound. -/
private lemma paddedVerifier_too_long (C c : ℕ) (V : Language Bool) (x u : List Bool)
    (k : ℕ) (hv : (u ++ true :: List.replicate k false).length =
      (C + 1) * (x.length + 1) ^ c) (hu : C * (x.length + 1) ^ c < u.length) :
    x ++ (u ++ true :: List.replicate k false) ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ hv]
  rintro ⟨u', hs, hu', -⟩
  rw [stripCertificate_pad] at hs
  have he : u = u' := Option.some.inj hs
  subst u'
  exact Nat.not_le_of_lt hu hu'

/-- Padding and stripping give the exact witness equivalence; the runtime
obligations are separate from this purely semantic statement. -/
private lemma paddedVerifier_witness (C c : ℕ) (V : Language Bool) (x : List Bool) :
    (∃ v, v.length = (C + 1) * (x.length + 1) ^ c ∧ x ++ v ∈ paddedVerifier C c V) ↔
    ∃ u, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨u, -, hu, hV⟩ := (paddedVerifier_append C c V x v hv).mp h
    exact ⟨u, hu, hV⟩
  · rintro ⟨u, hu, hV⟩
    let k := (C + 1) * (x.length + 1) ^ c - (u.length + 1)
    have hroom : u.length + 1 ≤ (C + 1) * (x.length + 1) ^ c :=
      (Nat.add_le_add_right hu 1).trans (certificate_room C c x.length)
    have hv : (u ++ true :: List.replicate k false).length =
        (C + 1) * (x.length + 1) ^ c := by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      dsimp [k]
      omega
    refine ⟨_, hv, (paddedVerifier_append C c V x _ hv).mpr ?_⟩
    exact ⟨u, stripCertificate_pad u k, hu, hV⟩


/-- A linear machine contract is already in the polynomial normal form. -/
private lemma verifier_poly_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime f (fun n => a * (n + 1))) : PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Fixed output words are polynomial-time computable. -/
private lemma verifier_poly_const (w : List Bool) :
    PolyTimeComputable (fun _ => w) :=
  verifier_poly_linear (FinTM.computesFunInTime_const w)

/-- A captured Boolean test selects one of two polynomial-time computations.

**Proof sketch.** The audited timed branch captures the test's complete output,
rewinds, and starts the selected branch on the same input. Enlarge the three
polynomial degrees to their maximum and absorb the final constant there. -/
private lemma verifier_poly_cond {p : List Bool → Bool}
    {f g : List Bool → List Bool}
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
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e := by
    exact max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Total first-component projection; malformed words produce the empty word. -/
private def verifier_fst (z : List Bool) : List Bool :=
  ((pairDecode z).map Prod.fst).getD []

/-- Total second-component projection; malformed words produce the empty word. -/
private def verifier_snd (z : List Bool) : List Bool :=
  ((pairDecode z).map Prod.snd).getD []

/-- The catalog's guarded pair-to-concatenation function. -/
private def verifier_concat (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => a ++ b
  | none => []

/-- The catalog's payload map retains the head and rejects malformed words. -/
private def verifier_map (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- The threaded map preserves polynomial time.

**Proof sketch.** Apply C1 with the monotone polynomial majorant. Degree `c+1`
dominates both the input scan and the payload computation, including `c=0`. -/
private lemma verifier_poly_map {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (verifier_map g) := by
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

/-- General pairing follows the audit's retained-request `H/s/t` recipe.

**Proof sketch.** First compute `H x = pairEncode (f x) []`, then retain the
whole input in `s x = pairEncode x (H x)`. Duplicate `s x` and map
`g ∘ pairFst` on its payload to obtain `t x = pairEncode (s x) (g x)`.
Concatenating this pair and extracting its second component yields exactly
`pairEncode (f x) (g x)`. Every payload map acts only on its own payload. -/
private lemma verifier_poly_pair {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
  have hdup := verifier_poly_linear FinTM.computesFunInTime_pairDup
  have hfst : PolyTimeComputable verifier_fst :=
    verifier_poly_linear FinTM.computesFunInTime_pairFst
  have hsnd : PolyTimeComputable verifier_snd :=
    verifier_poly_linear FinTM.computesFunInTime_pairSnd
  have hcat : PolyTimeComputable verifier_concat :=
    verifier_poly_linear FinTM.computesFunInTime_pairConcat
  have hH : PolyTimeComputable (fun x => pairEncode (f x) []) := by
    simpa only [Function.comp_def, verifier_map, pairDecode_pairEncode] using
      (verifier_poly_map (verifier_poly_const [])).comp (hdup.comp hf)
  have hs : PolyTimeComputable (fun x => pairEncode x (pairEncode (f x) [])) := by
    simpa only [Function.comp_def, verifier_map, pairDecode_pairEncode] using
      (verifier_poly_map hH).comp hdup
  have ht : PolyTimeComputable
      (fun x => pairEncode (pairEncode x (pairEncode (f x) [])) (g x)) := by
    simpa only [Function.comp_def, verifier_map, verifier_fst, pairDecode_pairEncode,
      Option.map_some, Option.getD_some] using
      (verifier_poly_map (hg.comp hfst)).comp (hdup.comp hs)
  convert hsnd.comp (hcat.comp ht) using 1
  funext x
  simp only [Function.comp_apply, verifier_concat, pairDecode_pairEncode]
  have heq : pairEncode x (pairEncode (f x) []) ++ g x =
      pairEncode x (pairEncode (f x) (g x)) := by
    simp only [pairEncode, List.append_nil, List.append_assoc]
  rw [heq]
  simp only [verifier_snd, pairDecode_pairEncode, Option.map_some, Option.getD_some]

/-- The two bounded searches are literally equal at the shifted coefficient. -/
private lemma verifier_split_bridge (C c : ℕ) :
    solveSplit (C + 1) c = certificateSplit C c := rfl

/-- The library's reverse scan implements the existing recursive strip spec.

**Proof sketch.** The semantic strip specification gives either an all-false
word or its last-true decomposition. Reversing that decomposition makes the
library scan discard exactly the false suffix and the marker. -/
private lemma verifier_strip_bridge : splitAtLastTrue = stripCertificate := by
  funext v
  cases hs : stripCertificate v with
  | none =>
    have hv := (stripCertificate_spec v).1.mp hs
    rw [hv]
    simp [splitAtLastTrue]
  | some u =>
    obtain ⟨k, hk⟩ := ((stripCertificate_spec v).2 u).mp hs
    rw [hk]
    simp [splitAtLastTrue]

/-- The original-bound test returns one Boolean, rejecting parse failures. -/
private def verifier_bound (C c : ℕ) (z : List Bool) : Bool :=
  match pairDecode z with
  | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ c)
  | none => false

/-- P8 supplies the timed original-bound test, with its parameters unchanged. -/
private lemma verifier_poly_bound (C c : ℕ) :
    PolyTimeComputable (fun z => [verifier_bound C c z]) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck C c
  exact ⟨M, a, c + 1, hM⟩

/-- Normalize a `P` decider through the audited capture-and-branch host.
The W3 controller uses `capture_run` to capture the old verifier's complete
singleton verdict, including an emission on its halting transition. -/
private lemma verifier_poly_indicator {V : Language Bool} (hV : V ∈ P) :
    PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp hV
  have h : PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := ⟨M, C, c, hM⟩
  have hc := verifier_poly_cond h (verifier_poly_const [true]) (verifier_poly_const [false])
  convert hc using 1
  funext x
  cases MultiTapeTM.indicator V x <;> rfl

/-- A polynomial-time singleton indicator is a polynomial-time decider. -/
private lemma verifier_mem_P {V : Language Bool}
    (h : PolyTimeComputable (fun x => [MultiTapeTM.indicator V x])) : V ∈ P := by
  obtain ⟨M, C, c, hM⟩ := h
  exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- The reverse length comparison uses general pairing and P8 at `(1,1)`.

**Proof sketch.** Generate `C(|a|+1)^c` in unary and prepend one bit. Pair the
old payload with this generated word. P8 then tests
`C(|a|+1)^c + 1 ≤ |b| + 1`, exactly the required reverse inequality. -/
private lemma verifier_poly_reverseBound (C c : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (C * ((verifier_fst z).length + 1) ^ c ≤ (verifier_snd z).length)]) := by
  have hfst : PolyTimeComputable verifier_fst :=
    verifier_poly_linear FinTM.computesFunInTime_pairFst
  have hsnd : PolyTimeComputable verifier_snd :=
    verifier_poly_linear FinTM.computesFunInTime_pairSnd
  obtain ⟨U, a, hU⟩ := FinTM.computesFunInTime_polyUnary C c
  have hgen : PolyTimeComputable (fun x => List.replicate (C * (x.length + 1) ^ c) true) :=
    ⟨U, a, c + 1, hU⟩
  have hpre := verifier_poly_linear (FinTM.computesFunInTime_prepend [true])
  have hpair := verifier_poly_pair hsnd (hpre.comp (hgen.comp hfst))
  simpa only [Function.comp_def, verifier_bound, pairDecode_pairEncode,
    List.singleton_append, List.length_cons, List.length_replicate, Nat.pow_one,
    Nat.one_mul, Nat.add_le_add_iff_right] using (verifier_poly_bound 1 1).comp hpair

/-- The forward verifier is decided by the guarded exact-width pipeline.

**Proof sketch.** Validate the pairing grammar, test both length inequalities,
concatenate the components, and capture the old decider's verdict. All branches
are timed catalog compositions; malformed words never reach the old verifier. -/
private lemma pairedVerifier_mem_P (C c : ℕ) {V : Language Bool} (hV : V ∈ P) :
    pairedVerifier C c V ∈ P := by
  classical
  have hfalse := verifier_poly_const [false]
  have hcat : PolyTimeComputable verifier_concat :=
    verifier_poly_linear FinTM.computesFunInTime_pairConcat
  have hrun := (verifier_poly_indicator hV).comp hcat
  have hreverse := verifier_poly_cond (verifier_poly_reverseBound C c) hrun hfalse
  have hwidth := verifier_poly_cond (verifier_poly_bound C c) hreverse hfalse
  have hfinal := verifier_poly_cond
    (verifier_poly_linear FinTM.computesFunInTime_pairValid) hwidth hfalse
  apply verifier_mem_P
  convert hfinal using 1
  funext y
  cases hy : pairDecode y with
  | none =>
    simp [hy, pairedVerifier, MultiTapeTM.indicator]
  | some p =>
    rcases p with ⟨x, u⟩
    by_cases hlo : u.length ≤ C * (x.length + 1) ^ c
    · by_cases hhi : C * (x.length + 1) ^ c ≤ u.length
      · have he := Nat.le_antisymm hlo hhi
        simp [hy, verifier_bound, verifier_fst, verifier_snd, verifier_concat,
          pairedVerifier, MultiTapeTM.indicator, he]
      · have he : u.length ≠ C * (x.length + 1) ^ c := fun h => hhi h.ge
        simp [hy, verifier_bound, verifier_fst, verifier_snd,
          pairedVerifier, MultiTapeTM.indicator, hlo, hhi, he]
    · have he : u.length ≠ C * (x.length + 1) ^ c := fun h => hlo h.le
      simp [hy, verifier_bound, pairedVerifier, MultiTapeTM.indicator, hlo, he]

/-- The shifted split machine retains the recovered input as the pair head. -/
private def verifier_split (C c : ℕ) (y : List Bool) : List Bool :=
  match solveSplit (C + 1) c y.length with
  | some n => pairEncode (y.take n) (y.drop n)
  | none => []

/-- Strip only the payload of a valid pair, retaining its original input. -/
private def verifier_strip (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, v) =>
    match splitAtLastTrue v with
    | some u => pairEncode a u
    | none => []
  | none => []

/-- The reverse verifier is decided by shifted split, marker, and bound guards.

**Proof sketch.** P10 at `(C+1,c)` recovers and retains the input prefix. A
grammar guard rejects its empty failure output. P9 strips only that pair's
payload; a second grammar guard rejects marker failure. P8 at the original
`(C,c)` rechecks the stripped witness before the captured old paired decider
runs. The search equation gives `n ≤ |y|`, so the retained prefix has exactly
length `n`; the two vocabulary bridges identify the original semantic spec. -/
private lemma paddedVerifier_mem_P (C c : ℕ) {V : Language Bool} (hV : V ∈ P) :
    paddedVerifier C c V ∈ P := by
  classical
  obtain ⟨S, a, hS⟩ := FinTM.computesFunInTime_splitSolve (C + 1) c
  have hsplit : PolyTimeComputable (verifier_split C c) := ⟨S, a, c + 2, hS⟩
  obtain ⟨T, b, hT⟩ := FinTM.computesFunInTime_stripLast
  have hstrip : PolyTimeComputable verifier_strip := ⟨T, b, 2, hT⟩
  have hvalid := verifier_poly_linear FinTM.computesFunInTime_pairValid
  have hfalse := verifier_poly_const [false]
  have hbound := verifier_poly_cond (verifier_poly_bound C c)
    (verifier_poly_indicator hV) hfalse
  have hmarked := verifier_poly_cond hvalid hbound hfalse
  have hfound := verifier_poly_cond hvalid (hmarked.comp hstrip) hfalse
  have hfinal := hfound.comp hsplit
  apply verifier_mem_P
  convert hfinal using 1
  funext y
  cases hs : certificateSplit C c y.length with
  | none =>
    simp [verifier_split, verifier_split_bridge, hs,
      pairDecode, paddedVerifier, MultiTapeTM.indicator]
  | some n =>
    have hn : n ≤ y.length := by
      have heq := (certificateSplit_spec C c y.length n).mp hs
      omega
    cases ht : stripCertificate (y.drop n) with
    | none =>
      simp [verifier_split, verifier_split_bridge, hs,
        verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
        pairDecode, paddedVerifier, MultiTapeTM.indicator]
    | some u =>
      by_cases hu : u.length ≤ C * (n + 1) ^ c
      · simp [verifier_split, verifier_split_bridge, hs,
          verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
          verifier_bound, List.length_take, Nat.min_eq_left hn,
          paddedVerifier, MultiTapeTM.indicator, hu]
      · simp [verifier_split, verifier_split_bridge, hs,
          verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
          verifier_bound, List.length_take, Nat.min_eq_left hn,
          paddedVerifier, MultiTapeTM.indicator, hu]

/-- **Bounded-length paired certificates define the same class**
[AB09, Exercise 2.1, repaired per the phase-1 audit]: `L ∈ NP` iff there are
`C`, `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V`. The bounded form pairs
`x` with `u` via the audited self-delimiting `Turing.pairEncode`: with plain
concatenation the empty certificate would force `V ⊆ L` and collapse every
prefix-free language (audit finding 2, Argument B).

**Proof sketch.** (⇒) From the exact form `(C, c, V)`, take the paired verifier
`V' := {pairEncode x u : |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` with the same bound:
deciding `V'` parses the aligned pair (the `Turing.pairDecode` grammar; a
polynomial-time scan), checks the length equality against the explicit formula,
reassembles `x ++ u`, and runs `V`'s decider — each a named machine obligation
for the fill, none exotic. (⇐) From the bounded form `(C, c, V)`, take exact
length `R n = (C+1)(n+1)^c` — **admissible** for the repaired `NP`
(coefficient `C+1`, degree `c`; the round-2 audit refuted the earlier choice
`C(n+1)^c + 1`, which is not of the class's required shape — round-2
finding 1) — leaving `R n - C(n+1)^c = (n+1)^c ≥ 1` room for the marker. Pad
each certificate right-self-delimitingly to `u ++ [true] ++ false-run` of
length `R n`. The new verifier, on `y` of length `m`: search `n ≤ m` for
`n + R n = m` — strict increase of `n ↦ n + R n` gives **at most one**
solution, and none may exist (e.g. `y = []`, since `R n ≥ 1`): **reject if no
such `n` exists** (round-3 audit, finding 1); otherwise split `y = x ++ v` at
that unique `n` with
`|v| = R n ≥ 1`; reject if `v` has no `true` bit (so stripping never enters
`x`); split `v = u ++ [true] ++ false-run` at the **last** `true`; check the
*original* bound `|u| ≤ C(n+1)^c` — checkable precisely because the bound is
the explicit formula (phase-1 finding 2's residual error, fixed in round 1) —
and consult `V` on `pairEncode x u`. Every old witness pads within `R n`
(`|u| + 1 ≤ C(n+1)^c + 1 ≤ R n`); every accepted new witness strips back to
an old one (the round-2 audit's reconstruction, checked there across the
`C = 0`, `c = 0`, `x = []`, `u = []`, all-`false`, and malformed edge
cases). -/
theorem mem_NP_iff_exists_length_le {L : Language Bool} :
    L ∈ NP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V  := by
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, pairedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: aligned parsing, the explicit polynomial
      -- length-equality test, concatenation, and timed execution of V's decider.
      exact pairedVerifier_mem_P C c hV
    · rw [hL x]
      constructor
      · rintro ⟨u, hu, hVu⟩
        exact ⟨u, hu.le, (pairedVerifier_pair C c V x u).mpr ⟨hu, hVu⟩⟩
      · rintro ⟨u, -, hVu⟩
        exact ⟨u, (pairedVerifier_pair C c V x u).mp hVu⟩
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C + 1, c, paddedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: bounded split search, last-true stripping,
      -- the original-bound test, pairing, and timed execution of V's decider.
      exact paddedVerifier_mem_P C c hV
    · exact (hL x).trans (paddedVerifier_witness C c V x).symm

end Complexity
