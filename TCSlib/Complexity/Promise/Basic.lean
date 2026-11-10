/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Promise problems

A promise problem is a pair of disjoint sets of strings, the yes-instances and the
no-instances; strings in neither set are outside the promise, and a decision procedure may
answer anything on them [Wat08, §II.1]. A language `L` is the promise problem `(L, Lᶜ)`.
Quantum complexity is naturally stated for promise problems: QMA and the local Hamiltonian
problem are promise classes (plan FD-7).

## Main definitions

* `Promise.Problem` — a promise problem: disjoint sets `yes` and `no` of binary strings.
* `Promise.ofLanguage L` — the language `L` as the promise problem `(L, Lᶜ)`.
* `Promise.Problem.IsTotal` — every string satisfies the promise.
* `Promise.InPromiseP` — the promise version of `P` [Wat08, §II.1].
* `Promise.InPromiseBPP E` — the promise version of `BPP`, relative to a verifier model `E`
  [Wat08, §II.1].

## Main results

* `Promise.ofLanguage_isTotal` — a language satisfies every promise.
* `Promise.inPromiseP_ofLanguage_iff` — on languages, the promise class `P` is `P`.
* `Promise.inPromiseBPP_ofLanguage_iff` — on languages, the promise class `BPP` is `InBPP`.

## Divergences

* [Wat08, §II.1] puts a promise problem in `P` when a polynomial-time machine accepts every
  yes-instance and rejects every no-instance. We state this as "some language in `P` contains
  the yes-instances and avoids the no-instances": the language the machine decides is such a
  separator, and conversely a separator's decider is such a machine. This reuses
  `Complexity.P` without restating machines.
* `InPromiseBPP` uses the certificate view and the verifier models of
  `Randomized.InBPP` (see `TCSlib/Complexity/Randomized/Classes.lean`, **Deviations**): an
  abstract `VerifierModel` and random strings of length `polyLen a k |x|`. [Wat08]'s "accepts
  with probability at most `1/3`" on no-instances appears as "rejects with probability at least
  `2/3`", as in `InBPP`; the two agree by `Randomized.randProb_bool_false`.

## References

* [Wat08] J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401, 2008.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Promise

open Randomized Complexity

/-- A *promise problem* over binary strings: a set `yes` of yes-instances and a set `no` of
no-instances, which are disjoint. Strings in neither set are outside the promise.
[Wat08, §II.1] -/
structure Problem where
  /-- The yes-instances. -/
  yes : Set (List Bool)
  /-- The no-instances. -/
  no : Set (List Bool)
  /-- No string is both a yes-instance and a no-instance. -/
  disjoint : Disjoint yes no

/-- The language `L` viewed as a promise problem: its yes-instances are the members of `L` and
its no-instances are all other strings. [Wat08, §II.1] -/
def ofLanguage (L : Language Bool) : Problem where
  yes := {x | x ∈ L}
  no := {x | x ∉ L}
  disjoint := Set.disjoint_left.2 fun _ h₁ h₂ => h₂ h₁

/-- The yes-instances of `ofLanguage L` are the members of `L`. -/
theorem ofLanguage_yes (L : Language Bool) : (ofLanguage L).yes = {x | x ∈ L} := rfl

/-- The no-instances of `ofLanguage L` are the non-members of `L`. -/
theorem ofLanguage_no (L : Language Bool) : (ofLanguage L).no = {x | x ∉ L} := rfl

/-- A promise problem is *total* when every string is a yes-instance or a no-instance, that is,
when the promise is trivial. [Wat08, §II.1] -/
def Problem.IsTotal (A : Problem) : Prop := ∀ x, x ∈ A.yes ∨ x ∈ A.no

/-- `A` is total iff every string is a yes-instance or a no-instance. -/
theorem Problem.isTotal_iff (A : Problem) : A.IsTotal ↔ ∀ x, x ∈ A.yes ∨ x ∈ A.no := Iff.rfl

/-- A language, viewed as a promise problem, is total.

**Proof sketch.** Every string is in `L` or not (`em`). -/
theorem ofLanguage_isTotal (L : Language Bool) : (ofLanguage L).IsTotal :=
  fun x => em (x ∈ L)

/-- The promise problem `A` is in (promise) `P`: some language in `P` contains every
yes-instance and no no-instance. [Wat08, §II.1], in the separator form described in the module
docstring. -/
def InPromiseP (A : Problem) : Prop :=
  ∃ L ∈ P, A.yes ⊆ {x | x ∈ L} ∧ A.no ⊆ {x | x ∉ L}

/-- `A` is in promise `P` iff some `L ∈ P` contains `A.yes` and avoids `A.no`. -/
theorem inPromiseP_iff (A : Problem) :
    InPromiseP A ↔ ∃ L ∈ P, A.yes ⊆ {x | x ∈ L} ∧ A.no ⊆ {x | x ∉ L} := Iff.rfl

/-- On languages, promise `P` is `P`: `ofLanguage L` is in promise `P` iff `L ∈ P`.

**Proof sketch.** (⇐) `L` separates itself from its complement. (⇒) A separator `L'` contains
`L` and avoids `Lᶜ`, so `L' = L`. -/
theorem inPromiseP_ofLanguage_iff (L : Language Bool) : InPromiseP (ofLanguage L) ↔ L ∈ P := by
  constructor
  · rintro ⟨L', hL', h1, h2⟩
    have : L' = L := by
      ext x
      constructor
      · intro hx
        by_contra hn
        exact h2 hn hx
      · intro hx
        exact h1 hx
    exact this ▸ hL'
  · intro h
    exact ⟨L, h, fun _ hx => hx, fun _ hx => hx⟩

/-- The promise problem `A` is in (promise) `BPP` relative to the verifier model `E`: some
efficient verifier `M` with random strings of length `polyLen a k |x|` accepts every
yes-instance with probability at least `2/3` and rejects every no-instance with probability at
least `2/3`. Strings outside the promise are unconstrained. [Wat08, §II.1]; the language form is
`Randomized.InBPP` [AB09, Def 7.3]. -/
def InPromiseBPP (E : VerifierModel) (A : Problem) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ A.yes → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∈ A.no → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- `A` is in promise `BPP` iff some efficient verifier decides it with error at most `1/3` on
the promise. -/
theorem inPromiseBPP_iff (E : VerifierModel) (A : Problem) :
    InPromiseBPP E A ↔
      ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
        E.Eff (boolVerifier M) ∧
        ∀ x : List Bool,
          (x ∈ A.yes → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
          (x ∈ A.no → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false) :=
  Iff.rfl

/-- On languages, promise `BPP` is `BPP`: `ofLanguage L` is in promise `BPP` iff `InBPP E L`.

**Proof sketch.** Membership in `(ofLanguage L).yes` is `x ∈ L` and membership in
`(ofLanguage L).no` is `x ∉ L`, so the two definitions coincide clause by clause. -/
theorem inPromiseBPP_ofLanguage_iff (E : VerifierModel) (L : Language Bool) :
    InPromiseBPP E (ofLanguage L) ↔ InBPP E L :=
  Iff.rfl

end Promise
