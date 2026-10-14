/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Immerman-Szelepcsényi theorem

[AB09, §4.3.2, Theorem 4.20 and Corollary 4.21]: nondeterministic space is
closed under complement — `PATH-complement ∈ NL`, hence `NL = coNL`, and for
space-constructible `S` the same inductive counting gives
`NSPACE(S) = coNSPACE(S)`. Phase P4.4 of `AroraBarakChapters3-4Plan.md`.

## Design

* **No read-once certificate model is introduced.** [AB09] proves Theorem
  4.20 in the certificate view of `NL` (its §4.3.1, Definition 4.19 — a
  read-once certificate tape), which the plan defers. The campaign's
  binary-choice NDTM makes that view *native*: a choice word is consumed one
  bit per step and can never be re-read, so the book's certificates are
  exactly choice words and the inductive-counting verifier runs directly on
  `Turing.FinNDTM` — the deviation is a simplification, recorded here for
  the audit.
* The counting runs directly over the **configuration graph** of an arbitrary
  `NSPACE S` decider (`S ≥ logSpace`), whose vertices are the codes of
  `TCSlib.Complexity.SpaceComplexity.Codec`: the generic
  `Complexity.compl_mem_NSPACE` (`L ∈ NSPACE S → Lᶜ ∈ NSPACE S`,
  `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect`) is proved by the
  window-growing inductive-counting nondeterministic register machine
  `Complexity.LogProg.ISGen.igA`, and `Complexity.compl_mem_NL` is its case
  `S = logSpace` (`NL = NSPACE logSpace`). The `PATH` form is then a corollary of
  `Complexity.PATH_mem_NL`, and no `NL`-completeness of `PATH` or closure of
  `NL` under logspace reductions is needed.

## Main results

* `Complexity.compl_PATH_mem_NL` — [AB09, Theorem 4.20] as stated there.
* `Complexity.NL_eq_coNL` — the headline equality. [AB09, §4.3.2]
* `Complexity.NSPACE_compl_eq` — [AB09, Corollary 4.21], from the generic
  `Complexity.compl_mem_NSPACE` (`L ∈ NSPACE S → Lᶜ ∈ NSPACE S` for `S ≥ log`,
  `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect`), proved by a
  window-growing variant of the counting machine that finds the window radius
  itself; of `SpaceConstructible S` only the conjunct `S ≥ logSpace` is used.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.1-§4.3.2, Theorem 4.20,
  Corollary 4.21.)
* [Imm88] N. Immerman, *Nondeterministic space is closed under
  complementation*, SIAM J. Comput. 17(5), 1988; [Sze87] R. Szelepcsényi,
  *The method of forcing for nondeterministic automata*, Acta Informatica
  26, 1988. (Cited through [AB09]; no external text required.)
-/

namespace Complexity

open Turing

/-- **`PATH`-complement is in `NL`** ([AB09, Theorem 4.20]): nonreachability has
nondeterministically verifiable certificates, by inductive counting.

**Proof sketch.** `PATH ∈ NL` (`Complexity.PATH_mem_NL`), and `NL` is closed under
complement (`Complexity.compl_mem_NL`, the case `S = logSpace` of
`Complexity.compl_mem_NSPACE`): the window-growing inductive-counting register machine runs
on the configuration graph of the `PATH` walk machine, at radii `s = 0, 1, …`, computing for
`i = 0, …, K - 1` the size of the ball `C_{i+1}` of codes reachable from the initial code
within `i + 1` steps from the size `cp` of `C_i`. Every code `v` is guessed in or out of
`C_{i+1}` in ascending order; a member is certified by a guessed walk (and must not be
accepting); a non-member by enumerating, again in ascending order, exactly `cp` guessed
members of `C_i` with their walks, none equal to `v` or stepping to `v`. It stops at the
first radius whose count of reachable codes equals the previous one. Choice words serve as
the certificates (native read-once). All registers have `O(log |x|)` digits and every branch
halts. -/
theorem compl_PATH_mem_NL : (PATHᶜ : Language Bool) ∈ NL := by
  exact compl_mem_NL PATH_mem_NL

/-- **`NL = coNL`** ([AB09, §4.3.2]).

**Proof sketch.** Both inclusions are `Complexity.compl_mem_NL`, i.e.
`Complexity.compl_mem_NSPACE` at `S = logSpace` (inductive counting on the configuration
graph of an `NL` decider): `L ∈ NL` gives `Lᶜ ∈ NL`, i.e. `L ∈ coNL`; and `Lᶜ ∈ NL` gives
`Lᶜᶜ = L ∈ NL` (complements are involutive). -/
theorem NL_eq_coNL : NL = coNL := by
  ext L
  exact ⟨fun h => compl_mem_NL h, fun h => compl_compl L ▸ compl_mem_NL h⟩

/-- **Nondeterministic space is closed under complement**
([AB09, Corollary 4.21]): for space-constructible `S`, the complements of
`NSPACE S` languages are exactly `NSPACE S`.

**Proof sketch.** Both inclusions are `Complexity.compl_mem_NSPACE` (with
`S ≥ logSpace`, the first conjunct of `Complexity.SpaceConstructible`) and the
involution `Lᶜᶜ = L`. `compl_mem_NSPACE` runs the inductive counting of
`Complexity.compl_PATH_mem_NL` on the configuration graph of a decider `N` of
`L` in space `c · S` (codes of window-bounded configurations, membership
certificates guessed walks of step pairs), but does **not** compute the window
radius from the constructibility witness as [AB09, Exercise 4.11] suggests:
the window-growing machine `Complexity.LogProg.ISGen.igA` counts the reachable
codes at radii `s = 0, 1, …` and stops at the first radius whose count equals
the previous one — the window is then closed under steps, so acceptance is
decided by the reachable codes (`Complexity.ExpBFS.mem_iff_of_card_eq`); the
counts agree above `c · S |x|` (`Complexity.ExpBFS.card_rset_succ_of_le`), so
the radius stays at most `c · S |x| + 1` and all registers have `O(S |x|)`
digits, within `Complexity.LogProg.narm_decides_space` with logspace code
deciders. -/
theorem NSPACE_compl_eq (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    {L : Language Bool | Lᶜ ∈ NSPACE S} = NSPACE S := by
  ext L
  exact ⟨fun h => compl_compl L ▸ compl_mem_NSPACE hS.1 h, fun h => compl_mem_NSPACE hS.1 h⟩

end Complexity
