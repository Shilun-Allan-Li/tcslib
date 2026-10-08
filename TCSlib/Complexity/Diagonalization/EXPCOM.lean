/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `EXPCOM` oracle: `P^EXPCOM = NP^EXPCOM = EXP`

[AB09, Example 3.6(3)]: relative to the oracle
`EXPCOM = {⟨M, x, 1ⁿ⟩ : M outputs 1 on x within 2ⁿ steps}`, deterministic and
nondeterministic polynomial time coincide — both equal `EXP`, via the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`. This is the `A` half of the
Baker-Gill-Solovay theorem ([AB09, Theorem 3.7], `Diagonalization/Relativization`),
taken by the book's route per the campaign decision CH34-Q4
(`AroraBarakChapters3-4Plan.md` §2.3; the machine-light self-referential oracle
of [BGS75, Theorem 1] stays recorded there as the fallback).

## Design

* **The triple `⟨M, x, 1ⁿ⟩` is rendered code-first** as
  `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)` — the universal machine's
  layout (code before payload, chapter-1 phase-3 audit, Argument B), nested
  right so each component is recovered by one aligned-pair parse.
* **The code scheme is the campaign's fixed `Complexity.TimeHierarchy.code`**,
  reused rather than re-chosen, so the timed universal machine
  (`Turing.timed_universal`) and every encoding lemma apply verbatim.
* **"Outputs `1` within `2ⁿ` steps"** is
  `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
  predicate is monotone in the budget and "within" is faithful.
* **Totalization**: a string that does not parse as a triple is simply not in
  `EXPCOM` (the existential fails); on genuine triples the witnessing
  decomposition is unique (`Turing.pairEncode_injective`,
  `Turing.pairEncode_replicate_inj`), so the defining condition is
  unambiguous.

## Main definitions

* `Complexity.EXPCOM` — the oracle language. [AB09, Example 3.6(3)]

## Main results (all sorried; phase-P3.2 statements)

* `Complexity.EXP_subset_POracle_EXPCOM` — one padded query decides any
  `EXP` language.
* `Complexity.NPOracle_EXPCOM_subset_EXP` — the fill summit: deterministic
  exponential-time simulation of a polynomial-time oracle NDTM, answering its
  queries with the timed universal machine.
* `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` — the chained identities.
  [AB09, Example 3.6(3)]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Example 3.6(3); Claim 2.4.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (Theorem 1: the recorded
  fallback oracle for the `A` half.)
-/

namespace Complexity

open Turing

/-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
`⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
rendered with the campaign's fixed code scheme `Complexity.TimeHierarchy.code`
and the code-first nesting `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with
"outputs `1` within `2ⁿ` steps" as
`Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in the budget, since
halting is absorbing). Strings that do not parse as such a triple are not in
the language; on genuine triples the decomposition is unique
(`Turing.pairEncode_injective`, `Turing.pairEncode_replicate_inj`). -/
def EXPCOM : Language Bool :=
  {z | ∃ (α x : List Bool) (n : ℕ),
    z = pairEncode α (pairEncode x (List.replicate n true)) ∧
    ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}

/-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
[AB09, Example 3.6(3), the first inclusion of the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`]

**Proof sketch.** Let `L ∈ EXP`, say decided by `M` within `a · 2^(n^c)`
(`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
`α_L := TimeHierarchy.code.encode N`, recovered by
`code.toMachineCode.decode_encode`. Choose the padding exponent
`Q n := C · (n + 1)^c` with `C` absorbing `a`, the square, and the `+1`
normalizations, so that `N` outputs `[χ_L x]` within `2^(Q |x|)` steps on every
`x`. The reduction is `f x := pairEncode α_L (pairEncode x 1^(Q |x|))` —
polynomial-time by the chapter-2 padding cluster: the constant prefix
(`Complexity.polyTimeComputable_const`), the copy
(`Complexity.polyTimeComputable_id`), the unary padding emitter
(`Complexity.polyTimeComputable_polyUnary C c`), assembled by two applications
of `Complexity.PolyTimeComputable.pairEncode`. Membership: if `x ∈ L` then the
witness `(α_L, x, Q |x|)` puts `f x ∈ EXPCOM`; conversely a witness for
`f x ∈ EXPCOM` is forced to be exactly `(α_L, x, Q |x|)`
(`Turing.pairEncode_injective` twice, `Turing.pairEncode_replicate_inj`), and
output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
verdict `[χ_L x]` forces `x ∈ L`. Conclude with
`Complexity.mem_POracle_of_polyTimeReducible`. -/
theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
  sorry

/-- **The fill summit of the `EXPCOM` cluster**: `NP^EXPCOM ⊆ EXP` — a
deterministic exponential-time machine can enumerate all branches of a
polynomial-time oracle NDTM and answer its `EXPCOM` queries itself.
[AB09, Example 3.6(3), the last inclusion; summit 2 of
`AroraBarakChapters3-4Plan.md` §6, continuation budget certain]

**Proof sketch.** Let `L ∈ NP^EXPCOM`: a well-formed oracle NDTM `N` decides
`L` with oracle `EXPCOM` within `p n := c · (n^k + 1)`. The deciding plain
machine, on input `x` of length `n`:

1. **Choice-word enumeration.** Iterate over all `2^(p n)` choice words of
   length exactly `p n` as a fixed-width counter, one round per word, in the
   `Complexity.NP_subset_EXP` enumerator pattern
   (`Complexity.exists_proj_decider` / `enumLoop_run`: fixed-width carry,
   captured round verdict, reversible scratch restoration, accept-or-increment
   control).
2. **Per-step simulation.** Within a round, simulate
   `Turing.OracleNDTM.runWith` step by step under the current word — the
   step-by-step compilation invariant of the chapter-2 2B cluster
   (`ClassNP/Nondeterminism.lean`), extended by one new case: the query state.
3. **Query answering.** When the simulated state is `qQuery`, read the
   simulated query tape `z` (`Turing.OracleTM.queryString` contract), parse it
   as `pairEncode α' (pairEncode x' 1^(n'))` by aligned two-bit parsing (the
   `Turing.pairDecode` layer; `TCSlib.Complexity.TuringMachine.CodeParser`
   machine precedent) — malformed strings answer "no" — and decide
   `z ∈ EXPCOM` by running the timed universal machine
   (`Turing.timed_universal` at the fixed scheme `TimeHierarchy.code`) on
   `(α', x')` with deadline `2^(n')`: answer "yes" exactly on success with
   simulated output `[true]` (report `true :: [true]`); the deadline-inclusive
   timeout clause makes the answer the exact membership bit, with
   parse-uniqueness (`Turing.pairEncode_injective`,
   `Turing.pairEncode_replicate_inj`) identifying the witness decomposition.
4. **Ledger.** Each branch submits queries of length at most the elapsed
   budget (`Turing.OracleTM.queryString_length_le` transferred along the
   simulation invariant), so `n' ≤ p n` and one oracle call costs
   `O((2^(p n) + 1)^2)` universal-machine steps; a round is `p n` simulated
   steps of which each costs at most one call: the total over `2^(p n)` rounds
   is `2^(O(p n) )·(2^(p n))^2 = 2^(O(n^k))`, inside `DTIME (2^(n^(k+1)))` by
   `Complexity.DTIME`'s constant absorption — so `L ∈ EXP`.
5. **Acceptance.** `x ∈ L` iff some length-`p n` branch accepts
   (`Turing.FinOracleNDTM.DecidesInTime`, with all-branch halting making every
   round's verdict defined); the enumerator's existential sweep returns exactly
   this disjunction.

Fill obligations, named for the brief: the query-dispatcher routine (parse +
clocked universal call + resume seam) and its capture discipline; the
simulation invariant tying the host's configuration coding to `runWith`; the
budget normalization into `EXP`'s `2^(n^c)` form. -/
theorem NPOracle_EXPCOM_subset_EXP : NPOracle EXPCOM ⊆ EXP := by
  sorry

/-- **`P^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊇` is `Complexity.EXP_subset_POracle_EXPCOM`; `⊆` chains
`Complexity.POracle_subset_NPOracle` with
`Complexity.NPOracle_EXPCOM_subset_EXP`. -/
theorem POracle_EXPCOM_eq_EXP : POracle EXPCOM = EXP := by
  sorry

/-- **`NP^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊆` is `Complexity.NPOracle_EXPCOM_subset_EXP`; `⊇` chains
`Complexity.EXP_subset_POracle_EXPCOM` with
`Complexity.POracle_subset_NPOracle`. -/
theorem NPOracle_EXPCOM_eq_EXP : NPOracle EXPCOM = EXP := by
  sorry

/-- **Relative to `EXPCOM`, determinism and nondeterminism coincide**:
`P^EXPCOM = NP^EXPCOM` — the `A` half of the Baker-Gill-Solovay theorem.
[AB09, Example 3.6(3), cited by the proof of Theorem 3.7]

**Proof sketch.** Chain `Complexity.POracle_EXPCOM_eq_EXP` with the inverse of
`Complexity.NPOracle_EXPCOM_eq_EXP`. -/
theorem POracle_EXPCOM_eq_NPOracle_EXPCOM : POracle EXPCOM = NPOracle EXPCOM := by
  sorry

end Complexity
