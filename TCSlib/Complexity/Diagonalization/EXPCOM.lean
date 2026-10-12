/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.TimeHierarchy.Diagonal
-- B5a sanctioned import: route Z uses the one-tape machine format.
import TCSlib.Complexity.TuringMachine.CodeSimulator
-- B5b sanctioned imports: the certificate shell and exponential-polynomial ledger.
import TCSlib.Complexity.TuringMachine.Build.CertShell
import TCSlib.Complexity.ClassNP.ExpPoly

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
* **The code scheme is a uniformly-timed scheme, not the hierarchy's
  arbitrary one** (round-1 blocker): `Turing.EffectiveMachineCode` bounds no
  decoding time — `canonizerTime` is arbitrary, and the round-1 audit built
  a permitted scheme embedding an arbitrarily hard decidable language into
  `decode`, putting `EXPCOM` outside `EXP` and even separating its
  relativized `P` from `NP`. `EXPCOM` queries carry **variable** codes, so
  per-code constants (`∀ α, ∃ C` — `Turing.timed_universal`'s shape) cannot
  pay for them. The new `Turing.UniformMachineCode` packages the scheme with
  a simulator whose time is **one polynomial in the code, the input, and
  the deadline jointly**; `EXPCOM` is defined over a scheme chosen from its
  sorried existence (`Turing.exists_uniformMachineCode` — the
  `TimeHierarchy.code` mirror, with the choice-over-a-sorried-existence
  declared). The hierarchy's own `Complexity.TimeHierarchy.code` is
  unchanged: fixed-code arguments never needed uniformity.
* **"Outputs `1` within `2ⁿ` steps"** is
  `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
  predicate is monotone in the budget and "within" is faithful.
* **Totalization**: a string that does not parse as a triple is simply not in
  `EXPCOM` (the existential fails); on genuine triples the witnessing
  decomposition is unique — `Turing.pairEncode_injective` applied twice,
  then `List.length` on the equality of the replicated tails (round-1
  finding 3 corrected the earlier `pairEncode_replicate_inj` citation, whose
  unary component sits on the wrong side for this nesting) — so the defining
  condition is unambiguous.

## Main definitions

* `Turing.UniformMachineCode` — an effective scheme with a uniformly timed
  bounded-acceptance simulator (round-1 repair).
* `Complexity.expCode` — the chosen uniformly-timed scheme (noncomputable;
  via the sorried existence).
* `Complexity.EXPCOM` — the oracle language, over `expCode`.
  [AB09, Example 3.6(3)]

## Main results (B5a partial: five bodies filled; the B5b summit remains sorried)

* `Turing.exists_uniformMachineCode` — a uniformly-timed scheme exists.

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

namespace Turing

/-- An effective representation scheme together with a **uniformly timed
bounded-acceptance simulator**: one machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the simulator decides whether the decoded machine outputs
`[true]` on `x` within `t` steps, in time one polynomial in
`|α| + |x| + t + 1` **jointly** — uniform in the code, which is exactly what
`EXPCOM`'s variable-code queries need and what a bare
`Turing.EffectiveMachineCode` (arbitrary `canonizerTime`) or the per-code
`∀ α, ∃ C` of `Turing.timed_universal` cannot supply (round-1 blocker). -/
structure UniformMachineCode extends EffectiveMachineCode where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-- **A uniformly-timed scheme exists** (proved modulo §12.11; B5a partial): the chapter-1 concrete scheme, with its time analysis made uniform.

**Proof sketch.** The concrete grammar of the chapter-1 scheme
(`encode := CodeTM.serialize`, `decode := codeDecode`, the encoding law from
`codeDecode_serialize_pad`), with an **independently constructed**
polynomial parser/simulator — the received generic compiler route is
arbitrary-time and its polynomial variant is explicitly superseded
(`MathlibBridge`), so no received time ledger is claimed (round-2 finding
1); the decoder's *correctness* lemmas are reused, its complexity is not.
The construction: (i) parse the nested simulator input keeping the deadline
in binary, and check the table's minimum-length guard
(`81 · (numStates + 1) ≤ rest.length`, `CodeParser`'s grammar) by **binary**
arithmetic before any per-state iteration — a huge declared state count
must never be expanded in unary; (ii) on success scan the linearly many
records with range checks (whence
`|(codeDecode α).serialize| ≤ max |α| 84`, the fallback's exact length);
(iii) simulate at most `t` source transitions under a binary countdown,
tracking the finite table, the heads, the visited work interval, and a
**three-way output status** (empty / exactly `[true]` / permanently other —
append-only output never returns), testing haltedness after the `t`-th
transition before declaring timeout; (iv) with `S := |α| + |x| + t + 1`,
bounded scans, lookups, and at most `t` rounds give `C·S^e` for a fixed
multitape machine, and `d ≥ max 1 (max C e)` gives `C·S^e ≤ d·S^d`. The
same parser emits the serialization prefix or the fallback serialization,
supplying the inherited canonizer field. Fill obligations, named: the
binary-guard parser; the simulation invariant with the three-way status;
the polynomial ledger; the degree arithmetic. **Continuation budget
certain.**

**Fill appendix (B5a, route Z).** Instantiate §12.11 at
`oneTapeMachineFormat`, as in the statement probe's `uniform_one`. The
polynomial canonizer and H1 supply the inherited canonizer and the two
simulator clauses. Both shared contracts remain admitted in this partial. -/
theorem exists_uniformMachineCode : Nonempty UniformMachineCode := by
  obtain ⟨C, dC, hC⟩ := oneTapeMachineFormat.exists_polyCanonizer
  obtain ⟨S, d, hS⟩ := oneTapeMachineFormat.exists_uniformSimulator
  exact ⟨{
    toEffectiveMachineCode := {
      toMachineCode := ⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩
      canonizer := C
      canonizerTime := fun n => dC * (n + 1) ^ dC
      canonizer_computes := hC }
    simulator := S
    simDegree := d
    simulator_accepts := fun α x t h => (hS α x t).1 h
    simulator_rejects := fun α x t h => (hS α x t).2 h }⟩

end Turing

namespace Complexity

open Turing

/-- The chosen uniformly-timed scheme for the `EXPCOM` cluster — the
`Complexity.TimeHierarchy.code` pattern over the **sorried** existence
`Turing.exists_uniformMachineCode` (declared: until that fill lands, this
definition and its consumers carry `sorryAx` through the choice). -/
noncomputable def expCode : UniformMachineCode :=
  Classical.choice exists_uniformMachineCode

/-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
`⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
rendered over the uniformly-timed scheme `Complexity.expCode` (round-1
repair — see the module docstring) and the code-first nesting
`Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with "outputs `1` within
`2ⁿ` steps" as `Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in
the budget, since halting is absorbing). Strings that do not parse as such a
triple are not in the language; on genuine triples the decomposition is
unique (`Turing.pairEncode_injective` twice, then `List.length` on the
replicated tails). -/
def EXPCOM : Language Bool :=
  {z | ∃ (α x : List Bool) (n : ℕ),
    z = pairEncode α (pairEncode x (List.replicate n true)) ∧
    (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}

/-- A polynomial unary padding exponent pays for the quadratic normal-form
slowdown, uniformly at empty input and at exponent zero.

**Proof sketch.** Bound each constant by a power of two and absorb the added
one before squaring. The resulting exponent is at most a fixed multiple of
`(n + 1)^c`, since this quantity is positive and dominates `n^c`. -/
private lemma expcom_padding_bound (a b c n : ℕ) :
    b * (a * 2 ^ n ^ c + 1) ^ 2 ≤
      2 ^ ((b + 2 * (a + 1) + 2) * (n + 1) ^ c) := by
  have hE : 1 ≤ 2 ^ n ^ c := Nat.one_le_pow _ _ (by omega)
  have hinner : a * 2 ^ n ^ c + 1 ≤ 2 ^ (a + 1 + n ^ c) := by
    calc
      a * 2 ^ n ^ c + 1 ≤ (a + 1) * 2 ^ n ^ c := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      _ ≤ 2 ^ (a + 1) * 2 ^ n ^ c :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n := a + 1)))
      _ = 2 ^ (a + 1 + n ^ c) := (Nat.pow_add _ _ _).symm
  have hexponent : b + (a + 1 + n ^ c) * 2 ≤
      (b + 2 * (a + 1) + 2) * (n + 1) ^ c := by
    have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have hconst : b + 2 * (a + 1) ≤ (b + 2 * (a + 1)) * (n + 1) ^ c := by
      simpa using Nat.mul_le_mul_left (b + 2 * (a + 1)) hone
    have hpower : 2 * n ^ c ≤ 2 * (n + 1) ^ c := by gcongr; omega
    calc
      b + (a + 1 + n ^ c) * 2 = (b + 2 * (a + 1)) + 2 * n ^ c := by ring
      _ ≤ (b + 2 * (a + 1)) * (n + 1) ^ c + 2 * (n + 1) ^ c :=
        Nat.add_le_add hconst hpower
      _ = (b + 2 * (a + 1) + 2) * (n + 1) ^ c := by ring
  calc
    b * (a * 2 ^ n ^ c + 1) ^ 2 ≤ 2 ^ b * (2 ^ (a + 1 + n ^ c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := b)))
        (Nat.pow_le_pow_left hinner 2)
    _ = 2 ^ (b + (a + 1 + n ^ c) * 2) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hexponent

/-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
[AB09, Example 3.6(3), the first inclusion of the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`]

**Proof sketch.** Let `L ∈ EXP`, say decided by `M` within `a · 2^(n^c)`
(`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
`α_L := expCode.encode N`, recovered by
`Turing.MachineCode.decode_encode` (a **fixed** code: this inclusion never
needed uniformity, as the round-1 audit confirmed). Choose the padding exponent
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
(`Turing.pairEncode_injective` twice, then `List.length` on the replicated
tails), and output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
verdict `[χ_L x]` forces `x ∈ L`. Conclude with
`Complexity.mem_POracle_of_polyTimeReducible`.

**Fill appendix (B5a).** Take `C = b + 2 * (a + 1) + 2`, where `b` is
the one-work-tape slowdown coefficient. `expcom_padding_bound` proves the
inequality for every input length, including zero, without an asymptotic
exception. The two pair injections force the full query witness. -/
theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
  intro L hL
  classical
  obtain ⟨c, a, M, hM⟩ := Set.mem_iUnion.mp hL
  obtain ⟨M', b, hk, hM'⟩ := M.one_work_tape_binary
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => a * 2 ^ n ^ c) hM
  obtain ⟨N, hN⟩ := exists_codeTM M' hk
  let C := b + 2 * (a + 1) + 2
  have hdec (x : List Bool) :
      N.toFinTM.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x]
        (2 ^ (C * (x.length + 1) ^ c)) :=
    ((hN x _ _).mpr (hM' x)).mono (expcom_padding_bound a b c x.length)
  apply mem_POracle_of_polyTimeReducible
  refine ⟨fun x => pairEncode (expCode.encode N)
      (pairEncode x (List.replicate (C * (x.length + 1) ^ c) true)),
    (polyTimeComputable_const (expCode.encode N)).pairEncode
      (polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary C c)), ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨expCode.encode N, x, C * (x.length + 1) ^ c, rfl, ?_⟩
    rw [expCode.toMachineCode.decode_encode]
    simpa [MultiTapeTM.indicator, hx] using hdec x
  · rintro ⟨α, y, n, heq, hy⟩
    have hpair :
        (expCode.encode N, pairEncode x (List.replicate (C * (x.length + 1) ^ c) true)) =
          (α, pairEncode y (List.replicate n true)) := pairEncode_injective heq
    have hcode := congrArg Prod.fst hpair
    have hinner : (x, List.replicate (C * (x.length + 1) ^ c) true) =
        (y, List.replicate n true) := pairEncode_injective (congrArg Prod.snd hpair)
    have hinput := congrArg Prod.fst hinner
    dsimp only at hcode hinput
    have hlen := congrArg List.length (congrArg Prod.snd hinner)
    simp only [List.length_replicate] at hlen
    rw [← hcode, expCode.toMachineCode.decode_encode, ← hinput, ← hlen] at hy
    have hout := hy.output_unique (hdec x)
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x = true := by
      simpa using hout.symm
    by_contra hx
    simp [MultiTapeTM.indicator, hx] at hi

/-- The binary deadline has one high bit after the unary tail's width.
Forced private restatement of `TimeHierarchy/Separation.bits_two_pow`;
promotion requested in the B5b report. -/
private lemma expcom_bits_two_pow (n : ℕ) :
    (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = Nat.bit false (2 ^ n) := by
      simp [Nat.bit_val, Nat.pow_succ]; ring
    rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (Nat.ne_of_gt (Nat.pow_pos (by decide)))), ih]
    simp [List.replicate_succ]

/-- Carry through a unary prefix, retaining the fixed width. -/
private lemma expcom_inc_prefix (n : ℕ) (w : List Bool) :
    incFixed (List.replicate n true ++ w) =
      (incFixed w).map (List.replicate n false ++ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, incFixed, ih, Option.map_map, Function.comp_def]

/-- An empty increment result certifies an all-`true` word.
This is the needed direction of the circuit module's overflow criterion;
promotion to `Build/Convention` is requested in the B5b report. -/
private lemma expcom_all_true (w : List Bool) (h : (incFixed w).getD [] = []) :
    w = List.replicate w.length true := by
  revert h
  induction w with
  | nil => intro _; rfl
  | cons b w ih =>
    intro h
    cases b with
    | false => simp [incFixed] at h
    | true =>
      cases he : incFixed w with
      | none =>
        have hw := ih (by simp [he])
        simpa only [List.length_cons, List.replicate_succ] using congrArg (true :: ·) hw
      | some v => simp [incFixed, he] at h

/-- The unary deadline field, projected from a possibly malformed query. -/
private def expcom_tail (z : List Bool) : List Bool := pairSndD (pairSndD z)

/-- The guard checks both pair separators and the unary deadline field. -/
private def expcom_ok (z : List Bool) : Bool :=
  (pairDecode z).isSome && (pairDecode (pairSndD z)).isSome &&
    decide ((incFixed (expcom_tail z)).getD [] = [])

/-- Rebuild the uniform simulator's input, replacing the unary deadline exponent
by its little-endian power-of-two clock. Only guarded queries use this word. -/
private def expcom_simIn (z : List Bool) : List Bool :=
  pairEncode (pairEncode ((incFixed (expcom_tail z ++ [false])).getD []) (pairFstD z))
    (pairFstD (pairSndD z))

/-- Malformed queries are redirected to the fixed zero-deadline simulator input. -/
private def expcom_front (z : List Bool) : List Bool :=
  if expcom_ok z then expcom_simIn z else pairEncode (pairEncode [] []) []

/-- The guard accepts exactly the specified nested triples.

**Proof sketch.** Recover each pair from a successful parse, then use the empty
increment output to identify the unary tail. Conversely both pair parsers succeed
on an encoded triple and the all-`true` increment overflows. -/
private lemma expcom_ok_iff (z : List Bool) :
    expcom_ok z = true ↔ ∃ (α x : List Bool) (n : ℕ),
      z = pairEncode α (pairEncode x (List.replicate n true)) := by
  constructor
  · intro h
    have hp : ((pairDecode z).isSome = true ∧
        (pairDecode (pairSndD z)).isSome = true) ∧
        (incFixed (expcom_tail z)).getD [] = [] := by
      simpa only [expcom_ok, Bool.and_eq_true, decide_eq_true_eq] using h
    obtain ⟨⟨α, v⟩, ha⟩ := Option.isSome_iff_exists.mp hp.1.1
    have hz := eq_pairEncode_of_pairDecode z α v ha
    subst z
    have hv : (pairDecode v).isSome = true := by simpa using hp.1.2
    obtain ⟨⟨x, w⟩, hx⟩ := Option.isSome_iff_exists.mp hv
    have hv := eq_pairEncode_of_pairDecode v x w hx
    subst v
    have hw : w = List.replicate w.length true :=
      expcom_all_true w (by simpa [expcom_tail] using hp.2)
    exact ⟨α, x, w.length, by rw [← hw]⟩
  · rintro ⟨α, x, n, rfl⟩
    have hinc : incFixed (List.replicate n true) = none := by
      simpa [incFixed] using expcom_inc_prefix n []
    simp [expcom_ok, expcom_tail, hinc, pairDecode_pairEncode]

/-- The guarded input reconstruction is polynomial-time.

**Proof sketch.** Compose the two projections, grammar tests, fixed-width
increment and whole-word equality test. Two conjunctions form the guard. Append
a zero and increment to build the clock, pair the three fields, then branch to
this input or the constant zero-deadline input. Every machine is a cited public
composition or primitive. -/
private lemma expcom_front_poly : PolyTimeComputable expcom_front := by
  have hi : PolyTimeComputable (fun w => (incFixed w).getD []) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_incFixed
  have ht : PolyTimeComputable expcom_tail :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hv : PolyTimeComputable (fun z => [(pairDecode z).isSome]) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
  have hu : PolyTimeComputable
      (fun z => [decide ((incFixed (expcom_tail z)).getD [] = [])]) := by
    convert (polyTimeComputable_of_linear
      (FinTM.computesFunInTime_ifEq [] [true] [false])).comp (hi.comp ht) using 1
    funext z
    by_cases h : (incFixed (expcom_tail z)).getD [] = [] <;> simp [Function.comp_def, h]
  have hg : PolyTimeComputable (fun z => [expcom_ok z]) :=
    polyTimeComputable_and
      (polyTimeComputable_and hv (hv.comp polyTimeComputable_pairSndD)) hu
  have hc : PolyTimeComputable (fun z => (incFixed (expcom_tail z ++ [false])).getD []) :=
    hi.comp ((polyTimeComputable_of_linear (FinTM.computesFunInTime_appendBit false)).comp ht)
  -- Use the public swap row for the simulator's clock-before-code layout.
  have hp : PolyTimeComputable (fun z =>
      pairEncode ((incFixed (expcom_tail z ++ [false])).getD []) (pairFstD z)) := by
    simpa only [Function.comp_def, pairSndD_pairEncode, pairFstD_pairEncode] using
      polyTimeComputable_pairSwap.comp (polyTimeComputable_pairFstD.pairEncode hc)
  have hs : PolyTimeComputable expcom_simIn :=
    hp.pairEncode (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite hg hs (polyTimeComputable_const (pairEncode (pairEncode [] []) []))

/-- On an encoded triple the front end supplies the simulator's canonical input. -/
private lemma expcom_front_triple (α x : List Bool) (n : ℕ) :
    expcom_front (pairEncode α (pairEncode x (List.replicate n true))) =
      pairEncode (pairEncode (Nat.bits (2 ^ n)) α) x := by
  have hok : expcom_ok (pairEncode α (pairEncode x (List.replicate n true))) = true :=
    (expcom_ok_iff _).mpr ⟨α, x, n, rfl⟩
  simp [expcom_front, hok, expcom_simIn, expcom_tail, expcom_inc_prefix,
    incFixed, expcom_bits_two_pow]

/-- The polynomial front end and simulator budget fit a linear exponential.

**Proof sketch.** Since `m + 1 ≤ 2^m`, both `m + 1` and `m + 2^m + 1`
are at most `2^(m+1)`. Raising to the two fixed degrees and increasing both
exponents to their sum gives a common power; its positivity absorbs the final
two transitions. -/
private lemma expcom_decider_budget (C c d m : ℕ) :
    2 * (C * (m + 1) ^ c) + d * (m + 2 ^ m + 1) ^ d + 2 ≤
      (2 * C + d + 2) * 2 ^ ((c + d) * (m + 1)) := by
  have hm : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have hbase : m + 2 ^ m + 1 ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    omega
  have he (e : ℕ) (he : e ≤ c + d) :
      (2 ^ (m + 1)) ^ e ≤ 2 ^ ((c + d) * (m + 1)) := by
    rw [← Nat.pow_mul, Nat.mul_comm (m + 1) e]
    exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ he)
  have hp : (m + 1) ^ c ≤ 2 ^ ((c + d) * (m + 1)) :=
    (Nat.pow_le_pow_left (by omega : m + 1 ≤ 2 ^ (m + 1)) c).trans (he c (by omega))
  have hs : (m + 2 ^ m + 1) ^ d ≤ 2 ^ ((c + d) * (m + 1)) :=
    (Nat.pow_le_pow_left hbase d).trans (he d (by omega))
  have hone : 1 ≤ 2 ^ ((c + d) * (m + 1)) := Nat.one_le_pow _ _ (by omega)
  calc
    _ = (2 * C) * (m + 1) ^ c + d * (m + 2 ^ m + 1) ^ d + 2 * 1 := by ring
    _ ≤ (2 * C) * 2 ^ ((c + d) * (m + 1)) +
        d * 2 ^ ((c + d) * (m + 1)) + 2 * 2 ^ ((c + d) * (m + 1)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hp)
        (Nat.mul_le_mul_left _ hs)) (Nat.mul_le_mul_left _ hone)
    _ = _ := by ring

/-- A genuine triple is in `EXPCOM` exactly when its bounded computation accepts.

**Proof sketch.** Inject the outer pair and then the inner pair; the lengths of
the equal unary tails identify the exponent. This is the one private reuse of
the frozen padding reduction's inline parse-uniqueness argument. -/
private lemma expcom_mem_triple (α x : List Bool) (n : ℕ) :
    pairEncode α (pairEncode x (List.replicate n true)) ∈ EXPCOM ↔
      (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n) := by
  constructor
  · rintro ⟨β, y, m, hz, hm⟩
    have hp : (α, pairEncode x (List.replicate n true)) =
        (β, pairEncode y (List.replicate m true)) := pairEncode_injective hz
    have hα : α = β := congrArg Prod.fst hp
    have hi : (x, List.replicate n true) = (y, List.replicate m true) :=
      pairEncode_injective (congrArg Prod.snd hp)
    have hx : x = y := congrArg Prod.fst hi
    have hn : n = m := by
      simpa only [List.length_replicate] using congrArg List.length (congrArg Prod.snd hi)
    simpa only [hα, hx, hn] using hm
  · intro h
    exact ⟨α, x, n, rfl, h⟩

/-- The uniform simulator computes the membership bit on the front end's image.

**Proof sketch.** On a genuine triple, the front end builds the canonical clock
and the two uniform simulator clauses decide the unique parsed computation.
Every component length is at most the original query length, so its exponential
budget dominates the simulator's polynomial in the numerical deadline. A failed
guard excludes membership and selects the zero-deadline input; its simulated
initial state is live, hence the simulator's rejection clause applies. -/
private lemma expcom_simulator_on_image (z : List Bool) :
    expCode.simulator.ComputesInTime (expcom_front z) [MultiTapeTM.indicator EXPCOM z]
      (expCode.simDegree * (z.length + 2 ^ z.length + 1) ^ expCode.simDegree) := by
  classical
  by_cases hok : expcom_ok z = true
  · obtain ⟨α, x, n, rfl⟩ := (expcom_ok_iff z).mp hok
    rw [expcom_front_triple]
    have hlen : α.length + x.length ≤
        (pairEncode α (pairEncode x (List.replicate n true))).length := by
      simp only [length_pairEncode, List.length_replicate]
      omega
    have hn : n ≤ (pairEncode α (pairEncode x (List.replicate n true))).length := by
      simp only [length_pairEncode, List.length_replicate]
      omega
    have hb : expCode.simDegree * (α.length + x.length + 2 ^ n + 1) ^ expCode.simDegree ≤
        expCode.simDegree *
          ((pairEncode α (pairEncode x (List.replicate n true))).length +
            2 ^ (pairEncode α (pairEncode x (List.replicate n true))).length + 1) ^
          expCode.simDegree := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      exact Nat.add_le_add_right
        (Nat.add_le_add hlen (Nat.pow_le_pow_right (by omega) hn)) 1
    by_cases hacc : (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)
    · have hmem := (expcom_mem_triple α x n).mpr hacc
      simpa [MultiTapeTM.indicator, hmem] using
        (expCode.simulator_accepts α x (2 ^ n) hacc).mono hb
    · have hnot : pairEncode α (pairEncode x (List.replicate n true)) ∉ EXPCOM :=
        fun hmem => hacc ((expcom_mem_triple α x n).mp hmem)
      simpa [MultiTapeTM.indicator, hnot] using
        (expCode.simulator_rejects α x (2 ^ n) hacc).mono hb
  · have hnot : z ∉ EXPCOM := by
      rintro ⟨α, x, n, hz, _⟩
      exact hok ((expcom_ok_iff z).mpr ⟨α, x, n, hz⟩)
    have hzero : ¬ (expCode.decode []).toFinTM.ComputesInTime [] [true] 0 :=
      FinTM.not_computesInTime_zero _ _ _
    have hu : expCode.simulator.ComputesInTime (expcom_front z)
        [MultiTapeTM.indicator EXPCOM z] expCode.simDegree := by
      simpa [expcom_front, hok, MultiTapeTM.indicator, hnot] using
        expCode.simulator_rejects [] [] 0 hzero
    apply hu.mono
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left expCode.simDegree
      (Nat.one_le_pow expCode.simDegree (z.length + 2 ^ z.length + 1) (Nat.succ_pos _))

/-- `EXPCOM` has a decider with a linear exponential time bound.
[AB09, Example 3.6(3), the query dispatcher]

**Proof sketch.** Use the polynomial front end to validate and rebuild the
simulator input, compose with the uniform simulator only on that image, then
absorb the polynomial setup and the simulator's budget into one fixed linear
exponent. Malformed queries have already been routed to the rejecting
zero-deadline input. -/
private theorem expcom_decider :
    ∃ (D : FinTM Bool) (A B : ℕ), D.DecidesInTime EXPCOM fun m => A * 2 ^ (B * (m + 1)) := by
  obtain ⟨M, C, c, hM⟩ := expcom_front_poly
  obtain ⟨D, hD⟩ := FinTM.exists_comp_on_image M expCode.simulator expcom_front
    (fun z => [MultiTapeTM.indicator EXPCOM z]) (fun n => C * (n + 1) ^ c)
    (fun n => expCode.simDegree * (n + 2 ^ n + 1) ^ expCode.simDegree)
    hM expcom_simulator_on_image
  exact ⟨D, 2 * C + expCode.simDegree + 2, c + expCode.simDegree,
    fun z => (hD z).mono (expcom_decider_budget C c expCode.simDegree z.length)⟩

/-- A constant bound is exponential-polynomial. -/
private theorem expcom_expPoly_const (A : ℕ) : ExpPoly fun _ => A :=
  (expPoly_poly A 0).of_le fun n => by simp

/-- `A · 2^(K·(n + 1)^k)` is exponential-polynomial. -/
private theorem expcom_expPoly_mul_two_pow (A K k : ℕ) : ExpPoly fun n => A * 2 ^ (K * (n + 1) ^ k) := by
  refine ⟨A + K, k, fun n => ?_⟩
  have h1 : A < 2 ^ A := Nat.lt_two_pow_self
  have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc A * 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ A * 2 ^ (K * (n + 1) ^ k) := Nat.mul_le_mul_right _ h1.le
    _ = 2 ^ (A + K * (n + 1) ^ k) := by rw [pow_add]
    _ ≤ 2 ^ ((A + K) * (n + 1) ^ k) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- **The summit's ledger** ([AB09, Example 3.6(3)]; the P3.2 round-2 uniform ledger in
this route's shape): the bound returned by `Complexity.exists_proj_decider` around the
certificate shell, the simulated choice machine and the `EXPCOM` decider is
exponential-polynomial. -/
private theorem expcom_summit_budget (a' A B b e b' C k : ℕ) :
    ExpPoly fun n => b' * 2 ^ (C * (n + 1) ^ k) *
      (b * ((n + C * (n + 1) ^ k + 1) ^ e +
          a' * (2 * (n + C * (n + 1) ^ k) + 2 + 1) *
            (2 * (n + C * (n + 1) ^ k) + 2 + 1 +
              A * 2 ^ (B * (2 * (n + C * (n + 1) ^ k) + 2 + 1)))) +
        (n + C * (n + 1) ^ k + 1) ^ (k + 1)) := by
  have hG : ∀ n : ℕ, n + C * (n + 1) ^ k + 1 ≤ (C + 1) * (n + 1) ^ (k + 1) := by
    intro n
    have h1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h3 : C * (n + 1) ^ k ≤ C * (n + 1) ^ (k + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
    calc n + C * (n + 1) ^ k + 1 = (n + 1) + C * (n + 1) ^ k := by ring
      _ ≤ (n + 1) ^ (k + 1) + C * (n + 1) ^ (k + 1) := Nat.add_le_add h1 h3
      _ = (C + 1) * (n + 1) ^ (k + 1) := by ring
  have eG : ∀ d, ExpPoly fun n => ((C + 1) * (n + 1) ^ (k + 1)) ^ d := fun d =>
    (expPoly_poly ((C + 1) ^ d) ((k + 1) * d)).of_le fun n =>
      le_of_eq (by rw [mul_pow, ← pow_mul])
  have e3G : ExpPoly fun n => 3 * ((C + 1) * (n + 1) ^ (k + 1)) :=
    (expPoly_poly (3 * (C + 1)) (k + 1)).of_le fun n => le_of_eq (by ring)
  have eExp := expcom_expPoly_mul_two_pow A (3 * B * (C + 1)) (k + 1)
  refine ((expcom_expPoly_mul_two_pow b' C k).mul (((expcom_expPoly_const b).mul ((eG e).add
    (((expcom_expPoly_const a').mul e3G).mul (e3G.add eExp)))).add (eG (k + 1)))).of_le
    fun n => ?_
  have hg := hG n
  generalize hgdef : n + C * (n + 1) ^ k = g at hg ⊢
  generalize hGdef : (C + 1) * (n + 1) ^ (k + 1) = G at hg ⊢
  have h3 : 2 * g + 2 + 1 ≤ 3 * G := by omega
  have hexp : A * 2 ^ (B * (2 * g + 2 + 1)) ≤ A * 2 ^ (3 * B * (C + 1) * (n + 1) ^ (k + 1)) := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by omega)
    calc B * (2 * g + 2 + 1) ≤ B * (3 * G) := Nat.mul_le_mul_left _ h3
      _ = 3 * B * (C + 1) * (n + 1) ^ (k + 1) := by rw [← hGdef]; ring
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add _ (Nat.pow_le_pow_left hg _)
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add (Nat.pow_le_pow_left hg _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) (Nat.add_le_add h3 hexp)

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
   `z ∈ EXPCOM` by running **`expCode.simulator`** on
   `⟨⟨bits 2^(n'), α'⟩, x'⟩`: its two uniform clauses make the answer the
   exact membership bit at cost `simDegree · (|α'| + |x'| + 2^(n') + 1) ^
   simDegree` — **uniform in the query's code**, which is the entire round-1
   repair (query codes vary with the branch; `Turing.timed_universal`'s
   per-code constant cannot pay for them) — with parse-uniqueness
   (`Turing.pairEncode_injective` twice, then `List.length` on the
   replicated tails) identifying the witness decomposition.
4. **Ledger.** Each branch submits queries of length at most the elapsed
   budget (`Turing.OracleTM.queryString_length_le` transferred along the
   simulation invariant), so `n' ≤ p n`, `|α'|, |x'| ≤ p n`, and one oracle call costs
   `simDegree · (3 · p n + 2^(p n) + 1) ^ simDegree = 2^(O(p n))` simulator
   steps; a round is `p n` simulated
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
budget normalization into `EXP`'s `2^(n^c)` form.

**Fill appendix (B5b, the §12.10 compositional route).** The hand-built route
above is superseded by design §12.10, decision 1, and wave-1 note 42.
`exists_proj_decider` enumerates certificates around the W2-V certificate shell
(`FinTM.exists_certificateShell`). The W2-C choice-word machine
(`FinOracleNDTM.exists_choiceTM`) handles nondeterministic choices; W2-S's single
oracle-call trace (`FinOracleTM.exists_plain_simulation_of_monotone`) supplies
the per-step simulation and resume seam, from the preloaded choice word.
The private `expcom_decider` answers queries by parsing, rebuilding the canonical
simulator input, and composing `expCode.simulator` only on that front end's image;
malformed queries select a fixed rejecting zero-deadline input. The transcribed
`ExpPoly` ledger absorbs the simulator, shell and projection-enumerator budgets.
The result is proved modulo exactly W2-S (`FinOracleTM.exists_plain_simulation`)
and the two §12.11 rows (`MachineFormat.exists_polyCanonizer` and
`MachineFormat.exists_uniformSimulator`). -/
theorem NPOracle_EXPCOM_subset_EXP : NPOracle EXPCOM ⊆ EXP := by
  intro L hL
  obtain ⟨k, a, N, hN⟩ := Set.mem_iUnion.mp hL
  obtain ⟨Mc, jc, hMc⟩ := FinOracleNDTM.exists_choiceTM N
  obtain ⟨D, A, B, hD⟩ := expcom_decider
  have hτ : Monotone fun m => A * 2 ^ (B * (m + 1)) := fun m m' hm =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega)))
  obtain ⟨P, a', hk, hP⟩ :=
    FinOracleTM.exists_plain_simulation_of_monotone Mc D EXPCOM _ hτ hD
  let jP : Fin P.k := ⟨jc.castSucc, lt_of_lt_of_le jc.castSucc.isLt hk⟩
  have hshell : ∀ x u : List Bool, u.length = 2 * a * (x.length + 1) ^ k →
      (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) jP u))
          ((fun m => a' * (2 * m + 2 + 1) *
            (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) (x.length + u.length))).state =
          none ∧
        (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) jP u))
          ((fun m => a' * (2 * m + 2 + 1) *
            (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) (x.length + u.length))).output =
          N.choiceOut EXPCOM x u := by
    intro x u _
    obtain ⟨h1, h2⟩ := hMc EXPCOM x u
    have hw : Function.update (fun _ : Fin (Mc.k + 1) => ([] : List Bool)) jc.castSucc u
        (Fin.last Mc.k) = [] := Function.update_of_ne (Fin.castSucc_ne_last jc).symm _ _
    obtain ⟨s, hs, hs1, hs2⟩ := hP x _ hw _ h1
    rw [FinTM.prefixWords_update _ _ hk] at hs1 hs2
    have hle : s ≤ a' * (2 * (x.length + u.length) + 2 + 1) *
        (2 * (x.length + u.length) + 2 + 1 +
          A * 2 ^ (B * (2 * (x.length + u.length) + 2 + 1))) := by
      refine hs.trans ?_
      have hu : u.length ≤ x.length + u.length := Nat.le_add_left _ _
      have h3 : 2 * u.length + 2 + 1 ≤ 2 * (x.length + u.length) + 2 + 1 := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h3)
        (Nat.add_le_add h3 (hτ (by omega : 2 * u.length + 2 ≤ 2 * (x.length + u.length) + 2)))
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs1]
      exact hs1
    · dsimp only
      rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs1]
      exact hs2.trans h2
  obtain ⟨V, bV, e, hV⟩ :=
    FinTM.exists_certificateShell P jP (2 * a) k (N.choiceOut EXPCOM)
      (fun m => a' * (2 * m + 2 + 1) * (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) hshell
  obtain ⟨b', E, hE⟩ := exists_proj_decider (2 * a) k _ _ V hV
  rw [FinTM.certificateShell_proj] at hE
  have hLeq : {x : List Bool | ∃ u, u.length = 2 * a * (x.length + 1) ^ k ∧
      N.choiceOut EXPCOM x u = [true]} = L :=
    Set.ext fun x => (FinOracleNDTM.mem_iff_exists_choiceOut hN x).symm
  rw [hLeq] at hE
  exact ExpPoly.mem_EXP (expcom_summit_budget a' A B bV e b' (2 * a) k)
    ⟨1, E, fun x => (hE x).mono (Nat.le_of_eq (Nat.one_mul _).symm)⟩

/-- **`P^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊇` is `Complexity.EXP_subset_POracle_EXPCOM`; `⊆` chains
`Complexity.POracle_subset_NPOracle` with
`Complexity.NPOracle_EXPCOM_subset_EXP`. -/
theorem POracle_EXPCOM_eq_EXP : POracle EXPCOM = EXP := by
  exact Set.Subset.antisymm
    ((POracle_subset_NPOracle EXPCOM).trans NPOracle_EXPCOM_subset_EXP)
    EXP_subset_POracle_EXPCOM

/-- **`NP^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊆` is `Complexity.NPOracle_EXPCOM_subset_EXP`; `⊇` chains
`Complexity.EXP_subset_POracle_EXPCOM` with
`Complexity.POracle_subset_NPOracle`. -/
theorem NPOracle_EXPCOM_eq_EXP : NPOracle EXPCOM = EXP := by
  apply Set.Subset.antisymm NPOracle_EXPCOM_subset_EXP
  simpa only [POracle_EXPCOM_eq_EXP] using POracle_subset_NPOracle EXPCOM

/-- **Relative to `EXPCOM`, determinism and nondeterminism coincide**:
`P^EXPCOM = NP^EXPCOM` — the `A` half of the Baker-Gill-Solovay theorem.
[AB09, Example 3.6(3), cited by the proof of Theorem 3.7]

**Proof sketch.** Chain `Complexity.POracle_EXPCOM_eq_EXP` with the inverse of
`Complexity.NPOracle_EXPCOM_eq_EXP`. -/
theorem POracle_EXPCOM_eq_NPOracle_EXPCOM : POracle EXPCOM = NPOracle EXPCOM := by
  exact POracle_EXPCOM_eq_EXP.trans NPOracle_EXPCOM_eq_EXP.symm

end Complexity
