# External audit pack — Chapter 2, epoch-2 fill gate

Audits the **proofs** of the ten epoch-2 targets — eleven public theorem
names (the ledger counts the Theorem-2.6 reverse inclusion and the
equality corollary as one target): `NP_subset_EXP`; `HALT_NPHard` and
`HALT_not_mem_NP`; `ntime_poly_subset_NP`; `NP_subset_iUnion_NTIME` with
`NP_eq_iUnion_NTIME`; `mem_NP_iff_exists_length_le`;
`timeConstructible_poly`; `TMSAT_mem_NP`; `TMSAT_NPHard`;
`TMSAT_NPComplete` — filled by **ten Codex commits across nine zip
deliveries** (four checkpoints, four continuations, B2) with **386 new
private declarations** in five files: `ClassNP/{EXP, Nondeterminism, NP,
Reductions, TMSAT}.lean`. With this gate the Chapter-2 ledger stands at
38 of 59 original admissions proved, and Theorem 2.6, Exercise 2.1, the
HALT pair, and Theorem 2.9 are end-to-end machine-checked.

The **statements are not in question here**: all eleven were frozen at
the phase-1/2/3 statement gates (`audits/ch2-phase{1,2,3}-*`), and the
span-wide freeze is independently attested below. This is the fill-epoch
proof audit in the mold of the epoch-1 and library fill gates: proof
correctness and helper hygiene against the frozen statements, the
inherited invariant tables (carried verbatim in the attached briefs),
and the audited machine-construction library. Gate closes on **zero
blockers/majors**. Record findings in `audits/ch2-epoch2-findings.md`.

**Evidence separation.** Out of scope: the machine-construction library
itself (`Build/`, two closed gates — consult `audits/ch1-infra-resolutions.md`
and `audits/ch1-libfill-resolutions.md`; its files are in the repository,
and the fills' *consumption* of its contracts is very much in scope); the
bridge `timed_universal_quantitative`'s statement and discharge
(sanctioned by 2D's bridge protocol, proof-audited at the infra gate —
its *consumption* by the TMSAT budget chain is in scope); the remaining
21 admissions (5 epoch-3 padding, `EXP_subset_NEXP`, 15 E3/E4 statement
layer — later epochs); the model files (attached as the definitions the
proofs elaborate against, audited in their own gates, not for re-audit).
Both continuation hosts disclosed a `/proc/<pid>/exe` shim; it never
entered the repository and is superseded by the maintainer's independent
fresh sweeps on an ordinary host.

## Maintainer-side integration attestations (verify or challenge)

The full evidence is the attached
`audits/evidence/ch2-epoch2/span-attestation.md`; summary:

1. **Whole-span freeze.** Over `f317f0c7` → `2e176f60`, the net diff of
   the five owned files deletes **exactly the eleven target `sorry`
   lines**, six append-only docstring tail splices, and 2C's one
   recorded token-identical statement-line rewrite — nothing else; and
   the name-level public surface is **identical everywhere except the
   one sanctioned bridge addition** in `TMSAT.lean`. Import drift:
   `Build.Primitives` per batch (route-forced) plus five disclosed
   modules, all order-legal.
2. **Per-delivery verification** (each recorded in the decision log at
   integration): checksums for all nine archives; per-patch
   deleted-lines audits; byte-identical format-patch replay in isolated
   worktrees before every `git am -3`; B2's attested source SHA-256
   reproduced; the three maintainer integration commits touch no source.
3. **Elaboration.** Fresh-olean sweeps at every integration, zero
   `error:` lines, admissions stepping 32 → 29 → 23 → **21**, each step
   predicted before the sweep and matched exactly. Final 57/57 sweep
   attached (`ch2-e2cont-B2-integration-sweep.log`).
4. **Axioms.** The maintainer closure traversal (attached committed
   program `audits/programs/ch2-e2-ClosureAxioms.lean`; attached log):
   all twelve closure names print at most the standard triple with
   **empty admission-root sets**; Chapter-1 headline and library
   regressions unchanged; `EXP_subset_NEXP` at exactly its own root.
   Intermediate traversals at both earlier integrations confirmed every
   interim root exactly as disclosed (the A/C cluster funneling through
   the single admitted private `enumMachine_contracts` before its
   continuation discharge).
5. **Policy.** Lint in scope: **0 FAIL, 3 WARN** — the recorded size
   exceptions (EXP 2,887 / Nondeterminism 2,627 / TMSAT 1,908 lines),
   each justified at integration under exclusive single-file fill
   ownership. Sketch docstrings extended append-only throughout;
   attributions intact.
6. **Deviations on record** (all disclosed at integration): all four
   initial deliveries were partials invoking their briefs'
   continuation provision; 2C's cosmetic statement-line respacing;
   both continuation hosts' cache-setup recoveries without touching
   pins; B2's `TAR_OPTIONS=--no-same-owner` cache recovery.

## Dispositions requested

* **E5 — dedup of superseded checkpoint privates.** The checkpoint
  strata contain helper families superseded by the continuations'
  library-based routes (A's `enumCarry*`/`enumCapture*`/`enumLoop_run`
  cluster; C's `prefixTM`/`fixedPair`, their promotion requests subsumed
  by library P3/P6; D's bespoke `polyUnaryTM`). Under the fills'
  **no-touch rule** (cite or ignore, never remove/modify) they remain in
  the files, admission-free but partially dead. Maintainer position:
  serial post-gate dedup under E5, with D7's split discipline
  (byte-identical relocation, ordered-sequence comparison, ride-along
  audit). Review the deferral; flag any superseded helper that is
  actually *consumed* by a final proof in a way that smuggles an
  unaudited route.
* **D7 extension — the ClassNP size exceptions.** EXP 2,887,
  Nondeterminism 2,627, TMSAT 1,908. Maintainer position: fold their
  splits into the already-approved trailing D7 queue
  (`Loop`/`Primitives`), same discipline, after this gate. Review
  whether anything forces a split before the E3 fills consume these
  files.
* **D6 (unchanged, for the record):** the two library shared-lemma
  promotions remain queued post-gate; no epoch-2 fill depends on them.

## What is under audit, and priorities

The eleven proofs and 386 private helpers, against the frozen
statements, the phase-gate invariant tables (in the attached briefs,
verbatim), the audited library contracts they consume, and the agent
reports (attached; challenge any attestation of theirs the maintainer
layer above does not independently cover). Priorities, riskiest first:

1. **The B2 reverse host** (`b2*`, 42 privates closing
   `NP_subset_iUnion_NTIME`). The five-step contract end to end: the
   **read-normalization seam** (`b2UnaryTM` changes only input reads;
   `b2_unary_run`'s exact-lockstep claim at every elapsed time;
   `b2_unary_first`'s transfer of the unary generator's first halt to
   arbitrary same-length inputs — this replaced the explicitly-missing
   scheduler relocation, so re-derive it, don't trust it); dispatch on
   the scheduler's **actual first halt**, never an upper bound as a
   clock; `b2_tables_coincide` as a definitional fact of the
   construction; all-branch totality with a **common** bound while
   actual per-branch halting times vary; the `C = 0`, degree-zero, and
   empty-input edges; the exact ledger `H(n) = 3n + Q(n) + τ(n) +
   A(n+Q(n)+1)^d + 5` and the `(B+A+5)·m^r` envelope feeding
   `cont_guess_normalize`'s frozen coefficient `K(C+1)^r·2^(r·max 1 c)`.
2. **The banked reverse assets** (B-cont, 36 privates): `contGuessTM`
   on the library's `captureAction`; coverage at **actual physical
   write positions** (`contSelect`/`cont_select_surjective`/
   `cont_guess_coverage`, zero-coefficient case included — never "the
   first Q(n) choices"); `cont_guess_time_bound`'s exact coefficient;
   `cont_guess_normalize`'s all-branch-halting route through
   `acceptsWithin_iff_of_halts` with both padding and backward
   truncation.
3. **The forward compiler** (`ntime_poly_subset_NP`): the phase-2
   invariant tables discharged in full; `cont_split_bridge :
   solveSplit C c = certificateSplit C c` proved by `rfl` — including
   the agent's recorded determination that the campaign's coefficient
   shift belongs to `NP.lean`'s padding convention, not this file; the
   `(A+13)(m+1)^(c+2)` envelope; the note-3 rule (no untimed
   composition, no bare computability substitution) everywhere.
4. **The enumerator discharge** (A-cont, 95 privates):
   `enumMachine_contracts` as an `exists_loopCfgTM` instantiation —
   §9b instance data (exact-width invariant, `incFixed`-getD-stall
   step, `R = 2^w − 1`, fuel `replicate w true` via the
   `Nat.bits (2^w − 1)` induction); the stall bridge to the
   checkpoint's rank enumeration; the configuration-export translation
   (round-3 item 5) — and the fact that **three targets funnel through
   this one private**, so an error here fells the A/C cluster.
5. **The TMSAT budget chain** (D, 87 privates): D-MEM's quadruple
   parser under the exact-value discipline; the clock conversion
   (`pairMapSnd` + `lengthBits`); the odd split at `(1,1)`; D-WRAP as
   `pairValid` + `pairConcat` + capture; D-EMIT's §9c pairing recipe
   over exact unary runs with the explicit `T'` deadline formula
   (never majorizing the certificate length); the bridge consumed
   through its public statement only.
6. **Exercise 2.1** (C, 54 privates incl. the HALT pair's 16 in
   `Reductions.lean`): both P8 orientations through the §9c recipe;
   the mandated **P10 at `(C+1, c)` / P8 at `(C, c)`** coefficient
   shift; the original-bound-test rule; the HALT pair's reduction
   plumbing against the frozen `Reductions.lean` vocabulary.
7. **Checkpoint strata and hygiene** (147 checkpoint privates): the
   superseded families are admission-free and untouched per the
   no-touch rule — verify no final proof silently routes through a
   superseded helper whose own contract was never finished; privates
   match their stated contracts; nothing public-worthy smuggled
   private beyond the recorded D6 requests; library contracts consumed
   at their audited statements (C's fourteen, A's catalog instances,
   B's `captureAction`/`splitSolve`, D's primitive rows); the
   deliveries' own kernel-traversal claims spot-checked against the
   attached program and logs.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch2-epoch2-findings.md`; this pack is immutable once sent
(errata via the resolutions file).

## Verification appendix (runs and manifest)

* Integration sweeps (fresh-olean, zero errors): 53/53 at 29 admissions
  (checkpoints), 57/57 at 23 (continuations), 57/57 at **21** (B2;
  attached). Logs: `audits/logs/ch2-e2-checkpoint-*`,
  `ch2-e2cont-{sweep,axioms,lint}.log`, `ch2-e2cont-B2-*` (committed;
  final three attached).
* Closure attestation: `ch2-e2cont-B2-axioms.log` (attached), from the
  attached committed program — exit 0, every expectation met.
* Lint: `ch2-e2cont-B2-lint.log` (attached): 0 FAIL / 3 WARN in scope,
  as itemized in attestation 5.
* Bundle manifest — **34 attachments** after the pack: the 5 owned
  sources (`EXP`, `Nondeterminism`, `NP`, `Reductions`, `TMSAT`); the
  4 model files (`TuringMachine/Nondeterministic`, `ClassNP/NTIME`,
  `ClassNP/PolyTime`, `ClassP/P`); the 9 briefs
  (`ch2-epoch2-batch{A,B,C,D}`, `ch2-e2cont-batch{A,B,C,D}`,
  `ch2-e2cont-batchB2`); the 10 agent documents (9 REPORTs + batch C's
  filed continuation plan); the closure program; the 3 final logs
  (sweep, axioms, lint); the span attestation; the 57-module order
  list. Total 5 + 4 + 9 + 10 + 1 + 3 + 1 + 1 = 34. The phase-1/2/3
  findings/resolutions, both library-gate records, the design document
  (§9b/§9c), and all earlier logs are committed in the repository at
  the paths the briefs and reports cite.

## ===== TCSlib/Complexity/ClassNP/EXP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

open Turing Turing.FinTM

/-! ### Private certificate enumeration infrastructure -/

/-- Little-endian value, including leading zeroes at the high end. -/
private def enumValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * enumValue bs + if b then 1 else 0

/-- Increment without extending the width; `none` means exhaustion.
The empty word overflows, so its caller must test it before incrementing. -/
private def enumInc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (enumInc bs).map (false :: ·)

/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
private def enumWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)

/-- Every width-`w` word has value strictly below `2^w`. -/
private lemma enumValue_lt (u : List Bool) : enumValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [enumValue]
  | cons b u ih =>
    cases b <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.pow_succ] <;> omega

/-- The representation retains exactly the requested width, even at zero. -/
private lemma enumWord_length (w i : ℕ) : (enumWord w i).length = w := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih => simp only [enumWord, List.length_cons, ih]

/-- The initial rank is represented by precisely the all-false word. -/
private lemma enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- In range, the representation has the specified value.
**Proof sketch.** Remove the low bit by division by two. The quotient is
in range for the remaining width, and the remainder is either zero or one. -/
private lemma enumWord_value (w i : ℕ) (hi : i < 2 ^ w) :
    enumValue (enumWord w i) = i := by
  induction w generalizing i with
  | zero => simp only [Nat.pow_zero] at hi; simp [enumWord, enumValue, show i = 0 by omega]
  | succ w ih =>
    have hdiv : i / 2 < 2 ^ w := by rw [Nat.pow_succ] at hi; omega
    simp only [enumWord, enumValue, ih (i / 2) hdiv]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    split <;> simp_all <;> omega

/-- Equal-length words with the same value are equal, including trailing
false bits. The parity determines the first bit; divide the remainder by two. -/
private lemma enumValue_injective (u v : List Bool) (hlen : u.length = v.length)
    (hval : enumValue u = enumValue v) : u = v := by
  induction u generalizing v with
  | nil => simpa using hlen.symm
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons b' v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases b <;> cases b' <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte] at hval
      all_goals first | omega | exact congrArg (_ :: ·) (ih v hlen' (by omega))

/-- Every word is the unique representative of its rank at its own width. -/
private lemma enumWord_complete (u : List Bool) :
    enumWord u.length (enumValue u) = u := by
  exact enumValue_injective _ _ (enumWord_length _ _)
    (enumWord_value _ _ (enumValue_lt u))

/-- One fixed-width increment either preserves width and adds one to the
value, or reports overflow exactly at the last rank.
**Proof sketch.** A low false bit changes to true. A low true bit is cleared
and passes the carry to the suffix; suffix overflow is total overflow. -/
private lemma enumInc_spec (u : List Bool) :
    match enumInc u with
    | some v => v.length = u.length ∧ enumValue v = enumValue u + 1
    | none => enumValue u + 1 = 2 ^ u.length := by
  induction u with
  | nil => simp [enumInc, enumValue]
  | cons b u ih =>
    cases b with
    | false => simp [enumInc, enumValue]
    | true =>
      cases he : enumInc u with
      | none =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_none, enumValue, ↓reduceIte,
          List.length_cons, Nat.pow_succ]
        omega
      | some v =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_some, enumValue, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact ⟨by omega, by omega⟩

/-- On canonical candidates, increment advances exactly one rank and reports
overflow only after the last rank. This includes width zero. -/
private lemma enumInc_word (w i : ℕ) (hi : i < 2 ^ w) :
    enumInc (enumWord w i) =
      if i + 1 < 2 ^ w then some (enumWord w (i + 1)) else none := by
  have hs := enumInc_spec (enumWord w i)
  rw [enumWord_length, enumWord_value w i hi] at hs
  cases he : enumInc (enumWord w i) with
  | none => simp only [he] at hs; simp [show ¬i + 1 < 2 ^ w by omega]
  | some v =>
    simp only [he] at hs
    have hv := enumValue_lt v
    rw [hs.1, hs.2] at hv
    rw [if_pos hv]
    congr 1
    exact enumValue_injective v _ (hs.1.trans (enumWord_length _ _).symm)
      (hs.2.trans (enumWord_value w (i + 1) hv).symm)

/-- No candidate repeats among the `2^w` in-range ranks. -/
private lemma enumWord_no_repeat (w i j : ℕ) (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (h : enumWord w i = enumWord w j) : i = j := by
  have := congrArg enumValue h
  simpa only [enumWord_value w i hi, enumWord_value w j hj] using this

/-- Exact-width existential certificates are exactly the in-range candidates. -/
private lemma enumCandidates_iff (w : ℕ) (p : List Bool → Prop) :
    (∃ u, u.length = w ∧ p u) ↔ ∃ i, i < 2 ^ w ∧ p (enumWord w i) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact ⟨enumValue u, enumValue_lt u, by simpa only [enumWord_complete] using hu⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨enumWord w i, enumWord_length w i, hp⟩

/-- Resulting tape contents and success flag of a fixed-width carry. Overflow
clears the entire word and returns false; it never writes an extra bit. -/
private def enumBump : List Bool → List Bool × Bool
  | [] => ([], false)
  | false :: bs => (true :: bs, true)
  | true :: bs => (false :: (enumBump bs).1, (enumBump bs).2)

/-- The number of leading true bits crossed by the carry. -/
private def enumCarryPos : List Bool → ℕ
  | true :: bs => enumCarryPos bs + 1
  | _ => 0

/-- The carry visits at most the candidate width before detecting overflow. -/
private lemma enumCarryPos_le (u : List Bool) : enumCarryPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [enumCarryPos, List.length_cons] <;> omega

/-- The physical carry's tape contents always retain the original width. -/
private lemma enumBump_length (u : List Bool) : (enumBump u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [enumBump, ih]

/-- The carry's success flag and tape contents implement `enumInc` exactly. -/
private lemma enumBump_inc (u : List Bool) :
    enumInc u = if (enumBump u).2 then some (enumBump u).1 else none := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | false => rfl
    | true => simp only [enumInc, enumBump, ih]; split <;> rfl

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma enumBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma enumBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width increment, followed by a rewind. The live states are
carry (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def enumCarryTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some true => ⟨0, fun _ => (some (some false), .pos), none, some (.inl none)⟩
          | some false => ⟨0, fun _ => (some (some true), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the carry tape, with arbitrary native input-head position. -/
private def enumCarryCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg enumCarryTM.k Bool enumCarryTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One carry transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma enumCarry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    enumCarryTM.tm.step (enumCarryCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => enumCarryCfg x p (.inl (some false)) (pre.length - 1) pre
      | false :: us => enumCarryCfg x p (.inl (some true)) (pre.length - 1) (pre ++ true :: us)
      | true :: us => enumCarryCfg x p (.inl none) (pre.length + 1) (pre ++ false :: us) := by
  unfold MultiTapeTM.step
  change (enumCarryTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, enumBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact enumBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The carry phase takes one step beyond the leading true prefix, including
one blank test on overflow.
**Proof sketch.** Induct on the remaining candidate. Each true bit is cleared
and added to the processed prefix. A false bit or the right blank starts
rewind without changing the width. -/
private lemma enumCarry_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) pre.length (pre ++ u))
        (enumCarryPos u + 1) =
      enumCarryCfg x p (.inl (some (enumBump u).2))
        ((pre.length : ℤ) + enumCarryPos u - 1) (pre ++ (enumBump u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
      enumCarry_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | false =>
      simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
        enumCarry_step x p pre (false :: u)
    | true =>
      simp only [enumCarryPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCarry_step]
      simpa [enumBump, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [false])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma enumCarry_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = enumCarryCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : enumCarryTM.tm.step
        (enumCarryCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width increment and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading true-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns overflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma enumCarry_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * enumCarryPos u + 2 ≤ 2 * u.length + 2 ∧
      enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) 0 u)
          (2 * enumCarryPos u + 2) =
        enumCarryCfg x p (.inr (enumBump u).2) 0 (enumBump u).1 := by
  refine ⟨by have := enumCarryPos_le u; omega, ?_⟩
  have hr := enumCarry_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * enumCarryPos u + 2 = (enumCarryPos u + 1) + (enumCarryPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact enumCarry_rewind x p (enumBump u).1 (enumBump u).2 _
    (by rw [enumBump_length]; exact enumCarryPos_le u)

section EnumCapture

variable {S : Type} [Fintype S] [DecidableEq S]
variable (M : FinTM Bool) (r : ℕ) (next : Option Bool → S)
variable (control : S → Option Bool → (Fin (M.k + (1 + r)) → Option Bool) →
  Action (M.k + (1 + r)) Bool (((Option M.State × Option Bool) × Bool) ⊕ S))

/-- Run a verifier on a work-tape input buffer, capture its first output bit
in finite control, and return live to a controller with access to all tapes.
The tape blocks are verifier work, input buffer, and `r` retained tapes.
The boundary tag supplies the verifier's native clamping behavior. The real
input head and retained tapes do not move during a call. -/
private def enumCaptureTM : FinTM Bool where
  k := M.k + (1 + r)
  State := ((Option M.State × Option Bool) × Bool) ⊕ S
  tm :=
    { q₀ := .inl ((some M.tm.q₀, none), true)
      tr := fun q inp work => match q with
        | .inl ((some q, reg), tag) =>
          let v := work (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1)))
          let a := M.tm.tr q v (fun i => work (Fin.castAdd (1 + r) i))
          let m := virtualMove tag v a.inputTape
          ⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
            some (.inl ((a.state, reg.or a.output), virtualNextTag tag m))⟩
        | .inl ((none, reg), _) => controlAction 0 (some (.inr (next reg)))
        | .inr q => control q inp work }

/-- A complete call invariant: exact source work tapes, an unchanged virtual
input buffer, arbitrary retained tapes, source output captured in finite
control, and empty physical output. The native input `x` can differ from
the verifier input `y`. -/
private def enumCaptureCfg {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) :
    Cfg (enumCaptureTM M r next control).k Bool
      (enumCaptureTM M r next control).State x where
  state := some (.inl ((cfg.state, cfg.output.head?), tag))
  inputPos := p
  workTapes := tapeBlocks cfg.workTapes (bufferTape y) tapes
  workTapePos := tapeBlocks cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1) heads
  output := []

/-- One live source transition is simulated in one physical step, updating
the captured bit before recording a possible halt.
**Proof sketch.** Buffer reads equal native source reads. The virtual movement
lemma proves both clamping and preservation of the boundary tag. The verifier
work block changes in lockstep; the other tape contents are unchanged. The
head-of-append identity gives the captured bit, even on the halting action. -/
private lemma enumCapture_step {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hs : cfg.state ≠ none) :
    ∃ tag', VirtualTag (M.tm.step cfg).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.step
          (enumCaptureCfg M r next control cfg tag p tapes heads) =
        enumCaptureCfg M r next control (M.tm.step cfg) tag' p tapes heads := by
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : M.tm.step cfg = a.apply cfg := by simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs' : (enumCaptureCfg M r next control cfg tag p tapes heads).state =
          some (.inl ((some q, cfg.output.head?), tag)) := by simp [enumCaptureCfg, hq]
      have hv : (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1))) = cfg.inputSymbol := by
        simp [enumCaptureCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.castAdd (1 + r) i)) = cfg.workTapeSymbols := by
        funext i
        simp [enumCaptureCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs']
      dsimp only [enumCaptureTM]
      rw [hv, hr, hq]
      change (⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
        some (.inl ((a.state, cfg.output.head?.or a.output), virtualNextTag tag m))⟩ :
        Action (M.k + (1 + r)) Bool _).apply _ =
          enumCaptureCfg M r next control (a.apply cfg) _ p tapes heads
      refine Cfg.ext ?_ (moveInputPos_zero p) ?_ ?_ ?_
      · simp [enumCaptureCfg, Action.apply, List.head?_append, Option.head?_toList]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [enumCaptureCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · simp [enumCaptureCfg, Action.apply]

/-- Lockstep through the first source halt, with an exact virtual-input
simulation, no physical emissions, and all retained tapes intact. -/
private lemma enumCapture_run {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    ∃ tag', VirtualTag (M.tm.runFrom cfg t).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control cfg tag p tapes heads) t =
        enumCaptureCfg M r next control (M.tm.runFrom cfg t) tag' p tapes heads := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', he⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨tag'', htag'', he'⟩ :=
      enumCapture_step M r next control _ tag' htag' p tapes heads (h t (by omega))
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The administrative return step dispatches on the updated register and
preserves every tape, head, and the empty physical output. -/
private lemma enumCapture_transfer {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (h : cfg.state = none) :
    (enumCaptureTM M r next control).tm.step
        (enumCaptureCfg M r next control cfg tag p tapes heads) =
      { enumCaptureCfg M r next control cfg tag p tapes heads with
        state := some (.inr (next cfg.output.head?)) } := by
  unfold MultiTapeTM.step
  simp only [enumCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Given a prepared buffer and fresh source tapes, a singleton-output call
returns its bit to the live controller within the source budget plus one.
This holds for any native input and parked head, including empty verifier
input. The complete returned configuration certifies retention and silence.
**Proof sketch.** Take the first source halting time. Start its virtual head
at cell zero with the right-boundary-compatible tag `true`. Apply lockstep
through the halt, then transfer. Absorbing source halting identifies its full
configuration with the one at the supplied budget. -/
private lemma enumCapture_returns (x y : List Bool) (b : Bool) (T : ℕ)
    (p : Fin (x.length + 2)) (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hM : M.ComputesInTime y [b] T) :
    ∃ t, t ≤ T + 1 ∧ ∃ tag,
      VirtualTag (M.tm.runFrom (M.tm.initCfg y) T).inputPos tag ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control (M.tm.initCfg y) true p tapes heads) t =
        { enumCaptureCfg M r next control (M.tm.runFrom (M.tm.initCfg y) T)
            tag p tapes heads with state := some (.inr (next (some b))) } := by
  classical
  obtain ⟨hh, hout⟩ := (computesInTime_iff M y [b] T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg y) t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  have hs : (M.tm.runFrom (M.tm.initCfg y) t).state = none := Nat.find_spec hex
  have he : M.tm.runFrom (M.tm.initCfg y) T = M.tm.runFrom (M.tm.initCfg y) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  obtain ⟨tag, htag, hr⟩ := enumCapture_run M r next control (M.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    (fun s hs => Nat.find_min hex hs)
  refine ⟨t + 1, by omega, tag, by rwa [he], ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hr,
    enumCapture_transfer M r next control _ tag p tapes heads hs, ← he, hout]
  rfl

end EnumCapture

/-- Boolean result of testing `count` consecutive candidate ranks, starting
with `i`. The recursive branch represents one rejected call. -/
private def enumAny (accept : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => false
  | count + 1 => if accept i then true else enumAny accept (i + 1) count

/-- The abstract loop accepts exactly when an in-range candidate accepts.
**Proof sketch.** Separate the first rank from the remaining interval. -/
private lemma enumAny_iff (accept : ℕ → Bool) (i count : ℕ) :
    enumAny accept i count = true ↔
      ∃ j, i ≤ j ∧ j < i + count ∧ accept j = true := by
  induction count generalizing i with
  | zero =>
    simp only [enumAny, Bool.false_eq_true, false_iff]
    rintro ⟨j, hj, hj', _⟩
    omega
  | succ count ih =>
    change (if accept i then true else enumAny accept (i + 1) count) = true ↔ _
    by_cases h : accept i = true
    · simp only [if_pos h, true_iff]
      exact ⟨i, le_refl _, by omega, h⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hj', ha⟩
        exact ⟨j, by omega, by omega, ha⟩
      · rintro ⟨j, hj, hj', ha⟩
        have hne : j ≠ i := by intro he; subst j; exact h ha
        exact ⟨j, by omega, by omega, ha⟩

/-- For the actual verifier's indicator, testing all ranks gives exactly the
definition's existential over certificates of width `w`. This is independent
of the machine implementation, and includes width zero. -/
private lemma enumAny_certificates (x : List Bool) (w : ℕ) (V : Language Bool) :
    enumAny (fun i => MultiTapeTM.indicator V (x ++ enumWord w i)) 0 (2 ^ w) = true ↔
      ∃ u, u.length = w ∧ x ++ u ∈ V := by
  classical
  rw [enumAny_iff, enumCandidates_iff]
  simp [MultiTapeTM.indicator]

/-- A timed loop invariant combines bounded accept-or-advance segments into
one bounded singleton-output computation. The terminal configuration is the
post-overflow rejection configuration, so every candidate, including the last,
is tested before exhaustion.
**Proof sketch.** Induct on the remaining number of candidates. Acceptance
terminates immediately. Rejection advances to the next canonical configuration;
compose run segments and add their bounds. This lemma does not assert that
any particular machine satisfies the required per-round contracts. -/
private lemma enumLoop_run (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (accept : ℕ → Bool) (B i count : ℕ)
    (hend : (cfg (i + count)).state = none ∧ (cfg (i + count)).output = [false])
    (hround : ∀ j, i ≤ j → j < i + count → ∃ t, t ≤ B ∧
      if accept j then
        (M.tm.runFrom (cfg j) t).state = none ∧ (M.tm.runFrom (cfg j) t).output = [true]
      else M.tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t, t ≤ count * B ∧ (M.tm.runFrom (cfg i) t).state = none ∧
      (M.tm.runFrom (cfg i) t).output = [enumAny accept i count] := by
  induction count generalizing i with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [enumAny] using hend
  | succ count ih =>
    obtain ⟨t, ht, hc⟩ := hround i (le_refl _) (by omega)
    by_cases hb : accept i = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simpa [enumAny, hb] using hc.2
    · simp only [hb] at hc
      have hend' : (cfg (i + 1 + count)).state = none ∧
          (cfg (i + 1 + count)).output = [false] := by
        simpa only [show i + 1 + count = i + (count + 1) by omega] using hend
      obtain ⟨s, hs, hhalt, hout⟩ := ih (i + 1) hend'
        (fun j hj hj' => hround j (by omega) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [enumAny, hb] using hout

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma enumExponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- The audited round budget is pointwise bounded by an `EXP` budget, for
all coefficients and degrees, including zero.
**Proof sketch.** Set `k=max 1 c`. Both `n+1` and the width are bounded by
constant multiples of `(n+1)^k`. Replace the polynomial round overhead by
`2^(d·(n+width+1))`, add the exponents, and use `enumExponent_bound`. -/
private lemma enumBudget_bound (a C c d : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
        A * 2 ^ n ^ e := by
  let k := max 1 c
  let K := C + d * (C + 1)
  obtain ⟨A, e, hA⟩ := enumExponent_bound K k
  refine ⟨a * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 c)
  have hn : n + 1 ≤ (n + 1) ^ k := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left 1 c)
  have hw : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ k := by
    calc n + C * (n + 1) ^ c + 1 = (n + 1) + C * (n + 1) ^ c := by omega
         _ ≤ (n + 1) ^ k + C * (n + 1) ^ k :=
           Nat.add_le_add hn (Nat.mul_le_mul_left C hc)
         _ = (C + 1) * (n + 1) ^ k := by ring
  have he : C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
      K * (n + 1) ^ k := by
    calc C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
        C * (n + 1) ^ k + d * ((C + 1) * (n + 1) ^ k) :=
          Nat.add_le_add (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left d hw)
         _ = K * (n + 1) ^ k := by dsimp [K]; ring
  have hb : (n + C * (n + 1) ^ c + 1) ^ d ≤
      2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
    calc (n + C * (n + 1) ^ c + 1) ^ d ≤
        (2 ^ (n + C * (n + 1) ^ c + 1)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) d
         _ = 2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  calc a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
      a * (2 ^ (C * (n + 1) ^ c) * 2 ^ (d * (n + C * (n + 1) ^ c + 1))) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hb
       _ = a * 2 ^ (C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1)) := by
        rw [Nat.pow_add]
       _ ≤ a * 2 ^ (K * (n + 1) ^ k) :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) he)
       _ ≤ a * A * 2 ^ n ^ e := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (hA n)

/-- The catalog counter and the predecessor's counter have the same recursive
equations, including overflow on the empty word. -/
private lemma enumCont_inc_eq (s : List Bool) : incFixed s = enumInc s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp only [incFixed, enumInc, ih]

/-- Stalling on overflow preserves the exact candidate width. -/
private lemma enumCont_step_length (s : List Bool) :
    ((incFixed s).getD s).length = s.length := by
  rw [enumCont_inc_eq]
  have h := enumInc_spec s
  cases hi : enumInc s with
  | none => rfl
  | some u => simp only [hi] at h; exact h.1

/-- Before exhaustion, the stalled catalog orbit is exactly the predecessor's
rank enumeration. No identity is asserted at the terminal rank `2^w`.
**Proof sketch.** The initial word is `enumWord w 0`. At a successor rank
still below `2^w`, the proved increment equation returns `some` of the next
word, so the fallback branch is never used. -/
private lemma enumCont_orbit (w : ℕ) : ∀ i, i < 2 ^ w →
    (fun s => (incFixed s).getD s)^[i] (List.replicate w false) =
      enumWord w i := by
  intro i
  induction i with
  | zero => intro _; exact (enumWord_zero w).symm
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), enumCont_inc_eq,
      enumInc_word w i (by omega), if_pos hi]
    rfl

/-- The exact fuel word is a unary all-true word of the certificate width.
**Proof sketch.** At successor width, `2^(w+1)-1 = 2*(2^w-1)+1`;
`Nat.bit1_bits` prepends a true bit. The base case is zero fuel. -/
private lemma enumCont_fuel_bits (w : ℕ) :
    Nat.bits (2 ^ w - 1) = List.replicate w true := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hp : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have he : 2 ^ (w + 1) - 1 = 2 * (2 ^ w - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [he, Nat.bit1_bits, ih, List.replicate_succ]

/-- A history tape can contain blank entries; its length is tracked on a
separate all-true clock tape. Cells outside its finite list are blank. -/
private def enumCont_sparse (w : List (Option Bool)) (z : ℤ) : Option Bool :=
  if 0 ≤ z then (w[z.toNat]?).join else none

/-- Appending a possibly blank history symbol writes just the next cell. -/
private lemma enumCont_sparse_append (w : List (Option Bool)) (b : Option Bool) :
    enumCont_sparse (w ++ [b]) =
      Function.update (enumCont_sparse w) (w.length : ℤ) b := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp [enumCont_sparse]
  · rw [Function.update_of_ne hz]
    by_cases hnonneg : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [enumCont_sparse, if_pos hnonneg]
      by_cases hlt : z.toNat < w.length
      · rw [List.getElem?_append_left hlt]
      · have hgt : w.length + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by omega)]
    · simp only [enumCont_sparse, if_neg hnonneg]

/-- Erasing the last history cell recovers its prefix, even if the erased
entry was itself blank. -/
private lemma enumCont_sparse_erase (w : List (Option Bool)) (b : Option Bool) :
    Function.update (enumCont_sparse (w ++ [b])) (w.length : ℤ) none =
      enumCont_sparse w := by
  rw [enumCont_sparse_append, Function.update_idem]
  have hblank : enumCont_sparse w (w.length : ℤ) = none := by
    simp [enumCont_sparse]
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Three tape symbols encode the three source head moves. -/
private def enumCont_moveCode : SignType → Option Bool
  | .neg => some false
  | .zero => none
  | .pos => some true

/-- Decode the inverse move for the backward restoration pass. -/
private def enumCont_unmove : Option Bool → SignType
  | some false => .pos
  | none => .zero
  | some true => .neg

/-- A recorded move and its inverse cancel as integer head displacements. -/
private lemma enumCont_unmove_cast (d : SignType) :
    (enumCont_unmove (enumCont_moveCode d)).cast = -(d.cast : ℤ) := by
  cases d <;> rfl

/-- A history entry retains every overwritten symbol and every source move.
No source state or native-input movement is needed for work-tape restoration. -/
private abbrev EnumContEntry (k : ℕ) :=
  (Fin k → Option Bool) × (Fin k → SignType)

/-- Instrument one source action with a clock cell and two history tracks per
source tape. The source action and output are otherwise unchanged. -/
private def enumCont_logAction {k : ℕ} {S : Type} (old : Fin k → Option Bool)
    (a : Action k Bool S) : Action (k + (1 + (k + k))) Bool S :=
  ⟨a.inputTape,
    tapeBlocks a.workTapes (some (some true), .pos)
      (Fin.addCases (fun i => (some (old i), .pos))
        (fun i => (some (enumCont_moveCode (a.workTapes i).2), .pos))),
    a.output, a.state⟩

/-- The logged source keeps its original finite state set. The extra tapes
are a unary step clock, old-symbol histories, and movement histories. -/
private def enumCont_logTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + (1 + (M.k + M.k))
  State := M.State
  tm := {
    q₀ := M.tm.q₀
    tr := fun q inp work =>
      let old := fun i : Fin M.k => work (Fin.castAdd (1 + (M.k + M.k)) i)
      enumCont_logAction old (M.tm.tr q inp old) }

/-- The correspondence stores exactly the source configuration and the
finite history; every history head is one cell past the recorded entries. -/
private def enumCont_logCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) :
    Cfg (k + (1 + (k + k))) Bool S x :=
  ⟨c.state, c.inputPos,
    tapeBlocks c.workTapes (bufferTape (List.replicate h.length true))
      (Fin.addCases (fun i => enumCont_sparse (h.map (fun e => e.1 i)))
        (fun i => enumCont_sparse (h.map (fun e => enumCont_moveCode (e.2 i))))),
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), c.output⟩

/-- One logged action preserves source semantics and appends exactly one
history entry, including a halting or emitting action.
**Proof sketch.** Split the physical tapes into source, clock, old-symbol,
and movement blocks. Source fields apply the original action; each history
field is the single-cell append identity at its current length. -/
private lemma enumCont_log_apply {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (a : Action k Bool S) :
    (enumCont_logAction c.workTapeSymbols a).apply (enumCont_logCfg c h) =
      enumCont_logCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
          List.replicate_add, bufferTape_append]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            enumCont_sparse_append, Fin.addCases]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            Fin.addCases]

/-- Record precisely the actions actually executed by a source run. No entry
is added after the source has halted. -/
private def enumCont_history {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) : ℕ → List (EnumContEntry k)
  | 0 => []
  | t + 1 =>
    let c := tm.runFrom c₀ t
    match c.state with
    | none => enumCont_history tm c₀ t
    | some q => enumCont_history tm c₀ t ++
        [(c.workTapeSymbols, fun i => ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).2)]

/-- Logging is lockstep with the source, from arbitrary prepared source
configurations. The source input, output, and halting time are unchanged.
**Proof sketch.** Induct on elapsed time. Halted configurations remain fixed;
otherwise the source-block reads agree and `enumCont_log_apply` records the
next action. This also covers the final emission on the halting action. -/
private lemma enumCont_log_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ) :
    (enumCont_logTM M).tm.runFrom (enumCont_logCfg c₀ []) t =
      enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    let c := M.tm.runFrom c₀ t
    have hr : (fun i : Fin M.k =>
        (enumCont_logCfg c (enumCont_history M.tm c₀ t)).workTapeSymbols
          (Fin.castAdd (1 + (M.k + M.k)) i)) = c.workTapeSymbols := by
      funext i
      simp [enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hsrun : (M.tm.runFrom c₀ t).state = c.state := rfl
    cases hs : c.state with
    | none =>
      have hn : (M.tm.runFrom c₀ t).state = none := hsrun.trans hs
      simp only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step,
        enumCont_history, enumCont_logCfg, hn]
    | some q =>
      have hq : (M.tm.runFrom c₀ t).state = some q := hsrun.trans hs
      have hstate : (enumCont_logCfg (M.tm.runFrom c₀ t)
          (enumCont_history M.tm c₀ t)).state = some q := hq
      simp only [MultiTapeTM.step, hstate]
      change (enumCont_logAction _ ((M.tm.tr q _ _))).apply _ = _
      rw [hr, enumCont_log_apply]
      simp only [enumCont_history, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.step, hq]
      rfl

/-- The restoration controller alternates inverse head movement with writing
the old symbols. It erases history as it goes and halts with history heads at
zero when the clock's left blank is reached. Native input is stationary. -/
private def enumCont_undoTM (k : ℕ) : FinTM Bool where
  k := k + (1 + (k + k))
  State := Option (Fin k → Option Bool)
  tm := {
    q₀ := none
    tr := fun q _ work => match q with
      | none =>
        if (work (Fin.natAdd k (Fin.castAdd (k + k) 0))).isSome then
          ⟨0, tapeBlocks
            (fun i => (none, enumCont_unmove
              (work (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i))))))
            (some none, 0) (fun _ => (some none, 0)), none,
            some (some (fun i => work (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))))⟩
        else
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos)
            (fun _ => (none, .pos)), none, none⟩
      | some old =>
        ⟨0, tapeBlocks (fun i => (some (old i), 0)) (none, .neg)
          (fun _ => (none, .neg)), none, some none⟩ }

/-- At a restoration checkpoint the heads inspect the last remaining
history entry. The native input position and source control are irrelevant
to undoing the source work fields, so the former is explicit. -/
private def enumCont_undoCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some none, p, (enumCont_logCfg c h).workTapes,
    tapeBlocks c.workTapePos ((h.length : ℤ) - 1) (fun _ => (h.length : ℤ) - 1), []⟩

/-- The completed restoration retains exactly the source's initial work
fields and leaves every history tape blank with its head at zero. -/
private def enumCont_undoResult {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨none, p, (enumCont_logCfg c []).workTapes,
    tapeBlocks c.workTapePos 0 (fun _ => 0), []⟩

/-- Undoing a tape write at the old head restores its original contents,
including no-write actions and writes of blank. -/
private lemma enumCont_restore_cell {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (i : Fin k) :
    Function.update ((a.apply c).workTapes i) (c.workTapePos i) (c.workTapeSymbols i) =
      c.workTapes i := by
  rw [Action.apply_workTapes, Function.update_idem]
  exact Function.update_eq_self _ _

/-- Erasing the last clock mark exposes exactly the preceding clock word. -/
private lemma enumCont_clock_erase (n : ℕ) :
    Function.update (bufferTape (List.replicate (n + 1) true)) (n : ℤ) none =
      bufferTape (List.replicate n true) := by
  rw [List.replicate_add, List.replicate_one, bufferTape_append,
    List.length_replicate, Function.update_idem]
  have hblank : bufferTape (List.replicate n true) (n : ℤ) = none := by simp
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Between inverse movement and inverse writing, the source heads are back
at their old positions and the last history entry is already erased. -/
private def enumCont_undoMid {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some (some c.workTapeSymbols), p, (enumCont_logCfg (a.apply c) h).workTapes,
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), []⟩

/-- The first restoration transition reverses the last source head moves,
retains the old symbols in finite control, and erases their history cells.
**Proof sketch.** At the newest clock mark, the parallel tracks read the
last appended entry. The inverse displacement returns every source head to
its pre-action location. Single-cell erase identities recover each prefix. -/
private lemma enumCont_undo_back {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step
      (enumCont_undoCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) =
      enumCont_undoMid c a h p := by
  let u := enumCont_undoCfg (a.apply c)
    (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p
  have hc : u.workTapeSymbols (Fin.natAdd k (Fin.castAdd (k + k) 0)) = some true := by
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  have ho : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))) = c.workTapeSymbols := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse]
  have hm : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i)))) =
      fun i => enumCont_moveCode (a.workTapes i).2 := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse, Fin.addCases]
    congr 3
    apply Fin.ext
    simp
  change ((enumCont_undoTM k).tm.tr none _ u.workTapeSymbols).apply u = _
  simp only [enumCont_undoTM, hc, Option.isSome_some, ↓reduceIte]
  rw [ho]
  have hm' (i : Fin k) := congrFun hm i
  have herase (f : EnumContEntry k → Option Bool) (b : Option Bool) :
      Function.update (enumCont_sparse (h.map f ++ [b])) (h.length : ℤ) none =
        enumCont_sparse (h.map f) := by
    simpa only [List.length_map] using enumCont_sparse_erase (h.map f) b
  simp only [hm']
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
          tapeBlocks, enumCont_clock_erase]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
            tapeBlocks, Fin.addCases, herase]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks,
        enumCont_unmove_cast]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks, Fin.addCases]

/-- The second restoration transition writes the retained old symbols and
backs the history heads up to the preceding entry. -/
private lemma enumCont_undo_write {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoMid c a h p) =
      enumCont_undoCfg c h p := by
  change ((enumCont_undoTM k).tm.tr (some c.workTapeSymbols) _ _).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
        Action.apply, tapeBlocks] using enumCont_restore_cell c a j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
          Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply,
          tapeBlocks, sub_eq_add_neg]

/-- With no history left, one silent transition restores the history heads
to zero and halts. This also handles a source that took no steps. -/
private lemma enumCont_undo_empty {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoCfg c [] p) =
      enumCont_undoResult c p := by
  change ((enumCont_undoTM k).tm.tr none _ _).apply _ = _
  have hc : (enumCont_undoCfg c [] p).workTapeSymbols
      (Fin.natAdd k (Fin.castAdd (k + k) 0)) = none := by
    simp [enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  simp only [enumCont_undoTM, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]

/-- A logged live source prefix can be completely undone in `2t+1` steps.
The theorem restores the full original work tapes and heads, with blank
history, while preserving any supplied native input position.
**Proof sketch.** Peel the last source action. Two proved transitions first
reverse its moves and erase its history, then restore its overwritten cells.
Induction undoes the shorter prefix; the empty prefix takes one final step. -/
private lemma enumCont_undo_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_undoTM M.k).tm.runFrom
      (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p) (2 * t + 1) =
      enumCont_undoResult c₀ p := by
  induction t with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, MultiTapeTM.runFrom_zero,
      enumCont_history, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
      using enumCont_undo_empty c₀ p
  | succ t ih =>
    have hs : (M.tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (M.tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      have he : 2 * (t + 1) + 1 = 2 + (2 * t + 1) := by omega
      let c := M.tm.runFrom c₀ t
      let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
      have hsrun : M.tm.runFrom c₀ (t + 1) = a.apply c := by
        rw [MultiTapeTM.runFrom_succ_eq_step']
        simp only [MultiTapeTM.step, hq]
        rfl
      have hhist : enumCont_history M.tm c₀ (t + 1) =
          enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)] := by
        simp only [enumCont_history, hq]
        rfl
      have htwo : (enumCont_undoTM M.k).tm.runFrom
          (enumCont_undoCfg (a.apply c)
            (enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) 2 =
          enumCont_undoCfg c (enumCont_history M.tm c₀ t) p := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
          MultiTapeTM.runFrom_zero, enumCont_undo_back, enumCont_undo_write]
      rw [hsrun, hhist, he, MultiTapeTM.runFrom_add, htwo]
      exact ih (fun j hj => hlive j (by omega))

/-- Any known halted endpoint is reached at the first halting time, with a
live source at every earlier time. The bound is never increased. -/
private lemma enumCont_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) (T : ℕ)
    (hh : (tm.runFrom c₀ T).state = none) :
    ∃ t ≤ T, (∀ j < t, ¬(tm.runFrom c₀ j).Halted) ∧
      tm.runFrom c₀ t = tm.runFrom c₀ T := by
  classical
  have hex : ∃ t, (tm.runFrom c₀ t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  refine ⟨t, ht, fun j hj => Nat.find_min hex hj, ?_⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
  rw [hr, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]

/-- Administrative actions preserve the source bank and only move the native
input and the final capture tape. -/
private def enumCont_bufferAction {L : ℕ} {H : Type}
    (m d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨m, fun i => (none, if i.val < L then 0 else d), none, q⟩

/-- Entry into restoration moves all history heads from the right blank to
the newest entry, leaving source heads fixed. -/
private def enumCont_undoEntry (k : ℕ) :
    Action (enumCont_undoTM k).k Bool (enumCont_undoTM k).State :=
  ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, .neg)),
    none, some none⟩

/-- A clean subroutine logs and captures a source, undoes all source work,
rewinds the native input and captured word, and halts silently. Its retained
output word lives on the last work tape; it emits no physical output. -/
private def enumCont_cleanTM (M : FinTM Bool) : FinTM Bool where
  k := (enumCont_logTM M).k + 1
  State := M.State ⊕ (Fin 6 ⊕ (enumCont_undoTM M.k).State)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl q => captureAction Sum.inl (.inr (.inl 0))
          ((enumCont_logTM M).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inr q) => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
          ((enumCont_undoTM M.k).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inl q) => match q.val with
        | 0 => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
            (enumCont_undoEntry M.k)
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inl 3)))
        | 3 => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
        | 4 => match work (Fin.last (enumCont_logTM M).k) with
          | some _ => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
          | none => enumCont_bufferAction 0 .pos (some (.inr (.inl 5)))
        | _ => controlAction 0 none }

/-- Clean administrative configurations expose only the native and capture
heads. The source work fields are already restored and the histories blank. -/
private def enumCont_cleanCfg (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ) :
    Cfg (enumCont_cleanTM M).k Bool (enumCont_cleanTM M).State x :=
  ⟨q, p,
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapes ⟨i, hi⟩ else bufferTape y),
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapePos ⟨i, hi⟩ else h), []⟩

/-- The clean subroutine's first phase is the public captured simulation of
the logged source. Halting emissions are retained on the capture tape. -/
private lemma enumCont_clean_capture (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
      captureCfg Sum.inl (.inr (.inl 0)) [] []
        (enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t)) := by
  rw [capture_run (enumCont_logTM M).tm (enumCont_cleanTM M).tm Sum.inl (.inr (.inl 0))
    (fun _ _ _ => rfl) [] [] (enumCont_logCfg c₀ []) t]
  · rw [enumCont_log_run]
  · intro j hj
    rw [enumCont_log_run]
    exact hlive j hj

/-- After source halt, one silent dispatch parks every history head on its
last entry and starts the captured restoration, retaining the source output. -/
private lemma enumCont_clean_undo_entry (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (h : List (EnumContEntry M.k))
    (hs : c.state = none) :
    (enumCont_cleanTM M).tm.step
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c h)) =
      captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1)) c.output []
        (enumCont_undoCfg c h c.inputPos) := by
  have hstate : (captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM M).State))
      (.inr (.inl 0)) [] [] (enumCont_logCfg c h)).state = some (.inr (.inl 0)) := by
    simp [captureCfg, enumCont_logCfg, hs]
  simp only [MultiTapeTM.step, hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg, List.nil_append, List.append_nil]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, j.isLt]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, sub_eq_add_neg]

/-- The captured restoration returns within `2t+1` steps with the original
source work restored and its completed output retained separately.
**Proof sketch.** Take the restoration machine's first halt below its proved
exact bound, apply `capture_run`, and identify the returned configuration
field by field. Its empty output appends nothing to the retained source word. -/
private lemma enumCont_clean_restore (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    ∃ r ≤ 2 * t + 1,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1))
          (M.tm.runFrom c₀ t).output []
          (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)) r =
        enumCont_cleanCfg M c₀ (M.tm.runFrom c₀ t).output
          (some (.inr (.inl 1))) p ((M.tm.runFrom c₀ t).output.length : ℤ) := by
  have hu := enumCont_undo_run M c₀ p t hlive
  obtain ⟨r, hr, hl, he⟩ := enumCont_first_halt (enumCont_undoTM M.k).tm
    (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)
    (2 * t + 1) (by rw [hu]; rfl)
  refine ⟨r, hr, ?_⟩
  rw [capture_run (enumCont_undoTM M.k).tm (enumCont_cleanTM M).tm
    (fun q => .inr (.inr q)) (.inr (.inl 1)) (fun _ _ _ => rfl)
    _ [] _ r hl, he, hu]
  simp [captureCfg, enumCont_undoResult, enumCont_cleanCfg, enumCont_logCfg,
    enumCont_logTM, enumCont_undoTM]
  exact ⟨rfl, rfl⟩

/-- Moving the clean subroutine's two exposed heads preserves every tape and
the empty physical output. -/
private lemma enumCont_buffer_apply (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q q' : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (m d : SignType) :
    (enumCont_bufferAction m d q').apply (enumCont_cleanCfg M c₀ y q p h) =
      enumCont_cleanCfg M c₀ y q' (moveInputPos p m) (h + d.cast) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext i
  by_cases hi : i.val < (enumCont_logTM M).k <;>
    simp [enumCont_bufferAction, enumCont_cleanCfg, Action.apply, hi]

/-- A mandatory left step followed by a boundary scan restores the native
head in at most its old position plus two steps. This private derivation
uses the proved `rewind_scan`, following the timed wrapper's template. -/
private lemma enumCont_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- The retained output word rewinds without being erased. Starting just
left of cell `j`, the scan returns its head to zero in exactly `j+1` steps. -/
private lemma enumCont_clean_buffer_rewind (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ y.length →
      (enumCont_cleanTM M).tm.runFrom
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1)) (j + 1) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) p 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
    have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((0 : ℤ) - 1)).workTapeSymbols
        (Fin.last (enumCont_logTM M).k) = none := by
      simp [enumCont_cleanCfg, Cfg.workTapeSymbols]
    simp only [enumCont_cleanTM, Nat.cast_zero]
    rw [hr, enumCont_buffer_apply]
    simp [SignType.cast]
  | succ j ih =>
    intro hj
    have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
    rw [hz, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (enumCont_cleanTM M).tm.step
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
      have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j).workTapeSymbols
          (Fin.last (enumCont_logTM M).k) = some (y[j]'(by omega)) := by
        simp [enumCont_cleanCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < y.length)]
      simp only [enumCont_cleanTM, hr]
      rw [enumCont_buffer_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- A halting source call can be made clean: retain its output on the final
tape, restore every source work field, blank all histories, and rewind both
exposed heads. The full duration is at most `3T+|x|+|y|+8`.
**Proof sketch.** Capture the logged run through its first halt; undo the
recorded actions; rewind native input; rewind the retained word; halt. Each
administrative transition is charged, and all phases keep physical output
empty. Only the actual source time is used in the restoration bound. -/
private lemma enumCont_clean_complete (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom c₀ T).state = none)
    (ho : (M.tm.runFrom c₀ T).output = y) :
    ∃ τ ≤ 3 * T + x.length + y.length + 8,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) τ =
        enumCont_cleanCfg M c₀ y none 1 0 := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M.tm c₀ T hh
  have hs : (M.tm.runFrom c₀ t).state = none := by rw [he]; exact hh
  have hout : (M.tm.runFrom c₀ t).output = y := by rw [he]; exact ho
  have hcap := enumCont_clean_capture M c₀ t hlive
  have hentry := enumCont_clean_undo_entry M (M.tm.runFrom c₀ t)
    (enumCont_history M.tm c₀ t) hs
  obtain ⟨r, hr, hrest⟩ := enumCont_clean_restore M c₀ (M.tm.runFrom c₀ t).inputPos t hlive
  have hfirst : (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) (t + 1 + r) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ) := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', hcap, hentry, hrest, hout]
  obtain ⟨u, hu, hrew⟩ := enumCont_rewind (enumCont_cleanTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inl 3)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
      (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) rfl
  have hrew' : (enumCont_cleanTM M).tm.runFrom
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) u =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ) := hrew
  have hback : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ)) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) 1 ((y.length : ℤ) - 1) := by
    change (enumCont_bufferAction 0 .neg _).apply _ = _
    rw [enumCont_buffer_apply]
    simp [sub_eq_add_neg, SignType.cast]
  have hlast : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) 1 0) =
      enumCont_cleanCfg M c₀ y none 1 0 := by
    change (controlAction 0 none).apply _ = _
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_cleanCfg]
  refine ⟨t + 1 + r + u + 1 + (y.length + 1) + 1, ?_, ?_⟩
  · change u ≤ (M.tm.runFrom c₀ t).inputPos.val + 2 at hu
    have hp := (M.tm.runFrom c₀ t).inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_add _ _ (y.length + 1),
      MultiTapeTM.runFrom_succ_eq_step' (t := t + 1 + r + u),
      MultiTapeTM.runFrom_add _ _ u, hfirst, hrew', hback,
      enumCont_clean_buffer_rewind M c₀ y 1 y.length (le_refl _), hlast]

/-- The assembly source emits native input followed by the candidate already
on its sole work tape. Its two phases never write the candidate. -/
private def enumCont_concatTM : FinTM Bool where
  k := 1
  State := Bool
  tm := {
    q₀ := false
    tr := fun q inp work =>
      if q then match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some true⟩
        | none => controlAction 0 none
      else match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some false⟩
        | none => controlAction 0 (some true) }

/-- Assembly configurations keep the candidate word fixed while exposing
the input head, candidate head, and emitted prefix. -/
private def enumCont_concatCfg (x s : List Bool) (q : Option Bool)
    (p : Fin (x.length + 2)) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool Bool x := ⟨q, p, fun _ => bufferTape s, fun _ => z, out⟩

/-- The native-input scan emits exactly the remaining input and switches to
the candidate phase, preserving the candidate and its head at zero.
**Proof sketch.** Induct on the remaining native suffix. A bit is emitted
and advances the native head; the right blank takes one silent phase change. -/
private lemma enumCont_concat_native (x s pre rest : List Bool) (hx : x = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre)
      (rest.length + 1) =
      enumCont_concatCfg x s (some true) (Fin.last (x.length + 1)) 0 x := by
  induction rest generalizing pre with
  | nil =>
    have hp : x = pre := by simpa using hx
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have hr : (enumCont_concatCfg x s (some false) ⟨x.length + 1, by omega⟩ 0 x).inputSymbol =
        none := by simp [enumCont_concatCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr false _ _).apply _ = _
    simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hr]
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_concatCfg]
    rfl
  | cons b rest ih =>
    have hread : (enumCont_concatCfg x s (some false)
        ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre).inputSymbol = some b := by
      rw [inputSymbol_at _ pre.length (by simp [hx]) rfl]
      simp [hx]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre) =
        enumCont_concatCfg x s (some false)
          ⟨(pre ++ [b]).length + 1, by simp [hx]⟩ 0 (pre ++ [b]) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr false _ _).apply _ = _
      simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · apply Fin.ext
        dsimp only [Action.apply, enumCont_concatCfg]
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx])]
        simp
      · funext i; simp [Action.apply, enumCont_concatCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hx)

/-- The candidate scan appends the exact tape word to the emitted native
input and halts at its right blank. Empty candidates take the final step. -/
private lemma enumCont_concat_candidate (x s pre rest : List Bool) (p : Fin (x.length + 2)) (out : List Bool)
    (hs : s = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some true) p pre.length (out ++ pre))
      (rest.length + 1) =
      enumCont_concatCfg x s none p s.length (out ++ s) := by
  induction rest generalizing pre with
  | nil =>
    have hp : s = pre := by simpa using hs
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr true _ _).apply _ = _
    simp only [enumCont_concatTM, ↓reduceIte, enumCont_concatCfg, Cfg.workTapeSymbols,
      bufferTape_nat, List.getElem?_length]
    rw [controlAction_apply]
    simp [moveInputPos_zero]
  | cons b rest ih =>
    have hr : (enumCont_concatCfg x s (some true) p
        pre.length (out ++ pre)).workTapeSymbols 0 = some b := by
      simp [enumCont_concatCfg, Cfg.workTapeSymbols, hs]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some true) p pre.length (out ++ pre)) =
        enumCont_concatCfg x s (some true) p
          (pre ++ [b]).length (out ++ (pre ++ [b])) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr true _ _).apply _ = _
      simp only [enumCont_concatTM, ↓reduceIte, hr]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext i; simp [enumCont_concatCfg, Action.apply]
      · simp [enumCont_concatCfg, Action.apply, List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hs)

/-- Assembly from the candidate seam emits exactly `x ++ s` in
`|x|+|s|+2` steps. The fixed candidate tape is retained. -/
private lemma enumCont_concat_run (x s : List Bool) :
    enumCont_concatTM.tm.runFrom
      (Cfg.ofWords (input := x) false (fun _ => s)) (x.length + s.length + 2) =
      enumCont_concatCfg x s none (Fin.last (x.length + 1)) s.length (x ++ s) := by
  have hn := enumCont_concat_native x s [] x rfl
  have hs := enumCont_concat_candidate x s [] s (Fin.last (x.length + 1)) x rfl
  simp only [List.length_nil, List.append_nil, Nat.zero_add,
    Nat.cast_zero] at hn hs
  have hp : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by apply Fin.ext; simp
  rw [hp] at hn
  change enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some false) 1 0 []) _ = _
  rw [show x.length + s.length + 2 = (x.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hn, hs]

/-- Buffered composition also works from a prepared first-machine work
configuration. Its second machine still receives genuine fresh work tapes.
**Proof sketch.** Use the first source halt, the public buffered lockstep and
rewind equations, then the public relocated second-phase simulation. -/
private lemma enumCont_prepared_comp (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M₁.k Bool M₁.State x) (y z : List Bool) (T₁ T₂ : ℕ)
    (hh : (M₁.tm.runFrom c₀ T₁).state = none)
    (ho : (M₁.tm.runFrom c₀ T₁).output = y)
    (h₂ : M₂.ComputesInTime y z T₂) :
    ∃ t ≤ T₁ + y.length + 2 + T₂,
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).state = none ∧
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).output = z := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M₁.tm c₀ T₁ hh
  let c := M₁.tm.runFrom c₀ t
  have hs : c.state = none := by dsimp [c]; rw [he]; exact hh
  have hout : c.output = y := by dsimp [c]; rw [he]; exact ho
  have hfirst := bufferedFirstCfg_run M₁ M₂ c₀ t hlive
  have hrew := bufferedFirstCfg_rewind M₁ M₂ c hs
  obtain ⟨tag, _, hrun⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg c.output) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
    c.inputPos c.workTapes c.workTapePos T₂
  have h₂' : (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).state = none ∧
      (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).output = z := by
    rw [hout]
    exact (computesInTime_iff _ _ _ _).mp h₂
  refine ⟨t + (c.output.length + 2) + T₂, by rw [hout]; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hfirst, hrew, hrun]
  exact ⟨by simp only [bufferedSecondCfg, h₂'.1, Option.map_none], h₂'.2⟩

/-- The prepared assembly source occupies tape zero; the composition buffer
and verifier work tapes are exactly blank at the candidate seam. -/
private lemma enumCont_round_seam (MV : FinTM Bool) (x s : List Bool) (phase : Bool) :
    bufferedFirstCfg enumCont_concatTM MV (Cfg.ofWords (input := x) phase (fun _ => s)) =
      Cfg.ofWords (.inl (some phase) : (bufferedCompTM enumCont_concatTM MV).State)
        (stateWord (bufferedCompTM enumCont_concatTM MV).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
      simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks, enumCont_concatTM]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]

/-- The prepared verifier call accepts the exact assembled input `x ++ s`.
Its bound includes assembly, the buffer rewind, and the verifier's actual
polynomial budget on that input. -/
private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
    ∃ t ≤ a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4,
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).output =
        [MultiTapeTM.indicator V (x ++ s)] := by
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM MV
    (Cfg.ofWords (input := x) false (fun _ => s)) (x ++ s)
    [MultiTapeTM.indicator V (x ++ s)] (x.length + s.length + 2)
    (a * ((x ++ s).length + 1) ^ d)
    (by rw [enumCont_concat_run]; rfl) (by rw [enumCont_concat_run]; rfl) (hV (x ++ s))
  rw [enumCont_round_seam MV x s false] at hh ho
  simp only [List.length_append] at ht
  exact ⟨t, by omega, hh, ho⟩

/-- Relabel live states and redirect halt to a live return state, preserving
the complete action. This wrapper is used only for already-silent calls. -/
private def enumCont_returnAction {k : ℕ} {S H : Type}
    (emb : S → H) (ret : H) (a : Action k Bool S) : Action k Bool H :=
  ⟨a.inputTape, a.workTapes, a.output, some ((a.state.map emb).getD ret)⟩

/-- The live-return correspondence preserves all configuration fields except
the control state, including work-tape results. -/
private def enumCont_returnCfg {k : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (ret : H) (c : Cfg k Bool S x) : Cfg k Bool H x :=
  ⟨some ((c.state.map emb).getD ret), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- A host with the redirected transition table simulates a source through
its first halt and returns the exact completed configuration.
**Proof sketch.** One redirected action commutes with the configuration map.
Induct through live source steps; a halting action selects the live return
state while preserving its final writes and output. -/
private lemma enumCont_return_run {k : ℕ} {S H : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (ret : H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_returnAction emb ret (tm.tr q inp work))
    (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c₀ j).Halted) :
    host.runFrom (enumCont_returnCfg emb ret c₀) t =
      enumCont_returnCfg emb ret (tm.runFrom c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    have hs : (tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      simp only [MultiTapeTM.step, enumCont_returnCfg, hq, Option.map_some, Option.getD_some]
      rw [htr]
      rfl

/-- Combining the prepared verifier call with the clean wrapper gives a
repeatable call: the candidate is retained, all other original source work
is restored to blank, and the sole verdict is held on the capture tape.
The concrete body still has to dispatch, clear that verdict, and increment. -/
private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
    let Q := bufferedCompTM enumCont_concatTM MV
    let c₀ := Cfg.ofWords (input := x) Q.tm.q₀ (stateWord Q.k s)
    ∃ t ≤ 3 * (a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4) +
        x.length + 9,
      (enumCont_cleanTM Q).tm.runFrom
        (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
        enumCont_cleanCfg Q c₀ [MultiTapeTM.indicator V (x ++ s)] none 1 0 := by
  dsimp only
  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V a d hV x s
  obtain ⟨r, hr, he⟩ := enumCont_clean_complete (bufferedCompTM enumCont_concatTM MV)
    (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
      (stateWord (bufferedCompTM enumCont_concatTM MV).k s))
    [MultiTapeTM.indicator V (x ++ s)] t hh ho
  exact ⟨r, by simp only [List.length_singleton] at hr; omega, he⟩

/-- Pad an action with inactive high tapes and embed its finite control. -/
private def enumCont_padAction {k K : ℕ} {S H : Type}
    (emb : S → H) (a : Action k Bool S) : Action K Bool H :=
  ⟨a.inputTape, fun i => if hi : i.val < k then a.workTapes ⟨i, hi⟩ else (none, 0),
    a.output, a.state.map emb⟩

/-- Pad a source configuration with blank stationary high tapes. -/
private def enumCont_padCfg {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) : Cfg K Bool H x :=
  ⟨c.state.map emb, c.inputPos,
    (fun i => if hi : i.val < k then c.workTapes ⟨i, hi⟩ else fun _ => none),
    (fun i => if hi : i.val < k then c.workTapePos ⟨i, hi⟩ else 0), c.output⟩

/-- Padding commutes with one action; the new high tapes remain blank. -/
private lemma enumCont_pad_apply {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) (a : Action k Bool S) :
    (enumCont_padAction (K := K) emb a).apply (enumCont_padCfg emb c) =
      enumCont_padCfg emb (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]

/-- A machine may run on an initial tape block of a larger controller.
**Proof sketch.** The source-block reads agree when the source fits. One
step commutes with padding, including the absorbing halted case; iterate. -/
private lemma enumCont_pad_run {k K : ℕ} {S H : Type} {x : List Bool}
    (hk : k ≤ K) (tm : MultiTapeTM k Bool S) (host : MultiTapeTM K Bool H)
    (emb : S → H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_padAction emb (tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (c : Cfg k Bool S x) (t : ℕ) :
    host.runFrom (enumCont_padCfg emb c) t = enumCont_padCfg emb (tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step (enumCont_padCfg emb) ?_ c t
  intro c
  cases hq : c.state with
  | none => simp only [MultiTapeTM.step, enumCont_padCfg, hq, Option.map_none]
  | some q =>
    have hs : (enumCont_padCfg (K := K) emb c).state = some (emb q) := by
      simp only [enumCont_padCfg, hq, Option.map_some]
    have hw : (fun i : Fin k => (enumCont_padCfg (K := K) emb c).workTapeSymbols
        ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i
      simp [enumCont_padCfg, Cfg.workTapeSymbols, i.isLt]
    have hin : (enumCont_padCfg (K := K) emb c).inputSymbol = c.inputSymbol := rfl
    simp only [MultiTapeTM.step, hs, hq]
    rw [htr, hw, hin, enumCont_pad_apply]

/-- Three finite source routines share a common padded tape block. The
startup routine is the initial branch; prepared calls may select either
other branch without moving their candidate off tape zero. -/
private def enumCont_sources (Q R U : FinTM Bool) : FinTM Bool where
  k := Q.k + R.k + U.k
  State := Q.State ⊕ (R.State ⊕ U.State)
  tm := {
    q₀ := .inr (.inr U.tm.q₀)
    tr := fun q inp work => match q with
      | .inl q => enumCont_padAction Sum.inl
          (Q.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inl q) => enumCont_padAction (fun q => .inr (.inl q))
          (R.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inr q) => enumCont_padAction (fun q => .inr (.inr q))
          (U.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩)) }

/-- Move or write the candidate at tape zero and the final capture tape,
preserving every intervening tape. -/
private def enumCont_endsAction {L : ℕ} {H : Type}
    (a b : Option (Option Bool)) (d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨0, fun i => if i.val = 0 then (a, d) else if i.val = L then (b, d) else (none, 0), none, q⟩

/-- The concrete body uses one clean source block for initialization,
verification, and increment. Administrative states are the anchor (0),
seed copy (1), unused reserve (2), verdict (3), increment check (4), result
copy (5), and synchronized rewind (6). The stopped variant freezes only
the anchor and is used to certify first returns without an interior visit. -/
private def enumCont_bodyTM (B : FinTM Bool) (qverify qinc : B.State) (stopped : Bool) :
    FinTM Bool where
  k := (enumCont_logTM B).k + 1
  State := ((enumCont_cleanTM B).State × Fin 3) ⊕ Fin 7
  tm := {
    q₀ := .inl ((enumCont_cleanTM B).tm.q₀, 0)
    tr := fun q inp work => match q with
      | .inl (q, mode) => enumCont_returnAction (fun q => .inl (q, mode))
          (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
          ((enumCont_cleanTM B).tm.tr q inp work)
      | .inr q => match q.val with
        | 0 => if stopped then controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inl (.inl qverify, 1)))
        | 3 => match work (Fin.last (enumCont_logTM B).k) with
          | some true => ⟨0, fun _ => (none, 0), some true, none⟩
          | _ => ⟨0, fun i => (if i.val = (enumCont_logTM B).k then some none else none, 0),
              none, some (.inl (.inl qinc, 2))⟩
        | 4 => if work (Fin.last (enumCont_logTM B).k) = none then
              controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inr 5))
        | 6 => match work 0 with
          | some _ => enumCont_endsAction none none .neg (some (.inr 6))
          | none => enumCont_endsAction none none .pos (some (.inr 0))
        | _ => match work (Fin.last (enumCont_logTM B).k) with
          | some b => enumCont_endsAction (some (some (if q.val = 1 then false else b)))
              (some none) .pos (some (.inr q))
          | none => enumCont_endsAction none none .neg (some (.inr 6)) }

/-- Starting assembly in its candidate phase supplies just that candidate to
the catalog incrementer. Its output is empty exactly on overflow; a clean
wrapper will retain the original candidate for that branch. -/
private lemma enumCont_increment_call (I : FinTM Bool) (j : ℕ)
    (hI : I.ComputesFunInTime (fun s => (incFixed s).getD []) (fun n => j * (n + 1)))
    (x s : List Bool) :
    ∃ t ≤ (j + 3) * (s.length + 1),
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).output =
        (incFixed s).getD [] := by
  have hs := enumCont_concat_candidate x s [] s 1 [] rfl
  simp only [List.length_nil, List.nil_append, Nat.cast_zero] at hs
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM I
    (Cfg.ofWords (input := x) true (fun _ => s)) s ((incFixed s).getD [])
    (s.length + 1) (j * (s.length + 1))
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).state = none
        rw [hs]; rfl)
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).output = s
        rw [hs]; rfl) (hI s)
  rw [enumCont_round_seam I x s true] at hh ho
  refine ⟨t, ht.trans ?_, hh, ho⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Padding preserves the candidate-on-zero convention when the source has
at least one work tape. All added tapes are blank and parked at zero. -/
private lemma enumCont_pad_words {k K : ℕ} {S H : Type} (hk : 0 < k) (_hle : k ≤ K)
    (emb : S → H) (q : S) (x s : List Bool) :
    enumCont_padCfg (K := K) emb (Cfg.ofWords (input := x) q (stateWord k s)) =
      Cfg.ofWords (emb q) (stateWord K s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k
    · simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi, hn]
  · funext i
    simp [enumCont_padCfg, Cfg.ofWords]

/-- The same padding identity for empty initial work is valid even when the
source machine has no work tapes. -/
private lemma enumCont_pad_init {k K : ℕ} {S H : Type} (emb : S → H)
    (q : S) (x : List Bool) :
    enumCont_padCfg (k := k) (K := K) emb (Cfg.init q x) =
      Cfg.ofWords (emb q) (stateWord K []) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords, stateWord]
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords]

/-- Overwriting the first remaining candidate cell extends the completed
prefix and drops the old cell, also when the old word is initially empty. -/
private lemma enumCont_overwrite (pre old : List Bool) (b : Bool) :
    Function.update (bufferTape (pre ++ old)) (pre.length : ℤ) (some b) =
      bufferTape (pre ++ b :: old.drop 1) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ pre.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hp : 0 < z.toNat - pre.length := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
        rw [hm]
        cases old <;> simp
    · simp [bufferTape, h0]

/-- The erased capture prefix consists entirely of blanks. Replacing its
next symbol by blank increases that prefix by one cell. -/
private lemma enumCont_sparse_clear (p : ℕ) (b : Bool) (rest : List Bool) :
    Function.update (enumCont_sparse (List.replicate p none ++ (b :: rest).map some))
      (p : ℤ) none =
      enumCont_sparse (List.replicate (p + 1) none ++ rest.map some) := by
  funext z
  by_cases hz : z = (p : ℤ)
  · subst z; simp [enumCont_sparse, List.getElem?_append]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ p := by omega
      by_cases hp : z.toNat < p
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show z.toNat < p + 1 by omega]
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show ¬z.toNat < p + 1 by omega,
          show z.toNat - p = (z.toNat - (p + 1)) + 1 by omega]
    · simp [enumCont_sparse, h0]

/-- Tape configurations for the administrative copy and rewind scans. Only
the candidate and final capture tape may be nonblank; their heads coincide. -/
private def enumCont_pairCfg {L : ℕ} {S : Type} {x : List Bool}
    (q : Option S) (u v : ℤ → Option Bool) (h : ℤ) : Cfg (L + 1) Bool S x :=
  ⟨q, 1, (fun i => if i.val = 0 then u else if i.val = L then v else fun _ => none),
    (fun i => if i.val = 0 ∨ i.val = L then h else 0), []⟩

/-- The two-ended administrative action changes exactly those tape cells and
their common head, preserving native input and physical silence. -/
private lemma enumCont_ends_apply {L : ℕ} {S : Type} {x : List Bool} (_hL : 0 < L)
    (q q' : Option S) (u v : ℤ → Option Bool) (h : ℤ)
    (a b : Option (Option Bool)) (d : SignType) :
    (enumCont_endsAction (L := L) a b d q').apply (enumCont_pairCfg (x := x) q u v h) =
      enumCont_pairCfg q' (Function.update u h (a.getD (u h)))
        (Function.update v h (b.getD (v h))) (h + (d : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      cases a <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply,
        Function.update_eq_self]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L
      · cases b <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl,
          Function.update_eq_self]
      · simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_endsAction, enumCont_pairCfg, Action.apply]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L <;>
        simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]

/-- A sparse list of blank entries is an everywhere blank tape. -/
private lemma enumCont_sparse_blanks (n : ℕ) :
    enumCont_sparse (List.replicate n none) = fun _ => none := by
  funext z
  by_cases hz : 0 ≤ z <;> by_cases hn : z.toNat < n <;>
    simp [enumCont_sparse, hz, hn]

/-- Lifting every word symbol into the sparse representation gives the usual
buffer tape. -/
private lemma enumCont_sparse_some (w : List Bool) :
    enumCont_sparse (w.map some) = bufferTape w := by
  funext z
  by_cases hz : 0 ≤ z
  · simp only [enumCont_sparse, bufferTape, if_pos hz, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · simp [enumCont_sparse, bufferTape, hz]

/-- The copy scan overwrites the candidate from left to right and erases each
captured symbol. The old suffix is explicit, so initialization from an empty
candidate and replacement of an equal-width candidate share this proof.
**Proof sketch.** One step uses the overwrite and sparse-clear identities;
induct on the remaining captured suffix. Its right blank starts rewind. -/
private lemma enumCont_copy_scan {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr : S) (f : Bool → Bool)
    (htr : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (pre old rest : List Bool) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ rest.map some)) pre.length)
      (rest.length + 1) =
      enumCont_pairCfg (some qr) (bufferTape (pre ++ rest.map f ++ old.drop rest.length))
        (fun _ => none) ((pre.length : ℤ) + rest.length - 1) := by
  induction rest generalizing pre old with
  | nil =>
    have hv : enumCont_sparse (List.replicate pre.length none ++ ([] : List Bool).map some) =
        (fun _ => none) := by simpa using enumCont_sparse_blanks pre.length
    rw [hv]
    simp only [List.length_nil, Nat.zero_add, List.map_nil, List.drop_zero, List.append_nil,
      Int.natCast_zero, add_zero]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qc _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
        (fun _ => none) pre.length).workTapeSymbols (Fin.last L) = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp [sub_eq_add_neg]
  | cons b rest ih =>
    let c := enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ (b :: rest).map some)) pre.length
    have hr : c.workTapeSymbols (Fin.last L) = some b := by
      simp [c, enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL, enumCont_sparse]
    have he : tm.step c = enumCont_pairCfg (some qc)
        (bufferTape ((pre ++ [f b]) ++ old.drop 1))
        (enumCont_sparse (List.replicate (pre ++ [f b]).length none ++ rest.map some))
        (pre ++ [f b]).length := by
      change (tm.tr qc _ _).apply c = _
      rw [htr, hr]
      dsimp only [c]
      rw [enumCont_ends_apply hL]
      simp only [Option.getD_some, enumCont_overwrite, enumCont_sparse_clear,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      simp [List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, he, ih]
    simp [List.map_cons, List.append_assoc, add_comm, add_left_comm]

/-- Rewind the two endpoint heads together across the completed candidate.
The left blank takes one positive move, restoring both heads to cell zero. -/
private lemma enumCont_pair_rewind {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qr qa : S)
    (htr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qr) (bufferTape w) (fun _ => none) (j - 1))
      (j + 1) = enumCont_pairCfg (some qa) (bufferTape w) (fun _ => none) 0 := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qr _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) (0 - 1)).workTapeSymbols 0 = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols]
    simp only [Nat.cast_zero]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp
  | succ j ih =>
    have hj' : j < w.length := by omega
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)).workTapeSymbols 0 = some w[j] := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj']
    have he : tm.step (enumCont_pairCfg (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)) =
        enumCont_pairCfg (some qr) (bufferTape w) (fun _ => none) (j - 1) := by
      change (tm.tr qr _ _).apply _ = _
      rw [htr, hr, enumCont_ends_apply hL]
      simp only [Option.getD_none, Function.update_eq_self]
      simp [sub_eq_add_neg, add_assoc]
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    exact ih (by omega)

/-- Copying a captured word at least as long as the old candidate completely
replaces it, erases capture, and restores the canonical seam in linear time. -/
private lemma enumCont_copy_complete {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr qa : S) (f : Bool → Bool)
    (hc : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (hr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (old v : List Bool) (hv : old.length ≤ v.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape old) (bufferTape v) 0)
      (2 * v.length + 2) =
      enumCont_pairCfg (some qa) (bufferTape (v.map f)) (fun _ => none) 0 := by
  have hc' := enumCont_copy_scan (x := x) hL tm qc qr f hc [] old v
  simp only [List.length_nil, List.replicate_zero, List.nil_append, Nat.cast_zero,
    zero_add, enumCont_sparse_some, List.drop_eq_nil_iff.mpr hv, List.append_nil] at hc'
  rw [show 2 * v.length + 2 = (v.length + 1) + (v.length + 1) by omega,
    MultiTapeTM.runFrom_add, hc']
  exact enumCont_pair_rewind hL tm qr qa hr (v.map f) v.length (by simp)

/-- Empty history adds only blank stationary tapes to a candidate seam. -/
private lemma enumCont_log_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) [] =
      Cfg.ofWords q (stateWord (enumCont_logTM B).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · have hn : B.k + j.val ≠ 0 := by omega
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks, Nat.ne_of_gt hB]
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
          simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks,
            Fin.addCases, Nat.ne_of_gt hB] <;> exact enumCont_sparse_blanks 0
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]

/-- Appending one output tape to a candidate seam has the two-endpoint tape
layout used by the administrative controller. -/
private lemma enumCont_extend_words {L : ℕ} (hL : 0 < L) (s y : List Bool) :
    (fun i : Fin (L + 1) => if hi : i.val < L then
      bufferTape (stateWord L s ⟨i, hi⟩) else bufferTape y) =
      (fun i => if i.val = 0 then bufferTape s else if i.val = L then bufferTape y
        else fun _ => none) := by
  funext i
  by_cases hz : i.val = 0
  · have he : i = 0 := Fin.ext hz
    subst i
    simp [stateWord, hL]
  · have he : i ≠ 0 := by intro he; apply hz; simp [he]
    by_cases hi : i.val < L
    · have hn : i.val ≠ L := by omega
      simp [stateWord, hi, hz, hn]
    · have hl : i.val = L := by have := i.isLt; omega
      simp [hl, Nat.ne_of_gt hL]

/-- The clean wrapper's entry configuration at a prepared source seam. -/
private lemma enumCont_clean_entry_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM B).State)) (.inr (.inl 0)) [] []
      (enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) []) =
      enumCont_pairCfg (some (.inl q)) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa only [captureCfg, Cfg.ofWords, List.append_nil, bufferTape_nil] using
      enumCont_extend_words (by omega) s []
  · funext i
    simp [captureCfg, Cfg.ofWords, enumCont_pairCfg]

/-- The completed clean call has restored the candidate seam and retained
only its captured output on the last tape. -/
private lemma enumCont_clean_exit_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s y : List Bool) (q : B.State) (q' : Option (enumCont_cleanTM B).State) :
    enumCont_cleanCfg B (Cfg.ofWords (input := x) q (stateWord B.k s)) y q' 1 0 =
      enumCont_pairCfg q' (bufferTape s) (bufferTape y) 0 := by
  unfold enumCont_cleanCfg
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact enumCont_extend_words (by dsimp [enumCont_logTM]; omega) s y
  · funext i
    simp [Cfg.ofWords, enumCont_pairCfg]

/-- A clean call inside the body redirects the clean wrapper's first halt to
the appropriate live administrative state. This is a complete configuration
equation: all scratch is blank, both endpoint heads are zero, and output is
physically empty. -/
private lemma enumCont_body_call (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi q : B.State) (stop : Bool) (mode : Fin 3) (x s y : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).output = y) :
    ∃ t ≤ 3 * T + x.length + y.length + 8,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl q, mode)))
          (bufferTape s) (fun _ => none) 0) t =
        enumCont_pairCfg (some (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4)))
          (bufferTape s) (bufferTape y) 0 := by
  obtain ⟨r, hr, he⟩ := enumCont_clean_complete B
    (Cfg.ofWords (input := x) q (stateWord B.k s)) y T hh ho
  rw [enumCont_clean_entry_words B hB, enumCont_clean_exit_words B hB] at he
  obtain ⟨t, ht, hlive, hend⟩ := enumCont_first_halt (enumCont_cleanTM B).tm _ r
    (by rw [he]; rfl)
  have hrun := enumCont_return_run (enumCont_cleanTM B).tm (enumCont_bodyTM B qv qi stop).tm
    (fun q => .inl (q, mode))
    (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
    (fun _ _ _ => rfl) (enumCont_pairCfg (x := x) (some (.inl q))
      (bufferTape s) (fun _ => none) 0) t hlive
  rw [hend, he] at hrun
  exact ⟨t, ht.trans hr, hrun⟩

/-- With empty capture and zero endpoint heads, the administrative tape
layout is exactly the public canonical candidate seam. -/
private lemma enumCont_pair_words {L : ℕ} {S : Type} {x : List Bool}
    (q : S) (s : List Bool) :
    enumCont_pairCfg (L := L) (x := x) (some q) (bufferTape s) (fun _ => none) 0 =
      Cfg.ofWords q (stateWord (L + 1) s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
  · funext i; simp [enumCont_pairCfg, Cfg.ofWords]

/-- Initialization runs the clean unary generator, copies its marks as false
candidate bits, erases the marks, and rewinds to the canonical anchor. -/
private lemma enumCont_body_start (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (enumCont_bodyTM B qv qi stop).tm.runFrom ((enumCont_bodyTM B qv qi stop).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k (List.replicate w false)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi B.tm.q₀ stop 0 x []
    (List.replicate w true) T hh ho
  have hi : enumCont_pairCfg (x := x) (some (.inl (.inl B.tm.q₀, (0 : Fin 3))))
      (bufferTape []) (fun _ => none) 0 = (enumCont_bodyTM B qv qi stop).tm.initCfg x := by
    rw [enumCont_pair_words]
    simp [enumCont_bodyTM, enumCont_cleanTM, enumCont_logTM,
      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord]
  rw [hi] at he
  have hc := enumCont_copy_complete (x := x)
    (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
    (enumCont_bodyTM B qv qi stop).tm (.inr 1) (.inr 6) (.inr 0) (fun _ => false)
    (by intro inp work; rfl) (by intro inp work; rfl) [] (List.replicate w true) (by simp)
  simp only [List.length_replicate, List.map_replicate, enumCont_pair_words] at hc
  refine ⟨t + (2 * w + 2), ?_, ?_⟩
  · simp only [List.length_replicate] at ht; omega
  · rw [MultiTapeTM.runFrom_add, he]
    exact hc

/-- A genuine round leaves the anchor in one silent stationary transition. -/
private lemma enumCont_body_depart (B : FinTM Bool) (qv qi : B.State) (x s : List Bool) :
    (enumCont_bodyTM B qv qi false).tm.step
      (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) =
      enumCont_pairCfg (some (.inl (.inl qv, 1))) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_pair_words]
  change (controlAction 0 (some (.inl (.inl qv, (1 : Fin 3)) :
    (enumCont_bodyTM B qv qi false).State))).apply _ = _
  rw [controlAction_apply]
  simp [moveInputPos_zero, Cfg.ofWords]
  exact ⟨rfl, rfl⟩

/-- A captured true verdict emits the sole physical accepting bit and halts. -/
private lemma enumCont_body_accept (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    let c := enumCont_pairCfg (x := x) (some (.inr (3 : Fin 7))) (bufferTape s)
      (bufferTape [true]) 0
    ((enumCont_bodyTM B qv qi stop).tm.step c).state = none ∧
      ((enumCont_bodyTM B qv qi stop).tm.step c).output = [true] := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  simp [MultiTapeTM.step, enumCont_bodyTM, enumCont_pairCfg, Cfg.workTapeSymbols,
    hL, Action.apply, bufferTape]

/-- A false verdict is erased before entering the clean increment call. -/
private lemma enumCont_body_reject (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 3)) (bufferTape s) (bufferTape [false]) 0) =
      enumCont_pairCfg (some (.inl (.inl qi, 2))) (bufferTape s) (fun _ => none) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : Function.update (bufferTape [false]) (0 : ℤ) none = fun _ => none := by
    rw [show [false] = [] ++ [false] by rfl, bufferTape_append]
    simp only [List.length_nil, Nat.cast_zero, Function.update_idem]
    simp [Function.update_eq_self]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (3 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape [false]) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      some false := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL, bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 3) _ _).apply _ = _
  simp only [enumCont_bodyTM, hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_pairCfg, Action.apply, Ne.symm hL]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = (enumCont_logTM B).k <;>
        simp [enumCont_pairCfg, Action.apply, he, hl, hv]
  · funext i
    simp [enumCont_pairCfg, Action.apply]

/-- The catalog's empty overflow output preserves the old candidate. Every
nonempty increment result has the exact old width and is the stalled step. -/
private lemma enumCont_increment_cases (s : List Bool) :
    let v := (incFixed s).getD []
    (v = [] ∧ (incFixed s).getD s = s) ∨
      (v ≠ [] ∧ v.length = s.length ∧ (incFixed s).getD s = v) := by
  have hlen := enumCont_step_length s
  cases hi : incFixed s with
  | none => simp
  | some v =>
    rw [hi] at hlen
    simp only [Option.getD_some] at hlen ⊢
    by_cases hv : v = []
    · subst v
      have hs : s = [] := List.length_eq_zero_iff.mp hlen.symm
      simp [hs]
    · exact Or.inr ⟨hv, hlen, trivial⟩

/-- The increment-result check preserves all fields and chooses the anchor
on overflow or the copy phase on a nonempty result. -/
private lemma enumCont_body_check (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s v : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 4)) (bufferTape s) (bufferTape v) 0) =
      enumCont_pairCfg (some (.inr (if v = [] then 0 else 5)))
        (bufferTape s) (bufferTape v) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : bufferTape v 0 = none ↔ v = [] := by cases v <;> simp [bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 4) _ _).apply _ = _
  simp only [enumCont_bodyTM]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (4 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape v) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      bufferTape v 0 := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL]
  rw [hr]
  simp only [hv]
  by_cases he : v = [] <;> simp only [he, ↓reduceIte, controlAction_apply]
  all_goals
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [enumCont_pairCfg]

/-- A clean increment call followed by copy and rewind implements the exact
stalled fixed-width step. Empty overflow results preserve the candidate;
successful results replace every candidate cell in place. -/
private lemma enumCont_body_increment (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).output =
      (incFixed s).getD []) :
    ∃ t ≤ 3 * T + x.length + 3 * s.length + 11,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl qi, 2)))
          (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qi stop 2 x s ((incFixed s).getD []) T hh ho
  simp only [show (2 : Fin 3).val = 2 by decide, show ¬(2 : ℕ) = 0 by decide,
    show ¬(2 : ℕ) = 1 by decide, ↓reduceIte] at he
  rcases enumCont_increment_cases s with ⟨hv, hs⟩ | ⟨hv, hl, hs⟩
  · refine ⟨t + 1, ?_, ?_⟩
    · rw [hv] at ht; simp only [List.length_nil] at ht; omega
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, enumCont_body_check, if_pos hv, hv,
        hs, bufferTape_nil, enumCont_pair_words]
      rfl
  · have hc := enumCont_copy_complete (x := x)
      (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
      (enumCont_bodyTM B qv qi stop).tm (.inr 5) (.inr 6) (.inr 0) id
      (by intro inp work; rfl) (by intro inp work; rfl) s ((incFixed s).getD []) (by omega)
    simp only [List.map_id, enumCont_pair_words] at hc
    refine ⟨(t + 1) + (2 * ((incFixed s).getD []).length + 2), ?_, ?_⟩
    · rw [hl] at ht ⊢; omega
    · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step' (t := t), he,
        enumCont_body_check, if_neg hv, hc, hs]
      rfl

/-- Starting just after departure, one verifier call either emits acceptance
or clears the verdict and completes one exact candidate update. This raw
segment is valid in both controller variants; first-return guards are added
separately using the stopped anchor. -/
private lemma enumCont_body_round_raw (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 21,
      if b then
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).state = none ∧
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).output = [true]
      else (enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qv stop 1 x s [b] Tv hv.1 hv.2
  simp only [show (1 : Fin 3).val = 1 by decide, show ¬(1 : ℕ) = 0 by decide,
    ↓reduceIte] at he
  simp only [List.length_singleton] at ht
  cases b with
  | false =>
    obtain ⟨r, hr, hrun⟩ := enumCont_body_increment B hB qv qi stop x s Ti hi.1 hi.2
    refine ⟨(t + 1) + r, by omega, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', he,
      enumCont_body_reject, hrun]
  | true =>
    refine ⟨t + 1, by omega, ?_⟩
    simp only [↓reduceIte, MultiTapeTM.runFrom_succ_eq_step', he]
    exact enumCont_body_accept B qv qi stop x s

/-- An anchor whose transition is a stationary self-loop preserves its
complete configuration for every subsequent step. -/
private lemma enumCont_absorb {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ inp work, tm.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (hc : c.state = some qa) (t : ℕ) : tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    simp only [MultiTapeTM.step, hc, ha, controlAction_apply]
    apply Cfg.ext
    · exact hc.symm
    · exact moveInputPos_zero _
    · rfl
    · rfl
    · rfl

/-- Two transition tables differing only at the anchor agree on every run
prefix that has not yet visited that anchor. -/
private lemma enumCont_agree_run {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (c : Cfg k Bool S x) (t : ℕ)
    (hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa) :
    tm.runFrom c t = stop.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hn j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (stop.runFrom c t).state with
    | none => simp only [MultiTapeTM.step, hs]
    | some q =>
      have hq : q ≠ qa := by intro he; subst q; exact hn t (by omega) hs
      simp only [MultiTapeTM.step, hs, ha q hq]

/-- The first visit to a stopped anchor transfers to the active machine with
the same full endpoint and no earlier anchor visit. Absorption identifies
the first endpoint with the supplied bounded endpoint. -/
private lemma enumCont_first_anchor {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = some qa) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some qa) ∧
      tm.runFrom c t = stop.runFrom c T := by
  classical
  have hex : ∃ t, (stop.runFrom c t).state = some qa := ⟨T, hT⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hT
  have hend : (stop.runFrom c t).state = some qa := Nat.find_spec hex
  have hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa := fun j hj => Nat.find_min hex hj
  have he : stop.runFrom c T = stop.runFrom c t := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
    rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hend]
  refine ⟨t, ht, ?_, ?_⟩
  · intro j hj
    rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
    exact hn j hj
  · rw [enumCont_agree_run tm stop qa ha c t hn, he]

/-- A halted stopped run never visited the live absorbing anchor. Its entire
bounded run therefore transfers unchanged to the active machine. -/
private lemma enumCont_halt_transfer {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = none) :
    tm.runFrom c T = stop.runFrom c T ∧
      ∀ j ≤ T, (tm.runFrom c j).state ≠ some qa := by
  have hn : ∀ j ≤ T, (stop.runFrom c j).state ≠ some qa := by
    intro j hj hjq
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
    have he : stop.runFrom c T = stop.runFrom c j := by
      rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hjq]
    have he' := congrArg Cfg.state he
    rw [hT, hjq] at he'
    contradiction
  refine ⟨enumCont_agree_run tm stop qa ha c T (fun j hj => hn j (by omega)), ?_⟩
  intro j hj
  rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
  exact hn j hj

/-- The active and stopped body have identical transitions away from the
anchor. Their tape counts and finite state types are definitionally equal. -/
private lemma enumCont_body_agree (B : FinTM Bool) (qv qi : B.State)
    (q : (enumCont_bodyTM B qv qi false).State) (hq : q ≠ .inr 0) (inp work) :
    (enumCont_bodyTM B qv qi false).tm.tr q inp work =
      (enumCont_bodyTM B qv qi true).tm.tr q inp work := by
  cases q with
  | inl q => rfl
  | inr q =>
    have hz : q.val ≠ 0 := by
      intro he
      apply hq
      congr 1
      exact Fin.ext he
    simp only [enumCont_bodyTM]
    split <;> first | contradiction | rfl

/-- Startup satisfies the loop export's first-anchor guard as well as its
full canonical configuration equality. -/
private lemma enumCont_body_start_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (∀ j < t, ((enumCont_bodyTM B qv qi false).tm.runFrom
        ((enumCont_bodyTM B qv qi false).tm.initCfg x) j).state ≠ some (.inr 0)) ∧
      (enumCont_bodyTM B qv qi false).tm.runFrom ((enumCont_bodyTM B qv qi false).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_start B hB qv qi true x w T hh ho
  change (enumCont_bodyTM B qv qi true).tm.runFrom
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r =
      Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) at he
  obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
    (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
    (enumCont_body_agree B qv qi) (by intro inp work; rfl)
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r (by rw [he]; rfl)
  rw [he] at hend
  exact ⟨t, ht.trans hr, hn, hend⟩

/-- The active round has positive duration and no strict interior visit to
the anchor. Rejection uses the first stopped-anchor visit; acceptance never
visits that live absorbing state. In either case departure adds one step. -/
private lemma enumCont_body_round_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t, 0 < t ∧ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 22 ∧
      (∀ j, 0 < j → j < t →
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) j).state
            ≠ some (.inr 0)) ∧
      if b then
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).state
            = none ∧
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).output
            = [true]
      else (enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k ((incFixed s).getD s)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_round_raw B hB qv qi true x s b Tv Ti hv hi
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r (by rw [he]; rfl)
    refine ⟨t + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjt
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend, he]
      rfl
  | true =>
    simp only [↓reduceIte] at he ⊢
    obtain ⟨hend, hn⟩ := enumCont_halt_transfer
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r he.1
    refine ⟨r + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjr
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend]
      exact he

/-- A prepared source call may use the initial tape block of the shared
source machine; padding preserves its halt and exact emitted word. -/
private lemma enumCont_lift_call (M B : FinTM Bool) (hM : 0 < M.k) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (q : M.State) (x s y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).state = none)
    (ho : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).output = y) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).output = y := by
  rw [← enumCont_pad_words hM hk emb q x s,
    enumCont_pad_run hk M.tm B.tm emb htr]
  exact ⟨by simp [enumCont_padCfg, hh], ho⟩

/-- Initial calls pad correctly even for a zero-work-tape source. -/
private lemma enumCont_lift_init (M B : FinTM Bool) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (x y : List Bool) (T : ℕ) (h : M.ComputesInTime x y T) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).output = y := by
  obtain ⟨hh, ho⟩ := (computesInTime_iff M x y T).mp h
  rw [← enumCont_pad_init (k := M.k) emb M.tm.q₀ x]
  change (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).state = none ∧
    (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).output = y
  rw [enumCont_pad_run hk M.tm B.tm emb htr]
  refine ⟨?_, ho⟩
  change ((M.tm.runFrom (M.tm.initCfg x) T).state.map emb) = none
  rw [hh]
  rfl

/-- One input-independent polynomial bounds both body phases. The degree
dominates the verifier degree, unary-generator degree, and linear scans;
the coefficient absorbs every fixed administrative transition. -/
private lemma enumCont_common_bound (a d f c j n w : ℕ) :
    let P := (n + w + 1) ^ (d + c + 2)
    let A := 3 * a + 3 * f + 3 * j + 60
    3 * (f * (n + 1) ^ (c + 1)) + n + 3 * w + 10 ≤ A * P ∧
      3 * (a * (n + w + 1) ^ d + 2 * (n + w) + 4) +
        3 * ((j + 3) * (w + 1)) + 2 * n + 3 * w + 22 ≤ A * P := by
  dsimp only
  let P := (n + w + 1) ^ (d + c + 2)
  have hn : n + w + 1 ≤ P := by
    calc n + w + 1 = (n + w + 1) ^ 1 := by simp
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (n + w + 1) ^ d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hf : (n + 1) ^ (c + 1) ≤ P :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have ha' := Nat.mul_le_mul_left a hd
  have hf' := Nat.mul_le_mul_left f hf
  have hj' := Nat.mul_le_mul_left (j + 3) (show w + 1 ≤ P by omega)
  change _ ≤ (3 * a + 3 * f + 3 * j + 60) * P ∧
    _ ≤ (3 * a + 3 * f + 3 * j + 60) * P
  simp only [Nat.add_mul, Nat.mul_assoc] at hj' ⊢
  omega

/-- A concrete body with polynomial startup and exact seam restoration gives
the frozen enumerator configuration contract by the audited loop export.
This lemma is conditional only on the two explicit body obligations below.
**Proof sketch.** Use the catalog unary generator for the fuel bits, enlarging
the common coefficient and degree to cover both fuel and body. Instantiate
`exists_loopCfgTM` with the exact-width invariant and stalled increment.
The terminal is `(2^w-1)+1=2^w`; on candidate indices use `enumCont_orbit`.
Finally absorb the export's additive one using `1 ≤ (n+w+1)^D`, exactly as
in infrastructure round 3, item 5. All constants are fixed before the input. -/
private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
    (body : FinTM Bool) (anchor : body.State)
    (hstart : ∀ x : List Bool,
      ∃ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D,
        (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
        body.tm.runFrom (body.tm.initCfg x) t =
          Cfg.ofWords anchor (stateWord body.k (List.replicate (C * (x.length + 1) ^ c) false)))
    (hround : ∀ (x s : List Bool), s.length = C * (x.length + 1) ^ c →
      ∃ t, 0 < t ∧ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if MultiTapeTM.indicator V (x ++ s) then
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = [true]
        else
          body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k ((incFixed s).getD s))) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨F, f, hF⟩ := computesFunInTime_polyUnary C c
  let T := fun n => (A + f) * (n + C * (n + 1) ^ c + 1) ^ (D + c + 1)
  have hbody (n : ℕ) : A * (n + C * (n + 1) ^ c + 1) ^ D ≤ T n := by
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hfuel : F.ComputesFunInTime
      (fun x => Nat.bits (2 ^ (C * (x.length + 1) ^ c) - 1)) T := by
    intro x
    dsimp only
    rw [enumCont_fuel_bits]
    apply (hF x).mono
    exact Nat.mul_le_mul (by omega)
      ((Nat.pow_le_pow_left (by omega : x.length + 1 ≤
        x.length + C * (x.length + 1) ^ c + 1) (c + 1)).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
  obtain ⟨E, K, hE⟩ := exists_loopCfgTM body F anchor
    (fun x s => s.length = C * (x.length + 1) ^ c)
    (fun _ s => (incFixed s).getD s)
    (fun x s => MultiTapeTM.indicator V (x ++ s))
    (fun x => List.replicate (C * (x.length + 1) ^ c) false)
    (fun n => 2 ^ (C * (n + 1) ^ c) - 1) T hfuel
    (by intro x; exact List.length_replicate)
    (by intro x s hs; exact (enumCont_step_length s).trans hs)
    (by
      intro x
      obtain ⟨t, ht, hi, hh⟩ := hstart x
      exact ⟨t, ht.trans (hbody x.length), hi, hh⟩)
    (by
      intro x s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround x s hs
      exact ⟨t, htpos, ht.trans (hbody x.length), hi, hh⟩)
  refine ⟨K * (A + f + 1), D + c + 1, E, fun x => ?_⟩
  obtain ⟨cfg, startup, ht, hi, _, hend, hout, hr⟩ := hE x
  have hone : 1 ≤ 2 ^ (C * (x.length + 1) ^ c) := Nat.one_le_two_pow
  have hterminal : 2 ^ (C * (x.length + 1) ^ c) - 1 + 1 =
      2 ^ (C * (x.length + 1) ^ c) := Nat.sub_add_cancel hone
  rw [hterminal] at hend hout
  have hbudget : K * (T x.length + 1) ≤ K * (A + f + 1) *
      (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) := by
    have hp : 1 ≤ (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) :=
      Nat.one_le_pow _ _ (by omega)
    calc K * (T x.length + 1) ≤ K * (T x.length +
        (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1)) :=
          Nat.mul_le_mul_left K (Nat.add_le_add_left hp _)
      _ = _ := by dsimp [T]; ring
  refine ⟨cfg, startup, ht.trans hbudget, hi, hend, hout, ?_⟩
  intro i hi
  obtain ⟨t, ht, hh⟩ := hr i (by omega)
  rw [enumCont_orbit _ i hi] at hh
  exact ⟨t, ht.trans hbudget, hh⟩

/-- **Continuation frontier; admitted in this partial delivery.** There is one
uniform finite machine with a polynomial startup and a polynomially bounded
accept-or-advance segment for each exact-width candidate. The configuration
after the last rejected candidate is a halted singleton rejection.

**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
the all-false candidate while retaining the instance; assemble `x ++ u` on
the virtual input buffer. Use `enumCapture_returns` for the captured call.
On rejection, clear the bounded visited work region, reset all source and
buffer heads and the captured bit, and use `enumCarry_correct` to increment.
Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
overflow signal. Emit the single final answer only on acceptance or overflow.
Prove the startup and per-round configuration equalities below with a uniform
polynomial budget. These machine assembly and reset obligations are NOT
discharged by the counter, capture, and abstract loop lemmas alone. -/
private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨U, f, hU⟩ := computesFunInTime_polyUnary C c
  obtain ⟨I, j, hI⟩ := computesFunInTime_incFixed
  let Q := bufferedCompTM enumCont_concatTM MV
  let R := bufferedCompTM enumCont_concatTM I
  let B := enumCont_sources Q R U
  let qv : B.State := .inl Q.tm.q₀
  let qi : B.State := .inr (.inl (.inl (some true)))
  have hQ : 0 < Q.k := by dsimp [Q, bufferedCompTM, enumCont_concatTM]; omega
  have hR : 0 < R.k := by dsimp [R, bufferedCompTM, enumCont_concatTM]; omega
  have hQB : Q.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hRB : R.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hUB : U.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hB : 0 < B.k := lt_of_lt_of_le hQ hQB
  apply enumCont_from_body C c (3 * a + 3 * f + 3 * j + 60) (d + c + 2) V
    (enumCont_bodyTM B qv qi false) (.inr 0)
  · intro x
    have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
      (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
      (f * (x.length + 1) ^ (c + 1)) (hU x)
    obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
      (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
    exact ⟨t, ht.trans (enumCont_common_bound a d f c j x.length
      (C * (x.length + 1) ^ c)).1, hn, he⟩
  · intro x s hs
    obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V a d hV x s
    obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
    have hv := enumCont_lift_call Q B hQ hQB Sum.inl
      (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
    have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
      (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
    obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
      (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
    refine ⟨t, htpos, ?_, hn, he⟩
    have hb := (enumCont_common_bound a d f c j x.length s.length).2
    rw [hs] at hb
    apply le_trans (show t ≤ 3 * (a * (x.length + s.length + 1) ^ d +
      2 * (x.length + s.length) + 4) + 3 * ((j + 3) * (s.length + 1)) +
      2 * x.length + 3 * s.length + 22 by omega)
    simpa only [hs] using hb

/-! **Continuation completion note (batch E2-cont A).** The historical
partial-fill descriptions above and below are retained under the statement
freeze. The former `enumMachine_contracts` admission is now discharged.
The new private body has proved initialization, exact buffered verifier
input, captured silent output, complete reversible scratch restoration,
in-place candidate replacement, and positive first-return round contracts.
`enumCont_from_body` supplies the audited exact-width loop instantiation,
catalog-generated `2^w-1` fuel, bounded rank orbit, terminal `2^w`, and
uniform startup/round budgets. -/

/-- Assuming the single machine-construction frontier, the proved loop
invariant gives a decider with the audited exponential-times-polynomial
budget. This lemma inherits exactly that pending admission.
**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
for all `2^width` candidates, and identify its Boolean answer using exact
candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
coefficient. The final computation has exactly one output bit. -/
private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool),
      E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
  classical
  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
  refine ⟨2 * b, e, E, fun x => ?_⟩
  obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
  let w := C * (x.length + 1) ^ c
  let B := b * (x.length + w + 1) ^ e
  let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
  obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
    (by simpa only [Nat.zero_add] using And.intro hend hout)
    (fun j _ hj => hround j (by simpa only [Nat.zero_add] using hj))
  have hb : enumAny accept 0 (2 ^ w) =
      MultiTapeTM.indicator
        {z | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x := by
    have ha := enumAny_certificates x w V
    change enumAny accept 0 (2 ^ w) = true ↔ _ at ha
    cases he : enumAny accept 0 (2 ^ w) with
    | false =>
      have hx : ¬∃ u, u.length = w ∧ x ++ u ∈ V := by
        intro hx
        have := ha.mpr hx
        rw [he] at this
        contradiction
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
    | true =>
      have hx := ha.mp he
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
  have hcomp : E.ComputesInTime x [enumAny accept 0 (2 ^ w)] (startup + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hinit]
    exact ⟨hh, ho⟩
  rw [hb] at hcomp
  apply hcomp.mono
  have hB : B ≤ 2 ^ w * B := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
       _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
       _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
machine — a **new obligation**; the explicit formula is what makes the width
computable at all, phase-1 audit finding 1 and question 4) and lay out a
width-`Q n` all-`false` candidate certificate; in each round, assemble
`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
candidate as a **fixed-width** counter and repeat, rejecting on width overflow
after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
definition's length — no majorant mismatch (audit question 4). The remaining
machine obligations, named for the fill per phase-1 finding 5 and round-2
finding 2: fixed-width increment with overflow detection (the private
`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
is a template, not a citable API — promotion or private re-derivation is a
fill-time decision); retention of `x` and the candidate across rounds;
**a verifier-call simulation that captures `MV`'s decision bit in finite
control, suppresses its physical emissions, and redirects its halt to the
loop controller** — the output tape is append-only, so forwarding per-round
emissions would accumulate (`[false, true]` across two rounds) and violate
`DecidesInTime`'s singleton contract; the real output stays empty until the
final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
and the captured bit between rounds (a bounded region — each head moves at
most one cell per step); and a timed loop invariant covering all of the above
(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
`L ∈ EXP`.
+
+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
+simulation, abstract timed-loop invariant, and final budget normalization
+are proved below the class definitions. The machine's initialization,
+reset, and controller assembly remain the single private admission
+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
  have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
    Set.ext (fun x => (hL x).symm)
  rw [heq] at hE
  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity

## ===== TCSlib/Complexity/ClassNP/Nondeterminism.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Primitives
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic characterizations: Theorem 2.6, NEXP, and padding

[AB09, Theorem 2.6]: `NP = ⋃ c, NTIME (n^c)` — the certificate view and the
nondeterministic-machine view of `NP` coincide, with the accepting choice word as the
certificate and vice versa. This module states both directions as machine
compilations, the analogous `NTIME` characterization of the certificate-form
`Complexity.NEXP` ([AB09, §2.6.2] *defines* `NEXP` as `⋃ c, NTIME (2^(n^c))`; our
definition is [AB09, Exercise 2.27]'s verifier form, so the equality here is the
reconciliation of the two), and Theorem 2.22 (`EXP ≠ NEXP → P ≠ NP`, by padding).

## Design and deviations from [AB09]

* **The `NTIME` unions carry the same `+ 1` padding as `P`**: we write
  `⋃ c, NTIME (n^c + 1)` where [AB09] writes `⋃_{c ≥ 1} NTIME(n^c)`, for the reason
  recorded at `Complexity.P` — `n^c` vanishes at `n = 0` for `c ≥ 1` and no machine
  halts in zero steps, so the literal union is degenerate on the empty input; for
  `n ≥ 1` the two readings sandwich each other inside the constant slack. The
  exponential union `⋃ c, NTIME (2^(n^c))` needs no padding (`2^(n^c) ≥ 1`) and is
  [AB09]'s expression verbatim, matching `Complexity.EXP`.
* **Theorem 2.22 is proved through the certificate form** of `Complexity.NEXP` — the
  route of [AB09, Exercise 2.27], which needs no nondeterministic machines — rather
  than by padding an `NTIME` machine as in [AB09]'s proof of the theorem. With
  `Complexity.NEXP_eq_iUnion_NTIME` on the books the two renderings of the statement
  agree; the certificate route reuses the audited Exercise-2.1 interface instead of
  re-deriving NDTM compilations inside the padding argument.
* The choice-word/certificate correspondence is stated over the repaired explicit
  length formulas of `Complexity.NP`/`Complexity.NEXP` (phase-1 audit): each direction
  must land certificates of length **exactly** `C·(n+1)^c` (resp. `C·2^((n+1)^c)`),
  which the sketches arrange by padding choice words — harmless because halting is
  absorbing under every choice (`Turing.NDTM.runWith_of_halt`).

## Main results

* `Complexity.ntime_poly_subset_NP`, `Complexity.NP_subset_iUnion_NTIME`,
  `Complexity.NP_eq_iUnion_NTIME` — [AB09, Theorem 2.6], both directions and the
  equality.
* `Complexity.ntime_expPow_subset_NEXP`, `Complexity.NEXP_subset_iUnion_NTIME`,
  `Complexity.NEXP_eq_iUnion_NTIME` — the `NTIME` form of `NEXP` [AB09, §2.6.2,
  reconciled with Exercise 2.27].
* `Complexity.EXP_eq_NEXP_of_P_eq_NP`, `Complexity.P_ne_NP_of_EXP_ne_NEXP` —
  [AB09, Theorem 2.22], padding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.6, pp. 41-42; §2.6.2, pp. 56-57;
  Theorem 2.22, p. 57; Exercises 2.1, 2.27.)
-/

namespace Complexity

open Turing
open Turing.FinTM

/-- The total length of an input and its prescribed certificate strictly increases
with the input length, including zero coefficient and degree. -/
private lemma certificate_split_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + C * (n + 1) ^ c) := by
  intro n m hnm
  exact Nat.add_lt_add_of_lt_of_le hnm
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) c))

/-- Two concatenations satisfying the same exact certificate-length formula have
the same input and certificate whenever their concatenated words agree. -/
private lemma certificate_split_unique (C c : ℕ) {x u y v : List Bool}
    (hu : u.length = C * (x.length + 1) ^ c)
    (hv : v.length = C * (y.length + 1) ^ c) (h : x ++ u = y ++ v) :
    x = y ∧ u = v := by
  have hlen := congrArg List.length h
  simp only [List.length_append, hu, hv] at hlen
  have hx := (certificate_split_strictMono C c).injective hlen
  exact ⟨List.append_inj_left h hx, List.append_inj_right h hx⟩

/-- A finite, total specification of split recovery. Its implementation on native
tapes, including the time for polynomial evaluation, remains a startup obligation. -/
private def certificateSplit (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? (fun n => decide (n + C * (n + 1) ^ c = m))

/-- Every returned split is within the actual input and satisfies the exact
length formula. No validity assumption on the input is needed. -/
private lemma certificateSplit_spec (C c m n : ℕ)
    (h : certificateSplit C c m = some n) : n ≤ m ∧ n + C * (n + 1) ^ c = m := by
  have hn := List.mem_of_find?_eq_some h
  have he := List.find?_some h
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp hn), of_decide_eq_true he⟩

/-- Failed finite search means there is no solution at any natural split position,
so malformed lengths must be rejected rather than assigned a default split. -/
private lemma certificateSplit_none_iff (C c m : ℕ) :
    certificateSplit C c m = none ↔ ¬ ∃ n, n + C * (n + 1) ^ c = m := by
  rw [certificateSplit, List.find?_eq_none]
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    exact h n (List.mem_range.mpr (by omega)) (by simpa using hn)
  · intro h n _ hn
    exact h ⟨n, of_decide_eq_true hn⟩

/-- A valid split is returned by finite search; strict increase rules out a
different successful candidate before it. -/
private lemma certificateSplit_complete (C c m n : ℕ)
    (hn : n + C * (n + 1) ^ c = m) : certificateSplit C c m = some n := by
  cases hs : certificateSplit C c m with
  | none => exact False.elim ((certificateSplit_none_iff C c m).mp hs ⟨n, hn⟩)
  | some k =>
    have hk := (certificateSplit_spec C c m k hs).2
    have heq := (certificate_split_strictMono C c).injective (hk.trans hn.symm)
    exact congrArg some heq

/-- The verifier language described in the forward Theorem-2.6 sketch. This is a
language specification; polynomial-time decidability still requires a machine. -/
private def choiceVerifier (N : FinNDTM Bool) (C c : ℕ) : Language Bool :=
  {y | ∃ x u : List Bool, u.length = C * (x.length + 1) ^ c ∧ y = x ++ u ∧
    (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith u (N.tm.initCfg x)).output = [true]}

/-- On a correctly split word, verifier membership is exactly halted singleton-true
acceptance of the supplied choice word; a different split cannot create acceptance. -/
private lemma choiceVerifier_append (N : FinNDTM Bool) (C c : ℕ)
    (x u : List Bool) (hu : u.length = C * (x.length + 1) ^ c) :
    x ++ u ∈ choiceVerifier N C c ↔
      (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
      (N.tm.runWith u (N.tm.initCfg x)).output = [true] := by
  constructor
  · rintro ⟨y, v, hv, heq, hhalt, hout⟩
    obtain ⟨rfl, rfl⟩ := certificate_split_unique C c hu hv heq
    exact ⟨hhalt, hout⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨x, u, hu, rfl, hhalt, hout⟩

/-- A word whose length has no valid split is outside the specified verifier
language. This is the rejecting branch of the total parser specification. -/
private lemma choiceVerifier_no_split (N : FinNDTM Bool) (C c : ℕ) (y : List Bool)
    (h : certificateSplit C c y.length = none) : y ∉ choiceVerifier N C c := by
  rintro ⟨x, u, hu, hy, _, _⟩
  have hlen := congrArg List.length hy
  simp only [List.length_append, hu] at hlen
  exact (certificateSplit_none_iff C c y.length).mp h ⟨x.length, hlen.symm⟩

/-- Once every branch has halted at `t`, extending the common budget changes
neither existential acceptance nor the accepting output. The reverse implication
uses the length-`t` prefix and all-branch halting, not just one halted branch. -/
private lemma acceptsWithin_iff_of_halts {N : FinNDTM Bool} {x : List Bool}
    {t t' : ℕ} (hhalt : N.tm.HaltsWithin x t) (hle : t ≤ t') :
    N.AcceptsWithin x t' ↔ N.AcceptsWithin x t := by
  constructor
  · rintro ⟨w, hw, _, hout⟩
    have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
    have hp := hhalt (w.take t) hlen
    have hr := N.tm.runWith_append (w.take t) (w.drop t) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hp] at hr
    exact ⟨w.take t, hlen, hp, hr ▸ hout⟩
  · intro h
    exact h.mono hle

/-- The exact certificate length with coefficient `2*a` covers the nondeterministic
time bound, uniformly at length zero and degree zero. -/
private lemma choice_budget_le (a c n : ℕ) :
    a * (n ^ c + 1) ≤ (2 * a) * (n + 1) ^ c := by
  have hp := Nat.pow_le_pow_left (Nat.le_succ n) c
  have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c _ (Nat.succ_pos n)
  calc
    a * (n ^ c + 1) ≤ a * ((n + 1) ^ c + (n + 1) ^ c) :=
      Nat.mul_le_mul_left a (Nat.add_le_add hp h1)
    _ = (2 * a) * (n + 1) ^ c := by ring

/-- Padding and truncation identify language membership with certificates for the
specified verifier. This proves the logical correspondence separately from the
timed construction needed to put the verifier in `P`. -/
private lemma choice_certificate_iff (N : FinNDTM Bool) (L : Language Bool)
    (a c : ℕ) (hN : N.DecidesInTime L (fun n => a * (n ^ c + 1)))
    (x : List Bool) :
    x ∈ L ↔ ∃ u : List Bool, u.length = (2 * a) * (x.length + 1) ^ c ∧
      x ++ u ∈ choiceVerifier N (2 * a) c := by
  rw [(hN x).2, ← acceptsWithin_iff_of_halts (hN x).1 (choice_budget_le a c x.length)]
  constructor
  · rintro ⟨u, hu, hhalt, hout⟩
    exact ⟨u, hu, (choiceVerifier_append N (2 * a) c x u hu).mpr ⟨hhalt, hout⟩⟩
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, hu, (choiceVerifier_append N (2 * a) c x u hu).mp hv⟩

/-- A finite summary of captured output: empty, the singleton true, or a rejecting
nonempty word. The complete word is retained separately on the capture tape. -/
private def capturedSummary : List Bool → Option Bool
  | [] => none
  | [b] => some b
  | _ => some false

/-- Update the output summary with one optional emission. -/
private def captureEmission (s : Option Bool) (e : Option Bool) : Option Bool :=
  match e with
  | none => s
  | some b => match s with
    | none => some b
    | some _ => some false

/-- The finite summary processes every emission, including one on the source's
halting transition; two or more emitted bits always give a rejecting summary. -/
private lemma captureEmission_correct (w : List Bool) (e : Option Bool) :
    captureEmission (capturedSummary w) e = capturedSummary (w ++ e.toList) := by
  cases e with
  | none => simp [captureEmission]
  | some b =>
    cases w with
    | nil => rfl
    | cons a w =>
      cases w with
      | nil => rfl
      | cons a' w => rfl

/-- The accepting summary recognizes exactly the singleton true, rather than a
word that merely contains true or starts with true. -/
private lemma capturedSummary_true (w : List Bool) :
    capturedSummary w = some true ↔ w = [true] := by
  cases w with
  | nil => simp [capturedSummary]
  | cons b w =>
    cases w with
    | nil => simp [capturedSummary]
    | cons b' w => simp [capturedSummary]

/-- Partition the work tapes into the original source tapes and three private
tapes, in order: virtual input, choices, captured output. -/
private def choiceTapes {α : Type} {k : ℕ} (source : Fin k → α)
    (input choices output : α) : Fin (k + 3) → α :=
  Fin.addCases source (fun i => if i = 0 then input else if i = 1 then choices else output)

/-- The deterministic simulation phase for a fixed NDTM. It starts only after its
three private tapes have been prepared. Each copied choice causes one source
step; a blank choice ends the clock and emits one verdict. Source halts remain
live simulator states until that clock ends. The physical input is never read.

The source state and the boundary tag are finite control. Every emission is
written to the capture tape, with a finite summary used only for the final exact
singleton test; physical output stays empty until that test. -/
private def choiceCore (N : FinNDTM Bool) : FinTM Bool where
  k := N.k + 3
  State := Option N.State × Bool × Option Bool
  tm :=
    { q₀ := (some N.tm.q₀, true, none)
      tr := fun ⟨q, tag, summary⟩ _ work =>
        match work (Fin.natAdd N.k 1) with
        | none =>
          ⟨0, fun _ => (none, 0), some (decide (q = none ∧ summary = some true)), none⟩
        | some bit =>
          match q with
          | none =>
            ⟨0, choiceTapes (fun _ => (none, 0)) (none, 0) (none, 1) (none, 0),
              none, some (none, tag, summary)⟩
          | some q =>
            let inp := work (Fin.natAdd N.k 0)
            let a := N.tm.tr bit q inp (fun i => work (Fin.castAdd 3 i))
            let m := virtualMove tag inp a.inputTape
            ⟨0, choiceTapes a.workTapes (none, m) (none, 1)
                (a.output.map some, if a.output.isSome then 1 else 0),
              none, some (a.state, virtualNextTag tag m, captureEmission summary a.output)⟩ }

/-- Embed a source configuration in the prepared simulator, preserving each
source tape and storing input, choices and captured output in disjoint blocks.
The native physical input position is arbitrary and remains fixed. -/
private def choiceCoreCfg (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (u : List Bool) (j : ℕ)
    (p : Fin (y.length + 2)) : Cfg (choiceCore N).k Bool (choiceCore N).State y where
  state := some (cfg.state, tag, capturedSummary cfg.output)
  inputPos := p
  workTapes := choiceTapes cfg.workTapes (bufferTape x) (bufferTape u) (bufferTape cfg.output)
  workTapePos := choiceTapes cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1)
    (j : ℤ) (cfg.output.length : ℤ)
  output := []

/-- A prepared simulator consumes exactly the next copied choice in one physical
step. Its source tapes, virtual input and complete captured output agree with the
native source step. The physical output is still empty, even on a source halt.

**Proof sketch.** The copied-input read is the native guarded read. Apply the
existing virtual-movement invariant to preserve both clamping and the boundary
tag. Check the disjoint tape blocks separately; the output block uses the
append-at-the-right-blank identity. A halted source is absorbed while the choice
head still advances. -/
private lemma choiceCore_step (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (j : ℕ) (hj : j < u.length) (p : Fin (y.length + 2)) :
    ∃ tag', VirtualTag (N.tm.stepWith u[j] cfg).inputPos tag' ∧
      (choiceCore N).tm.step (choiceCoreCfg N cfg tag u j p) =
        choiceCoreCfg N (N.tm.stepWith u[j] cfg) tag' u (j + 1) p := by
  have hu : (choiceCoreCfg N cfg tag u j p).workTapeSymbols (Fin.natAdd N.k 1) =
      some u[j] := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj]
  have hi : (choiceCoreCfg N cfg tag u j p).workTapeSymbols (Fin.natAdd N.k 0) =
      cfg.inputSymbol := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols, bufferTape_inputSymbol]
  have hw : (fun i => (choiceCoreCfg N cfg tag u j p).workTapeSymbols
      (Fin.castAdd 3 i)) = cfg.workTapeSymbols := by
    funext i
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols]
  have hs : (choiceCoreCfg N cfg tag u j p).state =
      some (cfg.state, tag, capturedSummary cfg.output) := rfl
  cases hq : cfg.state with
  | none =>
    have hc := NDTM.stepWith_of_halt (tm := N.tm) (b := u[j]) hq
    refine ⟨tag, ?_, ?_⟩
    · simpa only [hc] using htag
    · rw [hc]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [choiceCore]
      rw [hu, hq]
      refine Cfg.ext (by simp [choiceCoreCfg, hq]) (moveInputPos_zero _) ?_ ?_
        (by simp [choiceCoreCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i; fin_cases i <;> simp [choiceCoreCfg, choiceTapes]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i; fin_cases i <;> simp [choiceCoreCfg, choiceTapes, Nat.cast_add]
  | some q =>
    let a := N.tm.tr u[j] q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : N.tm.stepWith u[j] cfg = a.apply cfg := by
      simp only [NDTM.stepWith, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · rw [hc]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [choiceCore]
      rw [hu, hq, hi, hw]
      change (Action.mk 0 (choiceTapes a.workTapes (none, m) (none, 1)
          (a.output.map some, if a.output.isSome then 1 else 0)) none
          (some (a.state, virtualNextTag tag m,
            captureEmission (capturedSummary cfg.output) a.output))).apply
          (choiceCoreCfg N cfg tag u j p) =
        choiceCoreCfg N (a.apply cfg) (virtualNextTag tag m) u (j + 1) p
      refine Cfg.ext (by simp [choiceCoreCfg, captureEmission_correct])
        (moveInputPos_zero _) ?_ ?_ (by simp [choiceCoreCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i
          fin_cases i <;> cases he : a.output <;>
            simp [choiceCoreCfg, choiceTapes, he, bufferTape_append]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i
          fin_cases i
          · simpa [choiceCoreCfg, choiceTapes, m] using hm.1
          · simp [choiceCoreCfg, choiceTapes, Nat.cast_add]
          · cases he : a.output <;> simp [choiceCoreCfg, choiceTapes, he]

/-- After `t` physical simulation steps the represented source has consumed
exactly the first `t` copied choices. Administrative work before this phase is
not counted as source choices. The full configuration equality includes the
unchanged physical input, all source tapes, captured output, and empty real output.

**Proof sketch.** Induct on the physical step count, applying the one-step
invariant to the next indexed choice. The next prefix is the old prefix followed
by that bit, so the append law identifies the corresponding source run. -/
private lemma choiceCore_run (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (t : ℕ) (ht : t ≤ u.length) (p : Fin (y.length + 2)) :
    ∃ tag', VirtualTag (N.tm.runWith (u.take t) cfg).inputPos tag' ∧
      (choiceCore N).tm.runFrom (choiceCoreCfg N cfg tag u 0 p) t =
        choiceCoreCfg N (N.tm.runWith (u.take t) cfg) tag' u t p := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', hr⟩ := ih (by omega)
    obtain ⟨tag'', htag'', hs⟩ :=
      choiceCore_step N (N.tm.runWith (u.take t) cfg) tag' htag' u t (by omega) p
    have hn : N.tm.runWith (u.take (t + 1)) cfg =
        N.tm.stepWith u[t] (N.tm.runWith (u.take t) cfg) := by
      rw [List.take_succ_eq_append_getElem (by omega), NDTM.runWith_append]
      rfl
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [hn] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', hr, hs, hn]

/-- At the blank after the copied choice word, one final transition halts and
emits exactly one decision bit. A live source with output `[true]` rejects, as
does every halted source whose complete output differs from `[true]`. -/
private lemma choiceCore_finish (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (u : List Bool)
    (p : Fin (y.length + 2)) :
    ((choiceCore N).tm.step (choiceCoreCfg N cfg tag u u.length p)).state = none ∧
      ((choiceCore N).tm.step (choiceCoreCfg N cfg tag u u.length p)).output =
        [decide (cfg.state = none ∧ cfg.output = [true])] := by
  have hu : (choiceCoreCfg N cfg tag u u.length p).workTapeSymbols
      (Fin.natAdd N.k 1) = none := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols]
  have hs : (choiceCoreCfg N cfg tag u u.length p).state =
      some (cfg.state, tag, capturedSummary cfg.output) := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only [choiceCore]
  rw [hu]
  simp [choiceCoreCfg, capturedSummary_true]

/-- From a prepared configuration, the deterministic core halts after exactly the
declared `|u|+1` budget and reports whether the native source run under `u` accepts.
This is a timed `runFrom` contract, not a claim about blank-tape initialization. -/
private lemma choiceCore_timed (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (p : Fin (y.length + 2)) :
    let result := (choiceCore N).tm.runFrom (choiceCoreCfg N cfg tag u 0 p) (u.length + 1)
    result.state = none ∧ result.output =
      [decide ((N.tm.runWith u cfg).state = none ∧
        (N.tm.runWith u cfg).output = [true])] := by
  obtain ⟨tag', _, hr⟩ := choiceCore_run N cfg tag htag u u.length (le_refl _) p
  simp only [List.take_length] at hr
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', hr]
  exact choiceCore_finish N (N.tm.runWith u cfg) tag' u p

/-- The native initial source configuration has the correct virtual boundary tag,
including the empty-input case, where position one is already the right blank. -/
private lemma choiceCore_initial_tag (N : FinNDTM Bool) (x : List Bool) :
    VirtualTag (N.tm.initCfg x).inputPos true := by
  simp [NDTM.initCfg, Cfg.init, VirtualTag]

/-- Three concrete tape slots for the standalone copying phase. -/
private def copyTapes {α : Type} (left right clock : α) (i : Fin 3) : α :=
  if i = 0 then left else if i = 1 then right else clock

/-- A fixed copying phase, supplied with a unary split countdown on its third
tape. It copies the prefix to tape zero and the suffix to tape one, in a single
left-to-right pass, and never emits physical output. Split recovery and production
of the countdown are separate startup obligations. -/
private def choiceCopy : FinTM Bool where
  k := 3
  State := Bool
  tm :=
    { q₀ := true
      tr := fun phase inp work => match inp with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some bit =>
          if phase = true ∧ (work 2).isSome then
            ⟨1, copyTapes (some (some bit), 1) (none, 0) (none, 1),
              none, some true⟩
          else
            ⟨1, copyTapes (none, 0) (some (some bit), 1) (none, 0),
              none, some false⟩ }

/-- Configuration of the copying phase: completed prefix and suffix buffers,
with the countdown head equal to the number of prefix bits already copied. -/
private def choiceCopyCfg {y : List Bool} (n : ℕ) (phase : Bool)
    (left right : List Bool) (p : Fin (y.length + 2)) :
    Cfg 3 Bool Bool y where
  state := some phase
  inputPos := p
  workTapes := copyTapes (bufferTape left) (bufferTape right)
    (bufferTape (List.replicate n true))
  workTapePos := copyTapes (left.length : ℤ) (right.length : ℤ)
    (left.length : ℤ)
  output := []

/-- While the unary countdown is nonempty, one native copying step appends the
current input bit only to the prefix buffer and advances the countdown once. -/
private lemma choiceCopy_prefix_step {y : List Bool} (n : ℕ)
    (left right : List Bool) (p : Fin (y.length + 2)) (bit : Bool)
    (hlen : left.length < n)
    (hin : (choiceCopyCfg n true left right p).inputSymbol = some bit) :
    choiceCopy.tm.step (choiceCopyCfg n true left right p) =
      choiceCopyCfg n true (left ++ [bit]) right (moveInputPos p 1) := by
  have hc : (choiceCopyCfg n true left right p).workTapeSymbols 2 = some true := by
    simp [choiceCopyCfg, copyTapes, Cfg.workTapeSymbols, hlen]
  unfold MultiTapeTM.step
  change (choiceCopy.tm.tr true _ _).apply _ = _
  rw [hin]
  dsimp only [choiceCopy]
  rw [hc]
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [choiceCopyCfg])
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes, bufferTape_append]
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes]

/-- Once the countdown is exhausted, one native copying step appends the current
input bit only to the choice buffer, leaving the source-input buffer unchanged. -/
private lemma choiceCopy_suffix_step {y : List Bool} (n : ℕ) (phase : Bool)
    (left right : List Bool) (p : Fin (y.length + 2)) (bit : Bool)
    (hlen : left.length = n)
    (hin : (choiceCopyCfg n phase left right p).inputSymbol = some bit) :
    choiceCopy.tm.step (choiceCopyCfg n phase left right p) =
      choiceCopyCfg n false left (right ++ [bit]) (moveInputPos p 1) := by
  have hc : (choiceCopyCfg n phase left right p).workTapeSymbols 2 = none := by
    simp [choiceCopyCfg, copyTapes, Cfg.workTapeSymbols, hlen]
  unfold MultiTapeTM.step
  change (choiceCopy.tm.tr phase _ _).apply _ = _
  rw [hin]
  dsimp only [choiceCopy]
  rw [hc]
  simp only [Option.isSome_none, Bool.false_eq_true, and_false, if_false]
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [choiceCopyCfg])
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes, bufferTape_append]
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes]

/-- Starting with the unary prefix length and blank data buffers, copying the
first `t ≤ |x|` input symbols takes exactly `t` native transitions.

**Proof sketch.** Induct on `t`. The native input head reads the next bit of
`x`, and the unary countdown still has a bit. Apply the prefix-copy step and
the list-prefix append identity; the native head advances without clamping
because the next position is still within the input window. -/
private lemma choiceCopy_prefix_run (x u : List Bool) (t : ℕ) (ht : t ≤ x.length) :
    choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) t =
        choiceCopyCfg x.length true (x.take t) []
          ⟨t + 1, by simp only [List.length_append]; omega⟩ := by
  induction t with
  | zero => simp [MultiTapeTM.runFrom_zero, List.take_zero]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hp : (x.take t).length = t := List.length_take_of_le (by omega)
    have hin : (choiceCopyCfg (y := x ++ u) x.length true (x.take t) []
        ⟨t + 1, by simp only [List.length_append]; omega⟩).inputSymbol = some x[t] := by
      rw [inputSymbolInner t (by simp only [choiceCopyCfg, Nat.add_comm])
        (by simp only [List.length_append]; omega)]
      rw [List.getElem_append_left (by omega)]
    rw [choiceCopy_prefix_step _ _ _ _ _ (by rw [hp]; omega) hin,
      ← List.take_succ_eq_append_getElem (by omega)]
    congr 1
    apply Fin.ext
    rw [show (1 : SignType) = .pos from rfl,
      moveInputPos_pos_of_ne_right _ (by simp only [List.length_append]; omega)]

/-- After copying all of `x`, each additional suffix bit costs one native
transition. The copied source input and its completed countdown remain unchanged.
In particular, empty prefixes and empty suffixes are included.

**Proof sketch.** The prefix-run lemma supplies the initial suffix configuration.
Induct on the number of suffix bits: the countdown stays at its right blank,
and the input read lies in the suffix of the concatenation. The suffix-copy
step appends precisely that next bit and advances the native input head. -/
private lemma choiceCopy_suffix_run (x u : List Bool) (t : ℕ) (ht : t ≤ u.length) :
    ∃ phase : Bool, choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) (x.length + t) =
        choiceCopyCfg x.length phase x (u.take t)
          ⟨x.length + t + 1, by simp only [List.length_append]; omega⟩ := by
  induction t with
  | zero =>
    refine ⟨true, ?_⟩
    simpa only [Nat.add_zero, List.take_zero, List.take_length] using
      choiceCopy_prefix_run x u x.length (le_refl _)
  | succ t ih =>
    obtain ⟨phase, hr⟩ := ih (by omega)
    refine ⟨false, ?_⟩
    conv_lhs => rw [Nat.add_succ x.length t, MultiTapeTM.runFrom_succ_eq_step', hr]
    have hin : (choiceCopyCfg (y := x ++ u) x.length phase x (u.take t)
        ⟨x.length + t + 1, by simp only [List.length_append]; omega⟩).inputSymbol =
        some u[t] := by
      rw [inputSymbolInner (x.length + t)
        (by simp only [choiceCopyCfg, Nat.add_comm])
        (by simp only [List.length_append]; omega)]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [choiceCopy_suffix_step _ _ _ _ _ _ rfl hin,
      ← List.take_succ_eq_append_getElem (by omega)]
    congr 1
    apply Fin.ext
    rw [show (1 : SignType) = .pos from rfl,
      moveInputPos_pos_of_ne_right _ (by simp only [List.length_append]; omega)]
    change x.length + t + 1 + 1 = x.length + (t + 1) + 1
    omega

/-- The entire copying pass takes `|x++u|+1` transitions, including its final
boundary check. Both data buffers are exact, their heads are at their right
blanks, the countdown is preserved, and physical output is empty. This contract
still requires the unary split length to be present initially.

**Proof sketch.** Instantiate the suffix-run lemma at the complete suffix length.
The physical input head then reads the right blank. The next transition halts
without writing, moving work heads, or emitting, preserving the two full buffers. -/
private lemma choiceCopy_timed (x u : List Bool) :
    let result := choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) ((x ++ u).length + 1)
    result.state = none ∧
      result.workTapes = copyTapes (bufferTape x) (bufferTape u)
        (bufferTape (List.replicate x.length true)) ∧
      result.workTapePos = copyTapes (x.length : ℤ) (u.length : ℤ) (x.length : ℤ) ∧
      result.output = [] := by
  obtain ⟨phase, hr⟩ := choiceCopy_suffix_run x u u.length (le_refl _)
  simp only [List.take_length] at hr
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step']
  have hr' : choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) (x ++ u).length =
        choiceCopyCfg x.length phase x u
          ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩ := by
    simpa only [List.length_append] using hr
  rw [hr']
  have hin : (choiceCopyCfg (y := x ++ u) x.length phase x u
      ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩).inputSymbol =
      none := by
    have h := inputSymbol_at (choiceCopyCfg (y := x ++ u) x.length phase x u
      ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩)
      (x ++ u).length (le_refl _) (by simp [choiceCopyCfg])
    simpa using h
  unfold MultiTapeTM.step
  change ((choiceCopy.tm.tr phase _ _).apply _).state = none ∧ _
  rw [hin]
  simp [choiceCopy, choiceCopyCfg]

/-- The library and this file solve the same length equation. The coefficient
is unchanged here: the `C+1` translation recorded for the marker-padding parser
in `NP.lean` does not apply to this file's choice-word parser. -/
private lemma cont_split_bridge (C c m : ℕ) :
    solveSplit C c m = certificateSplit C c m := by
  rfl

/-- Parse an aligned pair into the two buffers of the proved choice core.
States 0--2 parse doubled prefix bits, state 3 copies the suffix, and states
4--5 rewind the input and choice buffers. Both rewinds first move left from
the right blank, so empty words have the same startup contract. Every
administrative transition is physically silent except malformed rejection.
The core's transition table is embedded verbatim in the right summand. -/
private def contPairTM (N : FinNDTM Bool) : FinTM Bool where
  k := N.k + 3
  State := Fin 6 ⊕ (choiceCore N).State
  tm :=
    { q₀ := .inl 0
      tr := fun q inp work => match q with
        | .inr q => Action.mapState Sum.inr ((choiceCore N).tm.tr q inp work)
        | .inl 0 => match inp with
          | some b => ⟨1, fun _ => (none, 0), none, some (.inl (if b then 2 else 1))⟩
          | none => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 1 => match inp with
          | some false => ⟨1, choiceTapes (fun _ => (none, 0))
              (some (some false), 1) (none, 0) (none, 0), none, some (.inl 0)⟩
          | some true => ⟨1, fun _ => (none, 0), none, some (.inl 3)⟩
          | none => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 2 => match inp with
          | some true => ⟨1, choiceTapes (fun _ => (none, 0))
              (some (some true), 1) (none, 0) (none, 0), none, some (.inl 0)⟩
          | _ => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 3 => match inp with
          | some b => ⟨1, choiceTapes (fun _ => (none, 0))
              (none, 0) (some (some b), 1) (none, 0), none, some (.inl 3)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, -1) (none, 0) (none, 0), none, some (.inl 4)⟩
        | .inl 4 => match work (Fin.natAdd N.k 0) with
          | some _ => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, -1) (none, 0) (none, 0), none, some (.inl 4)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 1) (none, -1) (none, 0), none, some (.inl 5)⟩
        | .inl _ => match work (Fin.natAdd N.k 1) with
          | some _ => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 0) (none, -1) (none, 0), none, some (.inl 5)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 0) (none, 1) (none, 0), none,
                some (.inr (some N.tm.q₀, true, none))⟩ }

/-- A silent loader configuration; the source work tapes and capture tape are
blank, and the two word buffers and their heads are explicit. -/
private def contLoadCfg (N : FinNDTM Bool) {y : List Bool} (q : Fin 6)
    (x u : List Bool) (p : Fin (y.length + 2)) (a b : ℤ) :
    Cfg (contPairTM N).k Bool (contPairTM N).State y :=
  ⟨some (.inl q), p, choiceTapes (fun _ _ => none) (bufferTape x)
    (bufferTape u) (fun _ => none), choiceTapes (fun _ => 0) a b 0, []⟩

/-- Once the loader dispatches, the proved core runs in exact lockstep in
its renamed control states, including its final physical verdict. -/
private lemma cont_core_run (N : FinNDTM Bool) {y : List Bool}
    (c : Cfg (choiceCore N).k Bool (choiceCore N).State y) (t : ℕ) :
    (contPairTM N).tm.runFrom (Cfg.mapState Sum.inr c) t =
      Cfg.mapState Sum.inr ((choiceCore N).tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
  intro d
  cases hs : d.state with
  | none => simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_none]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    change (Action.mapState Sum.inr ((choiceCore N).tm.tr q _ _)).apply _ = _
    rfl

/-- Rewinding the choice buffer costs exactly one step per remaining symbol
and one final dispatch, preserving the source input and every blank source tape.
**Proof sketch.** Induct on the number of cells to the left of the head. At
zero the head is at the left blank; otherwise its read is the corresponding
buffer bit and one left move reduces the induction parameter. -/
private lemma cont_rewind_choices (N : FinNDTM Bool) {y : List Bool}
    (x u : List Bool) (p : Fin (y.length + 2)) (j : ℕ) (hj : j ≤ u.length) :
    (contPairTM N).tm.runFrom (contLoadCfg (y := y) N 5 x u p 0 ((j : ℤ) - 1)) (j + 1) =
      Cfg.mapState Sum.inr (choiceCoreCfg N (N.tm.initCfg x) true u 0 p) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero]
    have hw : (contLoadCfg (y := y) N 5 x u p 0 ((0 : ℤ) - 1)).workTapeSymbols
        (Fin.natAdd N.k 1) = none := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 5) _ _).apply _ = _
    dsimp only [contPairTM]
    rw [hw]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
      · intro i; fin_cases i <;>
          simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
      · intro i; fin_cases i <;>
          simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
  | succ j ih =>
    have hw : (contLoadCfg (y := y) N 5 x u p 0 (((j + 1 : ℕ) : ℤ) - 1)).workTapeSymbols
        (Fin.natAdd N.k 1) = some u[j] := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes, List.getElem?_eq_getElem (by omega : j < u.length)]
    have hs : (contPairTM N).tm.step
        (contLoadCfg (y := y) N 5 x u p 0 (((j + 1 : ℕ) : ℤ) - 1)) =
          contLoadCfg (y := y) N 5 x u p 0 ((j : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((contPairTM N).tm.tr (.inl 5) _ _).apply _ = _
      dsimp only [contPairTM]
      rw [hw]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Rewind the input buffer, then make the mandatory initial left move on
the choice buffer. The complete tape contents and physical input head survive.
**Proof sketch.** The same decreasing-head induction as the choice rewind;
the left-blank transition resets this head to zero and starts the next rewind. -/
private lemma cont_rewind_input (N : FinNDTM Bool) {y : List Bool}
    (x u : List Bool) (p : Fin (y.length + 2)) (j : ℕ) (hj : j ≤ x.length) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 4 x u p ((j : ℤ) - 1) u.length) (j + 1) =
        contLoadCfg (y := y) N 5 x u p 0 ((u.length : ℤ) - 1) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero]
    have hw : (contLoadCfg (y := y) N 4 x u p ((0 : ℤ) - 1) u.length).workTapeSymbols
        (Fin.natAdd N.k 0) = none := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 4) _ _).apply _ = _
    dsimp only [contPairTM]
    rw [hw]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
  | succ j ih =>
    have hw : (contLoadCfg (y := y) N 4 x u p (((j + 1 : ℕ) : ℤ) - 1) u.length).workTapeSymbols
        (Fin.natAdd N.k 0) = some x[j] := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes, List.getElem?_eq_getElem (by omega : j < x.length)]
    have hs : (contPairTM N).tm.step
        (contLoadCfg (y := y) N 4 x u p (((j + 1 : ℕ) : ℤ) - 1) u.length) =
          contLoadCfg (y := y) N 4 x u p ((j : ℤ) - 1) u.length := by
      unfold MultiTapeTM.step
      change ((contPairTM N).tm.tr (.inl 4) _ _).apply _ = _
      dsimp only [contPairTM]
      rw [hw]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Appending optional bits at the two right blanks realizes precisely the
corresponding list appends; all source and capture tapes remain blank. -/
private lemma cont_write_apply (N : FinNDTM Bool) {y : List Bool}
    (q q' : Fin 6) (x u : List Bool) (p : Fin (y.length + 2))
    (m : SignType) (bx bu : Option Bool) :
    (Action.mk m (choiceTapes (fun _ => (none, 0))
      (bx.map some, if bx.isSome then 1 else 0)
      (bu.map some, if bu.isSome then 1 else 0) (none, 0)) none
      (some (.inl q'))).apply (contLoadCfg (y := y) N q x u p x.length u.length) =
        contLoadCfg (y := y) N q' (x ++ bx.toList) (u ++ bu.toList) (moveInputPos p m)
          (x ++ bx.toList).length (u ++ bu.toList).length := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [contLoadCfg, choiceTapes]
    · intro i
      fin_cases i <;> cases bx <;> cases bu <;>
        simp [contLoadCfg, choiceTapes, bufferTape_append]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [contLoadCfg, choiceTapes]
    · intro i
      fin_cases i <;> cases bx <;> cases bu <;>
        simp [contLoadCfg, choiceTapes]

/-- Read the physical input at the loader's explicit position, including its
right boundary. The buffers have no effect on this read. -/
private lemma cont_load_read (N : FinNDTM Bool) {y : List Bool} (q : Fin 6)
    (x u : List Bool) (i : ℕ) (hi : i ≤ y.length) (a b : ℤ) :
    (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ a b).inputSymbol = y[i]? := by
  exact inputSymbol_at _ i hi rfl

/-- One right-going loader transition carries an exact physical step bound
and installs the appended buffers, provided its finite table has the displayed
write actions. -/
private lemma cont_load_right (N : FinNDTM Bool) {y : List Bool}
    (q q' : Fin 6) (x u : List Bool) (i : ℕ) (hi : i < y.length)
    (bx bu : Option Bool)
    (htr : (contPairTM N).tm.tr (.inl q) y[i]?
      (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ x.length u.length).workTapeSymbols =
        ⟨1, choiceTapes (fun _ => (none, 0))
          (bx.map some, if bx.isSome then 1 else 0)
          (bu.map some, if bu.isSome then 1 else 0) (none, 0), none, some (.inl q')⟩) :
    (contPairTM N).tm.step
      (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ x.length u.length) =
        contLoadCfg (y := y) N q' (x ++ bx.toList) (u ++ bu.toList) ⟨i + 2, by omega⟩
          (x ++ bx.toList).length (u ++ bu.toList).length := by
  unfold MultiTapeTM.step
  change ((contPairTM N).tm.tr (.inl q) _ _).apply _ = _
  rw [cont_load_read N q x u i (by omega), htr, cont_write_apply]
  congr 1
  apply Fin.ext
  rw [show (1 : SignType) = .pos from rfl,
    moveInputPos_pos_of_ne_right _ (by simp; omega)]

/-- The suffix copier appends each remaining physical input bit in exactly
one step. The prefix buffer is preserved and physical output stays empty.
**Proof sketch.** Induct on the remaining suffix, extending the physical
prefix and the copied suffix together in the inductive step. -/
private lemma cont_copy_run (N : FinNDTM Bool) (y rest : List Bool) :
    ∀ (pre x u : List Bool) (hy : y = pre ++ rest),
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨pre.length + 1, by simp [hy]; omega⟩
        x.length u.length) rest.length =
          contLoadCfg (y := y) N 3 x (u ++ rest) ⟨y.length + 1, by omega⟩
            x.length (u ++ rest).length := by
  induction rest with
  | nil => intro pre x u hy; subst y; simp [MultiTapeTM.runFrom_zero]
  | cons b rest ih =>
    intro pre x u hy
    have hs := cont_load_right (y := y) N 3 3 x u pre.length (by simp [hy]) none (some b) (by
      have hr : y[pre.length]? = some b := by simp [hy]
      rw [hr]
      rfl)
    simp only [Option.toList_none, Option.toList_some, List.append_nil] at hs
    simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hs]
    have hh : y = (pre ++ [b]) ++ rest := by simp [hy, List.append_assoc]
    simpa only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] using ih (pre ++ [b]) x (u ++ [b]) hh

/-- After suffix copying, one left move plus the two exact rewinds enters the
proved simulator. No source choices are consumed during these administrative steps. -/
private lemma cont_start_core (N : FinNDTM Bool) (y x u : List Bool) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨y.length + 1, by omega⟩ x.length u.length)
      (1 + (x.length + 1) + (u.length + 1)) =
        Cfg.mapState Sum.inr (choiceCoreCfg N (N.tm.initCfg x) true u 0
          ⟨y.length + 1, by omega⟩) := by
  have hs : (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨y.length + 1, by omega⟩ x.length u.length) 1 =
        contLoadCfg (y := y) N 4 x u ⟨y.length + 1, by omega⟩
          ((x.length : ℤ) - 1) u.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 3) _ _).apply _ = _
    rw [cont_load_read N 3 x u y.length (le_refl _)]
    simp only [List.getElem?_length]
    dsimp only [contPairTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
  rw [MultiTapeTM.runFrom_add _ (1 + (x.length + 1)) (u.length + 1),
    MultiTapeTM.runFrom_add _ 1 (x.length + 1)]
  rw [hs, cont_rewind_input N x u _ x.length (le_refl _),
    cont_rewind_choices N x u _ u.length (le_refl _)]

/-- The suffix-copy, rewind, and native simulation phases compose with their
exact time bounds. A halted source's full output, including its final emission,
is tested only after the complete choice word has been consumed. -/
private lemma cont_suffix_run (N : FinNDTM Bool) (y pre x u : List Bool)
    (hy : y = pre ++ u) :
    let result := (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0)
      (u.length + (1 + (x.length + 1) + (u.length + 1)) + (u.length + 1))
    result.state = none ∧ result.output =
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])] := by
  have hc := cont_copy_run N y u pre x [] hy
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hc
  dsimp only
  rw [MultiTapeTM.runFrom_add _
      (u.length + (1 + (x.length + 1) + (u.length + 1))) (u.length + 1),
    MultiTapeTM.runFrom_add _ u.length (1 + (x.length + 1) + (u.length + 1)),
    hc, cont_start_core, cont_core_run]
  have h := choiceCore_timed (y := y) N (N.tm.initCfg x) true
    (choiceCore_initial_tag N x) u ⟨y.length + 1, by omega⟩
  exact ⟨by simpa only [Cfg.mapState, Option.map_eq_none_iff] using h.1, h.2⟩

/-- An aligned doubled bit is copied to the input buffer in exactly two
steps, without touching choices or emitting output. -/
private lemma cont_parse_double (N : FinNDTM Bool) (y pre rest x : List Bool)
    (b : Bool) (hy : y = pre ++ b :: b :: rest) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0) 2 =
        contLoadCfg (y := y) N 0 (x ++ [b]) [] ⟨pre.length + 3, by simp [hy]; omega⟩
          (x ++ [b]).length 0 := by
  have h1 := cont_load_right (y := y) N 0 (if b then 2 else 1) x [] pre.length
    (by simp [hy]) none none (by
      have hr : y[pre.length]? = some b := by simp [hy]
      rw [hr]
      have hz : choiceTapes (fun (_ : Fin N.k) => ((none : Option (Option Bool)), (0 : SignType)))
          (none, 0) (none, 0) (none, 0) = fun _ => (none, 0) := by
        funext i
        refine Fin.addCases (fun _ => by simp [choiceTapes]) (fun i => ?_) i
        fin_cases i <;> simp [choiceTapes]
      cases b <;> simp [contPairTM, hz])
  have h2 := cont_load_right (y := y) N (if b then 2 else 1) 0 x [] (pre.length + 1)
    (by simp [hy]) (some b) none (by
      have hr : y[pre.length + 1]? = some b := by simp [hy]
      rw [hr]
      cases b <;> rfl)
  simp only [Option.toList_none, Option.toList_some, List.append_nil,
    List.length_nil, Nat.cast_zero] at h1 h2
  simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  rw [h1]
  exact h2

/-- The aligned separator starts suffix copying after exactly two silent
transitions, leaving the already copied input word unchanged. -/
private lemma cont_parse_separator (N : FinNDTM Bool) (y pre u x : List Bool)
    (hy : y = pre ++ false :: true :: u) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0) 2 =
        contLoadCfg (y := y) N 3 x [] ⟨pre.length + 3, by simp [hy]; omega⟩ x.length 0 := by
  have hz : choiceTapes (fun (_ : Fin N.k) => ((none : Option (Option Bool)), (0 : SignType)))
      (none, 0) (none, 0) (none, 0) = fun _ => (none, 0) := by
    funext i
    refine Fin.addCases (fun _ => by simp [choiceTapes]) (fun i => ?_) i
    fin_cases i <;> simp [choiceTapes]
  have h1 := cont_load_right (y := y) N 0 1 x [] pre.length
    (by simp [hy]) none none (by
      have hr : y[pre.length]? = some false := by simp [hy]
      rw [hr]
      simp [contPairTM, hz])
  have h2 := cont_load_right (y := y) N 1 3 x [] (pre.length + 1)
    (by simp [hy]) none none (by
      have hr : y[pre.length + 1]? = some true := by simp [hy]
      rw [hr]
      simp [contPairTM, hz])
  simp only [Option.toList_none, List.append_nil, List.length_nil, Nat.cast_zero] at h1 h2
  simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  rw [h1]
  exact h2

/-- On a valid encoded pair, the doubled prefix and separator are parsed in
exactly `2*|x|+2` steps. The prefix buffer contains precisely the undoubled word.
**Proof sketch.** Induct on the first component. A data block invokes the
two-step copying lemma; the empty component invokes the separator lemma.
The generalized existing buffer and physical prefix make every seam explicit. -/
private lemma cont_parse_run (N : FinNDTM Bool) (y x u : List Bool) :
    ∀ (pre a : List Bool) (hy : y = pre ++ pairEncode x u),
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 a [] ⟨pre.length + 1, by simp [hy]; omega⟩ a.length 0)
      (2 * x.length + 2) =
        contLoadCfg (y := y) N 3 (a ++ x) []
          ⟨pre.length + 2 * x.length + 3, by simp [hy, pairEncode]; omega⟩ (a ++ x).length 0 := by
  induction x with
  | nil =>
    intro pre a hy
    simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, List.append_nil] using
      cont_parse_separator N y pre u a (by simpa [pairEncode] using hy)
  | cons b x ih =>
    intro pre a hy
    have hy' : y = pre ++ b :: b :: pairEncode x u := by
      simpa [pairEncode, List.append_assoc] using hy
    have hr := cont_parse_double N y pre (pairEncode x u) a b hy'
    have hh : y = (pre ++ [b, b]) ++ pairEncode x u := by
      simpa [List.append_assoc] using hy'
    conv_lhs =>
      arg 2
      simp only [List.length_cons]
      rw [show 2 * (x.length + 1) + 2 = 2 + (2 * x.length + 2) by omega]
    rw [MultiTapeTM.runFrom_add _ 2 (2 * x.length + 2), hr]
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using
        ih (pre ++ [b, b]) (a ++ [b]) hh

/-- Blank-tape initialization, parsing, copying, rewinds and simulation give
a genuine whole-machine contract on every valid pair, with a linear bound.
**Proof sketch.** The loader starts with two empty buffers and blank source
tapes. Sum the parser's `2|x|+2` steps, suffix copying's `|u|`, the
`|x|+|u|+3` rewind/dispatch steps, and the core's `|u|+1` steps. The sum
`3|x|+3|u|+6` fits `3(|pairEncode x u|+1)`. -/
private lemma cont_pair_computes (N : FinNDTM Bool) (x u : List Bool) :
    (contPairTM N).ComputesInTime (pairEncode x u)
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])]
      (3 * ((pairEncode x u).length + 1)) := by
  let y := pairEncode x u
  have hi : (contPairTM N).tm.initCfg y =
      contLoadCfg (y := y) N 0 [] [] ⟨1, by omega⟩ 0 0 := by
    refine Cfg.ext rfl (Fin.ext (by simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg])) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
  have hp := cont_parse_run N y x u [] [] rfl
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, Nat.zero_add] at hp
  have hf := cont_suffix_run N y (x.flatMap (fun b => [b, b]) ++ [false, true]) x u rfl
  have hlen : (x.flatMap (fun b => [b, b]) ++ [false, true]).length + 1 =
      2 * x.length + 3 := by simp; omega
  simp only [hlen] at hf
  have hbase : (contPairTM N).ComputesInTime y
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])]
      ((2 * x.length + 2) +
        (u.length + (1 + (x.length + 1) + (u.length + 1)) + (u.length + 1))) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hi, hp]
    exact hf
  apply hbase.mono
  simp [pairEncode]
  omega

/-- The split-search failure word is rejected in one transition, including
when the source NDTM would accept an empty input and empty choice word. -/
private lemma cont_pair_empty (N : FinNDTM Bool) :
    (contPairTM N).ComputesInTime [] [false] 1 := by
  apply (computesInTime_iff _ _ _ _).mpr
  simp [MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, Cfg.inputSymbol, contPairTM]

/-- The library split emitter, retaining the exact encoded pair on success
and its distinguished empty failure word otherwise. -/
private def contSplitWord (C c : ℕ) (y : List Bool) : List Bool :=
  match solveSplit C c y.length with
  | some i => pairEncode (y.take i) (y.drop i)
  | none => []

/-- Split emission increases length by at most the doubled-prefix overhead.
This bound holds before any validity assumption. -/
private lemma cont_split_length (C c : ℕ) (y : List Bool) :
    (contSplitWord C c y).length ≤ 2 * y.length + 2 := by
  cases hs : solveSplit C c y.length with
  | none => simp [contSplitWord, hs]
  | some i =>
    have hi := (certificateSplit_spec C c y.length i (by
      simpa only [cont_split_bridge] using hs)).1
    simp [contSplitWord, hs, pairEncode]
    omega

/-- Every output of split search is handled in linear time, with exactly the
verifier's decision bit. Failure rejects; success uses the unique recovered
prefix and the exact certificate length.
**Proof sketch.** In the success case the split specification proves the
dropped suffix has the required length, so `choiceVerifier_append` identifies
the verdict. In the failure case `choiceVerifier_no_split` excludes membership.
The emitted pair's length is bounded on both branches before composition. -/
private lemma cont_split_answer (N : FinNDTM Bool) (C c : ℕ) (y : List Bool) :
    (contPairTM N).ComputesInTime (contSplitWord C c y)
      [MultiTapeTM.indicator (choiceVerifier N C c) y] (3 * (2 * y.length + 3)) := by
  classical
  cases hs : solveSplit C c y.length with
  | none =>
    have hn := choiceVerifier_no_split N C c y (by
      simpa only [cont_split_bridge] using hs)
    simpa only [contSplitWord, hs, MultiTapeTM.indicator, if_neg hn] using
      (cont_pair_empty N).mono (by omega : 1 ≤ 3 * (2 * y.length + 3))
  | some i =>
    obtain ⟨hi, he⟩ := certificateSplit_spec C c y.length i (by
      simpa only [cont_split_bridge] using hs)
    have hu : (y.drop i).length = C * ((y.take i).length + 1) ^ c := by
      rw [List.length_drop, List.length_take_of_le hi]
      omega
    have hv := choiceVerifier_append N C c (y.take i) (y.drop i) hu
    rw [List.take_append_drop] at hv
    have hout : MultiTapeTM.indicator (choiceVerifier N C c) y =
        decide ((N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).state = none ∧
          (N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).output = [true]) := by
      simp only [MultiTapeTM.indicator, hv]
      split <;> simp_all
    rw [contSplitWord, hs, hout]
    apply (cont_pair_computes N (y.take i) (y.drop i)).mono
    have hl := cont_split_length C c y
    simp only [contSplitWord, hs] at hl
    omega

/-- The complete choice-word verifier is polynomial-time on all inputs.
**Proof sketch.** The audited native split search costs `A(n+1)^(c+2)`.
Its output has length at most `2n+2`. Timed buffered composition takes at
most that cost plus the output length plus two steps to start the loader;
the loader/simulator then costs at most `3(2n+3)`. Thus the whole budget
is at most `(A+13)(n+1)^(c+2)`. The second phase is proved on every possible
split-search output; no untimed composition or unstated totality is used. -/
private lemma cont_choiceVerifier_mem_P (N : FinNDTM Bool) (C c : ℕ) :
    choiceVerifier N C c ∈ P := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_splitSolve C c
  refine mem_P_iff.mpr ⟨A + 13, c + 2, bufferedCompTM M (contPairTM N), ?_⟩
  intro y
  have hfirst : M.ComputesInTime y (contSplitWord C c y)
      (A * (y.length + 1) ^ (c + 2)) := hM y
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M (contPairTM N) y (contSplitWord C c y) _ hfirst
  obtain ⟨tag, _, hr⟩ := bufferedSecondCfg_run M (contPairTM N)
    ((contPairTM N).tm.initCfg (contSplitWord C c y)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads
    (3 * (2 * y.length + 3))
  have hc := (computesInTime_iff _ _ _ _).mp (cont_split_answer N C c y)
  have hbase : (bufferedCompTM M (contPairTM N)).ComputesInTime y
      [MultiTapeTM.indicator (choiceVerifier N C c) y] (a + 3 * (2 * y.length + 3)) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  apply hbase.mono
  have hl := cont_split_length C c y
  have hp : y.length + 1 ≤ (y.length + 1) ^ (c + 2) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos y.length) (by omega : 1 ≤ c + 2)
  calc
    a + 3 * (2 * y.length + 3) ≤
        A * (y.length + 1) ^ (c + 2) + 13 * (y.length + 1) := by omega
    _ ≤ A * (y.length + 1) ^ (c + 2) + 13 * (y.length + 1) ^ (c + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 13 hp) _
    _ = (A + 13) * (y.length + 1) ^ (c + 2) := by ring

/-- **The choice word is a certificate** [AB09, Theorem 2.6, ⊆-direction of the
union]: every fixed-degree nondeterministic time class is contained in `NP`.

**Proof sketch.** Let `N` decide `L` within `T n = a·(n^c + 1)` (the `NTIME`
constant `a`). Certificate parameters: coefficient `2a`, degree `c`, so
`Q n = 2a·(n+1)^c ≥ T n` (as `n^c ≤ (n+1)^c` and `1 ≤ (n+1)^c`). The verifier
language is
`V = {x ++ u : |u| = Q |x| ∧ the run of N on x under choice word u is halted with output [true]}`
— a well-defined set, the split being unique since `n ↦ n + Q n` is strictly
increasing. Membership equivalence: forward, an accepting branch of length `T n` pads
with `false`-bits to length exactly `Q n`, still halted-with-`[true]` by
`Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`; backward, the length-
`T n` prefix of an accepting `u` is halted by the decider's `HaltsWithin`, absorption
gives it the same state and output, and `Turing.FinNDTM.AcceptsWithin` at `T n`
returns `x ∈ L`. `V ∈ P` by a deciding machine whose obligations are named for the
fill: (i) recover the unique split — search `n ≤ m` for `n + Q n = m`, **rejecting
explicitly when no solution exists** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`), with a polynomial-evaluation machine for
the explicit formula `Q`; (ii) copy the choice suffix `u` to a dedicated work tape;
(iii) a clocked product simulation of the **fixed** machine `N`: `N`'s work tapes as
disjoint tape blocks (the `Simulation` lockstep gadgets are the precedent), `N`'s
state in finite control, and `N`'s input head as a binary position counter with the
**input-window guard** — `N` reads `x` only, so when the tracked position leaves the
window the simulator feeds the boundary blank instead of the symbol of `x ++ u` under
its own head, emulating the clamping of `Turing.moveInputPos` against the recovered
`n`; (iv) per simulated step, consume the next bit of the copied choice tape to select
between `N`'s two transition tables; (v) **output capture**: buffer `N`'s emissions on
a work tape and never write to the real output during simulation (the append-only
isolation obligation of the `Complexity.NP_subset_EXP` sketch;
`Turing.universalCaptureTM` is the in-repo precedent); (vi) the verdict — output
`[true]` iff the simulated run is halted with buffer exactly `[true]`, else `[false]`.
Budget: `Q n ≤ m` simulated steps at polynomial bookkeeping each, so polynomial in
`m`; conclude `V ∈ P` via `Complexity.mem_P_of_dtime_le` and `L ∈ NP` with
`(2a, c, V)`.

**Partial fill note (epoch 2B).** The certificate correspondence, finite split-search
specification, and two native phase contracts are proved below their private
definitions. `choiceCopy_timed` assumes a prepared unary split countdown and copies
the two words in `|x ++ u| + 1` steps. `choiceCore_timed` assumes prepared data tapes
and uses `|u| + 1` steps. In that core, the virtual input head is represented directly
by a head on the copied input buffer and a finite boundary tag, using
`virtualMove_correct`, rather than a binary position counter. This preserves the
specified guarded reads and clamping with constant overhead per source step. All
source emissions are captured on a separate tape; a finite summary recognizes
exactly `[true]` for the final verdict. These prepared-configuration contracts do
not supply a decider from blank tapes: the native arithmetic/split-search machine,
its rejecting branch, countdown preparation, rewinds, and timed phase composition
remain the single admitted verifier-membership obligation in this partial fill.

**Continuation completion (E2-cont-B).** The native library split emitter
`computesFunInTime_splitSolve C c` has exactly this file's coefficient `C`.
The new paired-input loader fills the input and choice buffers, rewinds them,
and enters the unchanged `choiceCore`; it needs no unary countdown. The
library emitter's empty failure word rejects. Timed buffered composition and
`cont_choiceVerifier_mem_P` now supply the whole blank-tape decider with bound
`(A+13)(m+1)^(c+2)`, where `A(m+1)^(c+2)` bounds split search. The predecessor's
copier and all other private phase proofs are retained unchanged. -/
theorem ntime_poly_subset_NP (c : ℕ) : NTIME (fun n => n ^ c + 1) ⊆ NP := by
  rintro L ⟨a, N, hN⟩
  refine ⟨2 * a, c, choiceVerifier N (2 * a) c, ?_,
    choice_certificate_iff N L a c hN⟩
  exact cont_choiceVerifier_mem_P N (2 * a) c

/-- Select the physical choice positions at which the deterministic scheduler
writes a guess. Administrative positions consume physical choices but contribute
no certificate bit. A short choice word contributes only its existing positions. -/
private def contSelect : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | emit :: mask, b :: w => (if emit then [b] else []) ++ contSelect mask w

/-- A fixed mask extracts precisely one certificate bit at each marked position,
independently of the values of the physical choices. -/
private lemma cont_select_length (mask w : List Bool) (hw : w.length = mask.length) :
    (contSelect mask w).length = (mask.filter id).length := by
  induction mask generalizing w with
  | nil => simp [contSelect]
  | cons emit mask ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      have ht : w.length = mask.length := by simpa using hw
      cases emit <;> simp [contSelect, ih w ht]

/-- Every certificate of the scheduled length is realized at its actual physical
write positions. Unused choices may all be false; a zero-write schedule realizes
exactly the empty certificate.
**Proof sketch.** Induct on the mask. An unmarked position prepends an arbitrary
false choice. A marked position consumes and prepends the next certificate bit. -/
private lemma cont_select_surjective (mask u : List Bool)
    (hu : u.length = (mask.filter id).length) :
    ∃ w : List Bool, w.length = mask.length ∧ contSelect mask w = u := by
  induction mask generalizing u with
  | nil =>
    have he : u = [] := by simpa using hu
    subst u
    exact ⟨[], rfl, rfl⟩
  | cons emit mask ih =>
    cases emit with
    | false =>
      obtain ⟨w, hw, he⟩ := ih u (by simpa using hu)
      exact ⟨false :: w, by simp [hw], by simpa [contSelect] using he⟩
    | true =>
      cases u with
      | nil => simp at hu
      | cons b u =>
        obtain ⟨w, hw, he⟩ := ih u (by simpa using hu)
        exact ⟨b :: w, by simp [hw], by simp [contSelect, he]⟩

/-- The deterministic emission schedule, including the halting transition's
emission and excluding all subsequent absorbed steps. Evaluating it on the
unary word of length `n` gives a schedule depending on `n` alone. -/
private def contEmissionMask (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : ℕ → List Bool
  | 0 => []
  | t + 1 => (M.tm.outputSymbol c).isSome :: contEmissionMask M (M.tm.step c) t

/-- The schedule has one entry per physical scheduler transition. -/
private lemma cont_mask_length (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (contEmissionMask M c t).length = t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => simp [contEmissionMask, ih]

/-- Marked positions count every source emission exactly once, including an
emission on the halting transition.
**Proof sketch.** One step appends exactly `outputSymbol.toList`; its length
is zero or one according to the schedule's first entry. Induct on elapsed time. -/
private lemma cont_mask_count (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    c.output.length + ((contEmissionMask M c t).filter id).length =
      (M.tm.runFrom c t).output.length := by
  induction t generalizing c with
  | zero => simp [contEmissionMask]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := ih (M.tm.step c)
    rw [MultiTapeTM.step_output] at h
    cases he : M.tm.outputSymbol c <;>
      simpa [contEmissionMask, he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A native nondeterministic guessing phase driven by a deterministic
scheduler. At every scheduler emission, capture the current physical choice
bit on the extra tape; all other transitions ignore it. Source reads never
consult that extra tape. A completed scheduler stays at the live return
state `none`; a surrounding controller must perform the later dispatch. -/
private def contGuessTM (M : FinTM Bool) : FinNDTM Bool where
  k := M.k + 1
  State := Option M.State
  tm :=
    { q₀ := some M.tm.q₀
      tr := fun bit q inp work => match q with
        | none => controlAction 0 (some none)
        | some q =>
          let a := M.tm.tr q inp (fun i => work i.castSucc)
          captureAction some none {a with output := a.output.map (fun _ => bit)} }

/-- The guessing-phase invariant: the deterministic scheduler's state, input
head and work tapes are exact; the guessed word is held separately at its
right blank, and physical output is empty. -/
private def contGuessCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u : List Bool) :
    Cfg (contGuessTM M).k Bool (contGuessTM M).State x :=
  ⟨some c.state, c.inputPos,
    (fun i => if h : i.val < M.k then c.workTapes ⟨i, h⟩ else bufferTape u),
    (fun i => if h : i.val < M.k then c.workTapePos ⟨i, h⟩ else u.length), []⟩

/-- One native guessing transition selects its physical choice exactly when
the scheduler emits. It preserves the complete source configuration, apart
from storing chosen rather than emitted data on the separate capture tape.
**Proof sketch.** For a live source, instantiate the capture-action transformer
with the emission replaced by the current choice. Check source and capture
tapes separately. A halted source and the phase's return state both stutter. -/
private lemma cont_guess_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u : List Bool) (bit : Bool) :
    (contGuessTM M).tm.stepWith bit (contGuessCfg M c u) =
      contGuessCfg M (M.tm.step c)
        (u ++ if (M.tm.outputSymbol c).isSome then [bit] else []) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    simp only [MultiTapeTM.outputSymbol, hs, Option.isSome_none, Bool.false_eq_true,
      if_false, List.append_nil]
    unfold NDTM.stepWith
    simp only [contGuessCfg, hs]
    change (controlAction 0 (some none)).apply _ = _
    rw [controlAction_apply, moveInputPos_zero]
  | some q =>
    let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
    have hi : (contGuessCfg M c u).inputSymbol = c.inputSymbol := rfl
    have hw : (fun i => (contGuessCfg M c u).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
      funext i
      simp [contGuessCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (contGuessCfg M c u).state = some (some q) := by simp [contGuessCfg, hs]
    unfold NDTM.stepWith
    rw [hstate]
    dsimp only [contGuessTM]
    rw [hi, hw]
    change (captureAction some none {a with output := a.output.map (fun _ => bit)}).apply
      (contGuessCfg M c u) = contGuessCfg M (M.tm.step c)
        (u ++ if (M.tm.outputSymbol c).isSome then [bit] else [])
    have hc : M.tm.step c = a.apply c := by simp [MultiTapeTM.step, hs, a]
    have he : M.tm.outputSymbol c = a.output := by simp [MultiTapeTM.outputSymbol, hs, a]
    rw [hc, he]
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · cases ha : a.state <;> simp [captureAction, contGuessCfg, ha]
    · funext i
      by_cases h : i.val < M.k
      · simp [captureAction, contGuessCfg, h]
      · cases ho : a.output <;>
          simp [captureAction, contGuessCfg, h, ho, bufferTape_append]
    · funext i
      by_cases h : i.val < M.k
      · simp [captureAction, contGuessCfg, h]
      · cases ho : a.output <;> simp [captureAction, contGuessCfg, h, ho]

/-- The native phase realizes the emission-position mask exactly, with one
physical transition per choice and no changes to the source simulation.
**Proof sketch.** Induct on the physical choice word. The one-step lemma
appends its bit precisely at the first marked position; the remaining source
schedule is the schedule from the stepped configuration. -/
private lemma cont_guess_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u w : List Bool) :
    (contGuessTM M).tm.runWith w (contGuessCfg M c u) =
      contGuessCfg M (M.tm.runFrom c w.length)
        (u ++ contSelect (contEmissionMask M c w.length) w) := by
  induction w generalizing c u with
  | nil => simp [contSelect, contEmissionMask]
  | cons bit w ih =>
    rw [NDTM.runWith_cons, cont_guess_step, ih]
    simp only [List.length_cons, contEmissionMask, contSelect,
      MultiTapeTM.runFrom_succ_eq_step, List.append_assoc]

/-- The guessing phase's genuine initial configuration has the scheduler's
blank source bank and an empty capture tape. -/
private lemma cont_guess_initial (M : FinTM Bool) (x : List Bool) :
    (contGuessTM M).tm.initCfg x = contGuessCfg M (M.tm.initCfg x) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : i.val < M.k <;>
      simp [NDTM.initCfg, MultiTapeTM.initCfg, Cfg.init, contGuessCfg]
  · funext i
    by_cases h : i.val < M.k <;>
      simp [NDTM.initCfg, MultiTapeTM.initCfg, Cfg.init, contGuessCfg]

/-- The native guessing phase has both witness extraction and witness coverage
at the scheduler's physical step budget. It captures exactly as many bits as
the completed scheduler emitted, and all words of that length occur.
**Proof sketch.** The emission-count invariant fixes the mask's number of
marked positions. Exact-length selection gives extraction; mask surjectivity
gives coverage. The native run invariant then supplies the whole configuration,
not merely the captured tape. The host's return state is still live here. -/
private lemma cont_guess_coverage (M : FinTM Bool) (x v : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x v T) :
    (∀ w : List Bool, w.length = T → ∃ u : List Bool, u.length = v.length ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = T ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) := by
  let mask := contEmissionMask M (M.tm.initCfg x) T
  have hlen : mask.length = T := cont_mask_length M _ T
  have hcount : (mask.filter id).length = v.length := by
    have h := cont_mask_count M (M.tm.initCfg x) T
    have ho := ((computesInTime_iff _ _ _ _).mp hM).2
    rw [ho] at h
    simpa only [MultiTapeTM.initCfg, Cfg.init, List.length_nil, Nat.zero_add] using h
  have hrun (w : List Bool) (hw : w.length = T) :
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) (contSelect mask w) := by
    rw [cont_guess_initial, cont_guess_run, hw, List.nil_append]
  constructor
  · intro w hw
    exact ⟨contSelect mask w, (cont_select_length mask w (hw.trans hlen.symm)).trans hcount,
      hrun w hw⟩
  · intro u hu
    obtain ⟨w, hw, he⟩ := cont_select_surjective mask u (hu.trans hcount.symm)
    exact ⟨w, hw.trans hlen, by rw [hrun w (hw.trans hlen), he]⟩

/-- The reverse compiler's complete polynomial envelope has the exact padded
`NTIME` form demanded by the audited statement, including zero certificate
coefficient, zero degree, and empty inputs.
**Proof sketch.** Bound `n+1` and `(n+1)^c` by `(n+1)^max(1,c)`, add their
coefficients, raise to `r`, then apply the proved `succ_pow_le`. -/
private lemma cont_guess_time_bound (C c K r n : ℕ) :
    K * (n + C * (n + 1) ^ c + 1) ^ r ≤
      (K * (C + 1) ^ r * 2 ^ (r * max 1 c)) * (n ^ (r * max 1 c) + 1) := by
  have hp : 0 < n + 1 := Nat.succ_pos n
  have h1 : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right hp (Nat.le_max_left 1 c)
  have hc : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right hp (Nat.le_max_right 1 c)
  have hsum : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hc
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    K * (n + C * (n + 1) ^ c + 1) ^ r ≤
        K * ((C + 1) * (n + 1) ^ max 1 c) ^ r :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsum r)
    _ = (K * (C + 1) ^ r) * (n + 1) ^ (r * max 1 c) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) r, Nat.mul_assoc]
    _ ≤ (K * (C + 1) ^ r) * (2 ^ (r * max 1 c) * (n ^ (r * max 1 c) + 1)) :=
      Nat.mul_le_mul_left _ (succ_pow_le n (r * max 1 c))
    _ = _ := by ring

/-- An all-branch compiler with the stated complete polynomial envelope lands
in one fixed-degree `NTIME` component. Acceptance at the enlarged budget is
proved by all-branch truncation as well as accepting-branch padding. -/
private lemma cont_guess_normalize (L : Language Bool) (C c : ℕ)
    (h : ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * (n + 1) ^ c + 1) ^ r)) :
    L ∈ ⋃ e : ℕ, NTIME fun n => n ^ e + 1 := by
  obtain ⟨K, r, N, hN⟩ := h
  refine Set.mem_iUnion.mpr ⟨r * max 1 c, K * (C + 1) ^ r * 2 ^ (r * max 1 c), N, ?_⟩
  intro x
  have ht := cont_guess_time_bound C c K r x.length
  refine ⟨(hN x).1.mono ht, ?_⟩
  exact (hN x).2.trans (acceptsWithin_iff_of_halts (hN x).1 ht).symm

/-- The proved unary polynomial generator supplies a concrete native guessing
phase for every exact certificate length. Its physical schedule is evaluated
on the unary input of length `n`, so it depends only on `n`, including when
`C=0`. This contract does not yet preserve an arbitrary original input or
run its verifier; those are obligations of the surrounding reverse compiler. -/
private lemma cont_poly_guess_phase (C c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ), ∀ n : ℕ,
    let x := List.replicate n true
    let T := A * (n + 1) ^ (c + 1)
    (∀ w : List Bool, w.length = T → ∃ u : List Bool,
      u.length = C * (n + 1) ^ c ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = C * (n + 1) ^ c → ∃ w : List Bool,
      w.length = T ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_polyUnary C c
  refine ⟨M, A, fun n => ?_⟩
  have h := cont_guess_coverage M (List.replicate n true)
    (List.replicate (C * (n + 1) ^ c) true) (A * (n + 1) ^ (c + 1)) (by
      simpa only [List.length_replicate] using hM (List.replicate n true))
  simpa only [List.length_replicate] using h

/-- Normalize each nonblank physical input read to `true`. The physical input
and its head are retained; source work symbols are not normalized. -/
private def b2UnaryTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := M.State
  tm := ⟨M.tm.q₀, fun q inp work => M.tm.tr q (inp.map fun _ => true) work⟩

/-- View an arbitrary-input configuration over the unary word of the same
length, leaving its state, work tapes, heads, and output unchanged. -/
private def b2UnaryCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg k Bool S (List.replicate x.length true) :=
  ⟨c.state, ⟨c.inputPos.val, by simp⟩,
    c.workTapes, c.workTapePos, c.output⟩

/-- Normalization preserves both input blanks and maps every interior symbol
to the corresponding unary symbol, including at empty input. -/
private lemma b2_unary_read {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) :
    (b2UnaryCfg c).inputSymbol = c.inputSymbol.map (fun _ => true) := by
  by_cases h0 : c.inputPos.val = 0 <;>
    by_cases h1 : c.inputPos.val = x.length + 1 <;>
    simp [Cfg.inputSymbol, b2UnaryCfg, Fin.ext_iff, h0, h1]

/-- Applying an action commutes with changing to an equal-length unary input:
native clamping uses only the length, and no work symbol is changed. -/
private lemma b2_unary_apply {k : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    b2UnaryCfg (a.apply c) = a.apply (b2UnaryCfg c) := by
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  simp only [b2UnaryCfg, Action.apply, moveInputPos, List.length_replicate]
  split <;> rfl

/-- One step of the input-normalized scheduler is exactly a native step on
the unary word, including the absorbing halted case. -/
private lemma b2_unary_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    b2UnaryCfg ((b2UnaryTM M).tm.step c) = M.tm.step (b2UnaryCfg c) := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, b2UnaryTM, b2UnaryCfg, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, b2UnaryTM]
    change b2UnaryCfg ((M.tm.tr q (c.inputSymbol.map fun _ => true)
      c.workTapeSymbols).apply c) = _
    rw [b2_unary_apply]
    have hs' : (b2UnaryCfg c).state = some q := hs
    simp only [hs', b2_unary_read]
    rfl

/-- Every elapsed time, not just a declared upper bound, has exactly the
unary scheduler configuration. Thus first halts and emission times can be
selected from the input length alone. -/
private lemma b2_unary_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    b2UnaryCfg ((b2UnaryTM M).tm.runFrom c t) =
      M.tm.runFrom (b2UnaryCfg c) t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, ih, b2_unary_step,
      MultiTapeTM.runFrom_succ_eq_step]

/-- The normalized scheduler's genuine startup corresponds to the genuine
unary startup, with blank work tapes and initial input head one. -/
private lemma b2_unary_initial (M : FinTM Bool) (x : List Bool) :
    b2UnaryCfg ((b2UnaryTM M).tm.initCfg x) =
      M.tm.initCfg (List.replicate x.length true) := by
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  simp [b2UnaryCfg, b2UnaryTM, MultiTapeTM.initCfg, Cfg.init]

/-- Normalizing input reads also preserves every emission position; no
assumption of value-independent timing is extracted from a function contract. -/
private lemma b2_unary_mask (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    contEmissionMask (b2UnaryTM M) c t = contEmissionMask M (b2UnaryCfg c) t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [contEmissionMask, contEmissionMask, ih, b2_unary_step]
    congr 1
    have hs' : (b2UnaryCfg c).state = c.state := rfl
    cases hs : c.state <;>
      simp only [MultiTapeTM.outputSymbol, b2UnaryTM, hs', hs, b2_unary_read]
    rfl

/-- A unary timed computation transfers to every original word of that
length, at exactly the same time and with exactly the same completed output. -/
private lemma b2_unary_computes (M : FinTM Bool) (x v : List Bool) (t : ℕ)
    (hM : M.ComputesInTime (List.replicate x.length true) v t) :
    (b2UnaryTM M).ComputesInTime x v t := by
  have hr := b2_unary_run M ((b2UnaryTM M).tm.initCfg x) t
  rw [b2_unary_initial] at hr
  have hc := (computesInTime_iff _ _ _ _).mp hM
  apply (computesInTime_iff _ _ _ _).mpr
  exact ⟨(congrArg Cfg.state hr).trans hc.1, (congrArg Cfg.output hr).trans hc.2⟩

/-- A total unary scheduler has a first halt depending only on input length.
The bound is used to prove existence, never as a native phase-dispatch clock.
**Proof sketch.** Choose the least halting time on each unary input. Absorption
identifies its output with the output at the given bound. Exact normalized
lockstep transfers the first halt and all earlier live states to every word
of that length. -/
private lemma b2_unary_first (M : FinTM Bool) (f : ℕ → List Bool) (T : ℕ → ℕ)
    (hM : ∀ n, M.ComputesInTime (List.replicate n true) (f n) (T n)) :
    ∃ τ : ℕ → ℕ, ∀ x : List Bool,
      τ x.length ≤ T x.length ∧
      (b2UnaryTM M).ComputesInTime x (f x.length) (τ x.length) ∧
      ∀ s < τ x.length, ((b2UnaryTM M).tm.runFrom
        ((b2UnaryTM M).tm.initCfg x) s).state ≠ none := by
  classical
  have hex (n : ℕ) : ∃ t, (M.tm.runFrom
      (M.tm.initCfg (List.replicate n true)) t).state = none :=
    ⟨T n, ((computesInTime_iff _ _ _ _).mp (hM n)).1⟩
  refine ⟨fun n => Nat.find (hex n), fun x => ?_⟩
  have hh := Nat.find_spec (hex x.length)
  have ht := Nat.find_min' (hex x.length)
    ((computesInTime_iff _ _ _ _).mp (hM x.length)).1
  have ho := M.tm.runFrom_output_eq_of_halt
    (M.tm.initCfg (List.replicate x.length true)) ht hh
  have hc : M.ComputesInTime (List.replicate x.length true) (f x.length)
      (Nat.find (hex x.length)) := (computesInTime_iff _ _ _ _).mpr
    ⟨hh, ho.symm.trans ((computesInTime_iff _ _ _ _).mp (hM x.length)).2⟩
  refine ⟨ht, b2_unary_computes M x _ _ hc, fun s hs hh' => ?_⟩
  have hr := congrArg Cfg.state (b2_unary_run M ((b2UnaryTM M).tm.initCfg x) s)
  rw [b2_unary_initial] at hr
  exact Nat.find_min (hex x.length) hs (hr.symm.trans hh')

/-- The host's four disjoint tape banks: scheduler, assembled input, verifier,
and verifier output. Each machine bank has a private final buffer slot. -/
private def b2Slots {α : Type} (S V : FinTM Bool) (s : Fin S.k → α)
    (input : α) (v : Fin V.k → α) (output : α) :
    Fin ((S.k + 1) + (V.k + 1)) → α :=
  Fin.addCases
    (fun i => if h : i.val < S.k then s ⟨i, h⟩ else input)
    (fun i => if h : i.val < V.k then v ⟨i, h⟩ else output)

/-- Native reverse host. Administrative states copy the input, rewind its
physical head, and rewind the assembled buffer. The scheduler reads the
normalized physical input; its emissions append choices to the copied input.
The verifier uses only its own bank and the guarded virtual assembly input.
Both tables are definitionally identical outside live guessing states. -/
private def b2Host (S V : FinTM Bool) : FinNDTM Bool where
  k := (S.k + 1) + (V.k + 1)
  State := Fin 3 ⊕ (Option S.State ⊕ (Option V.State × Bool × Option Bool))
  tm :=
    { q₀ := .inl 0
      tr := fun bit q inp work => match q with
        | .inl q =>
          if q = 0 then
            match inp with
            | some b =>
              ⟨1, b2Slots S V (fun _ => (none, 0)) (some (some b), 1)
                (fun _ => (none, 0)) (none, 0), none, some (.inl 0)⟩
            | none => controlAction (-1) (some (.inl 1))
          else if q = 1 then
            match inp with
            | some _ => controlAction (-1) (some (.inl 1))
            | none => controlAction 1 (some (.inr (.inl (some S.tm.q₀))))
          else
            let inp := work (Fin.castAdd (V.k + 1) (Fin.last S.k))
            ⟨0, b2Slots S V (fun _ => (none, 0))
              (none, if inp.isSome then -1 else 1)
              (fun _ => (none, 0)) (none, 0), none,
              some (if inp.isSome then .inl 2
                else .inr (.inr (some V.tm.q₀, true, none)))⟩
        | .inr (.inl q) => match q with
          | none =>
            ⟨0, b2Slots S V (fun _ => (none, 0)) (none, -1)
              (fun _ => (none, 0)) (none, 0), none, some (.inl 2)⟩
          | some q =>
            leftAction (V.k + 1) (fun q => .inr (.inl q))
              ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q) inp
                (fun i => work (Fin.castAdd (V.k + 1) i)))
        | .inr (.inr (q, tag, summary)) => match q with
          | none =>
            ⟨0, fun _ => (none, 0), some (decide (summary = some true)), none⟩
          | some q =>
            let inp := work (Fin.castAdd (V.k + 1) (Fin.last S.k))
            let a := V.tm.tr q inp
              (fun i => work (Fin.natAdd (S.k + 1) i.castSucc))
            let m := virtualMove tag inp a.inputTape
            ⟨0, b2Slots S V (fun _ => (none, 0)) (none, m) a.workTapes
              (a.output.map some, if a.output.isSome then 1 else 0), none,
              some (.inr (.inr (a.state, virtualNextTag tag m,
                captureEmission summary a.output)))⟩ }

/-- Embed the guessing phase with the original word already on its buffer.
The verifier bank and its output capture remain blank throughout this phase. -/
private def b2GuessCfg (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (u : List Bool) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  leftCfg (fun q => .inr (.inl q)) (contGuessCfg (b2UnaryTM S) c (x ++ u))
    (fun _ _ => none) (fun _ => 0)

/-- Outside a live guessing state, the two native transition tables coincide
by the definition of the host, for every possible tuple of symbols. -/
private lemma b2_tables_coincide (S V : FinTM Bool) (q : (b2Host S V).State)
    (hq : ∀ s, q ≠ .inr (.inl (some s))) (inp : Option Bool)
    (work : Fin (b2Host S V).k → Option Bool) :
    (b2Host S V).tm.tr false q inp work = (b2Host S V).tm.tr true q inp work := by
  rcases q with q | (q | q)
  · rfl
  · cases q with
    | none => rfl
    | some q => exact False.elim (hq q rfl)
  · rfl

/-- A live host guessing step is the banked native guessing transition with
an inactive verifier bank. In particular a halting emission is appended before
the host enters its scheduler-return state.
**Proof sketch.** The left-bank projection has precisely the standalone
phase's reads. The library's disjoint-bank action identity embeds its step;
the predecessor's guessing-step invariant supplies the exact appended bit. -/
private lemma b2_guess_step (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state ≠ none) (u : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2GuessCfg S V c u) =
      b2GuessCfg S V ((b2UnaryTM S).tm.step c)
        (u ++ if ((b2UnaryTM S).tm.outputSymbol c).isSome then [bit] else []) := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    let g := contGuessCfg (b2UnaryTM S) c (x ++ u)
    have hstate : (b2GuessCfg S V c u).state = some (.inr (.inl (some q))) := by
      simp [b2GuessCfg, leftCfg, contGuessCfg, hs]
    have hi : (b2GuessCfg S V c u).inputSymbol = g.inputSymbol := rfl
    have hw : (fun i : Fin (S.k + 1) => (b2GuessCfg S V c u).workTapeSymbols
        (Fin.castAdd (V.k + 1) i)) = g.workTapeSymbols := by
      funext i
      simp [b2GuessCfg, leftCfg, Cfg.workTapeSymbols, g]
    unfold NDTM.stepWith
    rw [hstate]
    dsimp only [b2Host]
    simp only [hi]
    simp only [b2GuessCfg, leftCfg, Cfg.workTapeSymbols, Fin.addCases_left]
    change (leftAction (V.k + 1) (fun q : Option S.State => (Sum.inr (Sum.inl q) : (b2Host S V).State))
      ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q) g.inputSymbol g.workTapeSymbols)).apply
        (leftCfg (fun q : Option S.State => (Sum.inr (Sum.inl q) : (b2Host S V).State)) g (fun _ _ => none) (fun _ => 0)) = _
    rw [leftCfg_apply]
    have hg : ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q)
        g.inputSymbol g.workTapeSymbols).apply g =
        (contGuessTM (b2UnaryTM S)).tm.stepWith bit g := by
      simp [NDTM.stepWith, g, contGuessCfg, hs]
    rw [hg]
    dsimp only [g]
    rw [cont_guess_step]
    simp only [List.append_assoc]
    rfl

/-- The host follows the standalone emission mask until the actual first
scheduler halt. The preserved original input is a prefix of the assembly
buffer, and every other bank remains isolated.
**Proof sketch.** Induct on the physical choice word. The strict liveness
guard permits one guessing step, including the final source-halting step;
shift the guard by one for the remaining choices. -/
private lemma b2_guess_run (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (u w : List Bool)
    (hlive : ∀ s < w.length, ((b2UnaryTM S).tm.runFrom c s).state ≠ none) :
    (b2Host S V).tm.runWith w (b2GuessCfg S V c u) =
      b2GuessCfg S V ((b2UnaryTM S).tm.runFrom c w.length)
        (u ++ contSelect (contEmissionMask (b2UnaryTM S) c w.length) w) := by
  induction w generalizing c u with
  | nil => simp [contEmissionMask, contSelect]
  | cons bit w ih =>
    have hc : c.state ≠ none := hlive 0 (by simp)
    have ht : ∀ s < w.length,
        ((b2UnaryTM S).tm.runFrom ((b2UnaryTM S).tm.step c) s).state ≠ none := by
      intro s hs
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hlive (s + 1) (by simpa using hs)
    rw [NDTM.runWith_cons, b2_guess_step S V c hc, ih _ _ ht]
    simp only [List.length_cons, contEmissionMask, contSelect,
      MultiTapeTM.runFrom_succ_eq_step, List.append_assoc]

/-- Loader configuration: all machine tapes are blank and only the assembly
buffer is populated. The physical input is retained verbatim. -/
private def b2LoadCfg (S V : FinTM Bool) {x : List Bool} (q : Fin 3)
    (p : Fin (x.length + 2)) (pre : List Bool) (j : ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inl q), p,
    b2Slots S V (fun _ _ => none) (bufferTape pre) (fun _ _ => none) (fun _ => none),
    b2Slots S V (fun _ => 0) j (fun _ => 0) 0, []⟩

/-- One copy transition appends exactly the next original input bit; its
physical choice is ignored and every scheduler/verifier tape stays blank. -/
private lemma b2_copy_step (S V : FinTM Bool) (x : List Bool) (i : ℕ)
    (hi : i < x.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i) =
        b2LoadCfg S V (x := x) 0 ⟨i + 2, by omega⟩ (x.take (i + 1)) (i + 1) := by
  have hr : (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i).inputSymbol =
      some x[i] := inputSymbolInner i (by simp [b2LoadCfg]; omega) hi
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 0) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_pos rfl, hr]
  dsimp only
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · by_cases hj : j.val < S.k
      · simp [b2LoadCfg, b2Slots, hj]
      · simp only [b2LoadCfg, b2Slots, Action.apply, Fin.addCases_left, dif_neg hj]
        rw [List.take_succ_eq_append_getElem hi, bufferTape_append,
          List.length_take_of_le (Nat.le_of_lt hi)]
    · by_cases hj : j.val < V.k <;> simp [b2LoadCfg, b2Slots]
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · by_cases hj : j.val < S.k <;> simp [b2LoadCfg, b2Slots, hj]
    · by_cases hj : j.val < V.k <;> simp [b2LoadCfg, b2Slots]

/-- The original input prefix is copied in exactly one transition per bit,
independently of all physical choices. Induction on the consumed choices
uses the one-step copier and never reads the guessed-data buffer. -/
private lemma b2_copy_run (S V : FinTM Bool) (x w : List Bool)
    (i : ℕ) (hi : i + w.length ≤ x.length) :
    (b2Host S V).tm.runWith w
      (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i) =
        b2LoadCfg S V (x := x) 0 ⟨i + w.length + 1, by omega⟩
          (x.take (i + w.length)) (i + w.length) := by
  induction w generalizing i with
  | nil => simp
  | cons bit w ih =>
    rw [NDTM.runWith_cons, b2_copy_step S V x i (by simp only [List.length_cons] at hi; omega)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
      add_assoc, add_comm, add_left_comm] using
      ih (i + 1) (by simp only [List.length_cons] at hi; omega)

/-- At the left blank, one choice-independent transition starts the scheduler
at head one with blank source tapes and the preserved original input buffer. -/
private lemma b2_rewind_done (S V : FinTM Bool) (x : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2LoadCfg S V (x := x) 1 0 x x.length) =
      b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  have hr : (b2LoadCfg S V (x := x) 1 0 x x.length).inputSymbol = none := by
    simp [b2LoadCfg, Cfg.inputSymbol]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 1) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [b2LoadCfg, b2GuessCfg, leftCfg, contGuessCfg, MultiTapeTM.initCfg,
      Cfg.init, moveInputPos]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, h,
          MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, h,
          MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg]

/-- Each interior rewind transition moves the physical input head left by
one, preserving the copied word and both blank machine banks. -/
private lemma b2_rewind_step (S V : FinTM Bool) (x : List Bool) (j : ℕ)
    (hj : j < x.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 1 ⟨j + 1, by omega⟩ x x.length) =
        b2LoadCfg S V (x := x) 1 ⟨j, by omega⟩ x x.length := by
  have hr : (b2LoadCfg S V (x := x) 1 ⟨j + 1, by omega⟩ x x.length).inputSymbol =
      some x[j] := inputSymbolInner j (by simp [b2LoadCfg]; omega) hj
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 1) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  change (moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = j
  rw [moveInputPos_neg_val]
  simp

/-- The physical rewind reaches the genuine scheduler startup in exactly
`j+1` steps from position `j`. Decreasing-position induction applies to
every choice word, including the empty-input left blank. -/
private lemma b2_rewind_run (S V : FinTM Bool) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (w : List Bool) (hw : w.length = j + 1) :
    (b2Host S V).tm.runWith w
      (b2LoadCfg S V (x := x) 1 ⟨j, by omega⟩ x x.length) =
        b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  induction j generalizing w with
  | zero =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : w = [] := by simpa using hw
      subst w
      exact b2_rewind_done S V x bit
  | succ j ih =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      rw [NDTM.runWith_cons, b2_rewind_step S V x j (by omega)]
      exact ih (by omega) w (by simpa using hw)

/-- The host's blank-tape initial configuration is exactly the empty loader
configuration, rather than an assumed prepared assembly tape. -/
private lemma b2_initial (S V : FinTM Bool) (x : List Bool) :
    (b2Host S V).tm.initCfg x = b2LoadCfg S V (x := x) 0 1 [] 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2LoadCfg, b2Slots]
    · by_cases h : i.val < V.k <;> simp [b2LoadCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2LoadCfg, b2Slots]
    · by_cases h : i.val < V.k <;> simp [b2LoadCfg, b2Slots]

/-- The right input blank triggers a mandatory left move before the rewind
scan, so an empty input is handled without confusing its two boundaries. -/
private lemma b2_copy_done (S V : FinTM Bool) (x : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length) =
        b2LoadCfg S V (x := x) 1 ⟨x.length, by omega⟩ x x.length := by
  have hr : (b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length).inputSymbol =
      none := (inputSymbol_at _ x.length (le_refl _) rfl).trans (by simp)
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 0) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  change (moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = x.length
  rw [moveInputPos_neg_val]
  simp

/-- Startup preserves the original input and installs the normalized scheduler
after exactly `2*|x|+2` physical choices, all ignored.
**Proof sketch.** Split off `|x|` choices for the copier. One blank transition
starts the rewind; the remaining `|x|+1` choices return the input head to one
with blank scheduler/verifier banks and assembly buffer exactly `x`. -/
private lemma b2_start (S V : FinTM Bool) (x w : List Bool)
    (hw : w.length = 2 * x.length + 2) :
    (b2Host S V).tm.runWith w ((b2Host S V).tm.initCfg x) =
      b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  have hp : (w.take x.length).length = x.length := List.length_take_of_le (by omega)
  have hcopy : (b2Host S V).tm.runWith (w.take x.length)
      ((b2Host S V).tm.initCfg x) =
        b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length := by
    rw [b2_initial]
    simpa [hp] using b2_copy_run S V x (w.take x.length) 0 (by omega)
  have hdlen : (w.drop x.length).length = x.length + 2 := by
    rw [List.length_drop, hw]
    omega
  cases hd : w.drop x.length with
  | nil => simp [hd] at hdlen
  | cons bit rest =>
    have hrest : rest.length = x.length + 1 := by simpa [hd] using hdlen
    have hsplit : w = w.take x.length ++ bit :: rest := by
      rw [← hd, List.take_append_drop]
    rw [hsplit, NDTM.runWith_append, hcopy, NDTM.runWith_cons, b2_copy_done]
    exact b2_rewind_run S V x x.length (le_refl _) rest hrest

/-- A captured guessing word is determined by its tape contents. This reads
every nonnegative tape cell, so it also covers the zero-length word. -/
private lemma b2_guess_word_injective (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) {u v : List Bool}
    (h : contGuessCfg M c u = contGuessCfg M c v) : u = v := by
  apply List.ext_getElem?
  intro i
  have he := congrArg (fun g => g.workTapes (Fin.last M.k) (i : ℤ)) h
  simpa [contGuessCfg] using he

/-- Reuse the predecessor's native coverage at the actual first scheduler
halt, and transfer its full-word extraction/coverage into the host. The
assembly buffer has original prefix `x` and exactly the extracted suffix.
**Proof sketch.** Standalone coverage supplies the guessed word. Equality of
its capture tape identifies that word with physical-mask selection; the
guarded host run then gives the same selection after the preserved prefix. -/
private lemma b2_guess_coverage (S V : FinTM Bool) (x v : List Bool) (T : ℕ)
    (hS : (b2UnaryTM S).ComputesInTime x v T)
    (hlive : ∀ s < T, ((b2UnaryTM S).tm.runFrom
      ((b2UnaryTM S).tm.initCfg x) s).state ≠ none) :
    (∀ w : List Bool, w.length = T → ∃ u : List Bool, u.length = v.length ∧
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = T ∧
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) := by
  have hcov := cont_guess_coverage (b2UnaryTM S) x v T hS
  have htransfer (w u : List Bool) (hw : w.length = T)
      (hr : (contGuessTM (b2UnaryTM S)).tm.runWith w
        ((contGuessTM (b2UnaryTM S)).tm.initCfg x) =
          contGuessCfg (b2UnaryTM S) ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) :
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u := by
    rw [cont_guess_initial, cont_guess_run, hw, List.nil_append] at hr
    have hu := b2_guess_word_injective _ _ hr
    rw [b2_guess_run S V _ [] w (by simpa [hw] using hlive), hw, List.nil_append, hu]
  constructor
  · intro w hw
    obtain ⟨u, hu, hr⟩ := hcov.1 w hw
    exact ⟨u, hu, htransfer w u hw hr⟩
  · intro u hu
    obtain ⟨w, hw, hr⟩ := hcov.2 u hu
    exact ⟨w, hw, htransfer w u hw hr⟩

/-- Verifier invariant: its input is the assembly buffer with a guarded
virtual head, its own source tapes are exact, all emitted bits are captured,
and the scheduler's bank remains unchanged. Physical output is still empty. -/
private def b2VerifyCfg (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin S.k → ℤ → Option Bool) (heads : Fin S.k → ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inr (.inr (c.state, tag, capturedSummary c.output))), p,
    b2Slots S V tapes (bufferTape y) c.workTapes (bufferTape c.output),
    b2Slots S V heads ((c.inputPos.val : ℤ) - 1) c.workTapePos c.output.length, []⟩

/-- The assembled-input rewind retains the completed scheduler bank and
the blank verifier bank. Its assembly head is explicitly recorded. -/
private def b2ReadyCfg (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inl 2), c.inputPos,
    b2Slots S V c.workTapes (bufferTape y) (fun _ _ => none) (fun _ => none),
    b2Slots S V c.workTapePos j (fun _ => 0) 0, []⟩

/-- A live verifier step reads the exact assembly input, clamps both virtual
boundaries correctly, and captures even an emission on a halting transition.
Its physical choice is ignored.
**Proof sketch.** The assembly-buffer read is the source input read. The
library virtual-head identity supplies the new head and boundary tag. Check
the scheduler/assembly and verifier/capture banks separately; the capture
append identity and finite-summary update retain the whole emitted word. -/
private lemma b2_verify_step (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (hc : c.state ≠ none)
    (tag : Bool) (htag : VirtualTag c.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin S.k → ℤ → Option Bool) (heads : Fin S.k → ℤ) (bit : Bool) :
    ∃ tag', VirtualTag (V.tm.step c).inputPos tag' ∧
      (b2Host S V).tm.stepWith bit (b2VerifyCfg S V c tag p tapes heads) =
        b2VerifyCfg S V (V.tm.step c) tag' p tapes heads := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    let a := V.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove tag c.inputSymbol a.inputTape
    have hm := virtualMove_correct c tag htag a.inputTape
    have hstep : V.tm.step c = a.apply c := by simp [MultiTapeTM.step, hs, a]
    have hi : (b2VerifyCfg S V c tag p tapes heads).workTapeSymbols
        (Fin.castAdd (V.k + 1) (Fin.last S.k)) = c.inputSymbol := by
      simp [b2VerifyCfg, b2Slots, Cfg.workTapeSymbols, bufferTape_inputSymbol]
    have hw : (fun i : Fin V.k => (b2VerifyCfg S V c tag p tapes heads).workTapeSymbols
        (Fin.natAdd (S.k + 1) i.castSucc)) = c.workTapeSymbols := by
      funext i
      simp [b2VerifyCfg, b2Slots, Cfg.workTapeSymbols, i.isLt]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hstep, Action.apply] using hm.2
    · rw [hstep]
      unfold NDTM.stepWith
      change ((b2Host S V).tm.tr bit
        (.inr (.inr (c.state, tag, capturedSummary c.output))) _ _).apply _ = _
      rw [hs]
      dsimp only [b2Host]
      rw [hi, hw]
      change (Action.mk 0 (b2Slots S V (fun _ => (none, 0)) (none, m) a.workTapes
        (a.output.map some, if a.output.isSome then 1 else 0)) none
        (some (.inr (.inr (a.state, virtualNextTag tag m,
          captureEmission (capturedSummary c.output) a.output))))).apply
            (b2VerifyCfg S V c tag p tapes heads) = _
      refine Cfg.ext (by simp [b2VerifyCfg, captureEmission_correct])
        (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro i
        · by_cases h : i.val < S.k <;> simp [b2VerifyCfg, b2Slots, h]
        · by_cases h : i.val < V.k
          · simp [b2VerifyCfg, b2Slots, h]
          · cases he : a.output <;> simp [b2VerifyCfg, b2Slots, h, he, bufferTape_append]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro i
        · by_cases h : i.val < S.k
          · simp [b2VerifyCfg, b2Slots, h]
          · simpa [b2VerifyCfg, b2Slots, h, m] using hm.1
        · by_cases h : i.val < V.k
          · simp [b2VerifyCfg, b2Slots, h]
          · cases he : a.output <;> simp [b2VerifyCfg, b2Slots, h, he]

/-- Every physical choice word simulates the same verifier until its first
halt, with exact output capture and a valid boundary tag. Induction applies
the choice-independent one-step invariant and shifts the liveness guard. -/
private lemma b2_verify_run (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (tag : Bool) (htag : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (w : List Bool)
    (hlive : ∀ s < w.length, (V.tm.runFrom c s).state ≠ none) :
    ∃ tag', VirtualTag (V.tm.runFrom c w.length).inputPos tag' ∧
      (b2Host S V).tm.runWith w (b2VerifyCfg S V c tag p tapes heads) =
        b2VerifyCfg S V (V.tm.runFrom c w.length) tag' p tapes heads := by
  induction w generalizing c tag with
  | nil => exact ⟨tag, htag, rfl⟩
  | cons bit w ih =>
    obtain ⟨tag', htag', hs⟩ := b2_verify_step S V c (hlive 0 (by simp))
      tag htag p tapes heads bit
    have ht : ∀ s < w.length, (V.tm.runFrom (V.tm.step c) s).state ≠ none := by
      intro s hs
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hlive (s + 1) (by simpa using hs)
    obtain ⟨tag'', htag'', hr⟩ := ih (V.tm.step c) tag' htag' ht
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step] using htag''
    · rw [NDTM.runWith_cons, hs, hr]
      simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]

/-- After the verifier halts, one physical transition emits exactly one
verdict bit and halts the host. Acceptance tests the entire captured word. -/
private lemma b2_verify_finish (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (hc : c.state = none) (tag : Bool)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (bit : Bool) :
    let out := (b2Host S V).tm.stepWith bit (b2VerifyCfg S V c tag p tapes heads)
    out.state = none ∧ out.output = [decide (c.output = [true])] := by
  simp [NDTM.stepWith, b2Host, b2VerifyCfg, hc, capturedSummary_true]

/-- The actual scheduler-return state dispatches to assembly rewind. This
transition is available only after the represented scheduler has halted. -/
private lemma b2_guess_return (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2GuessCfg S V c u) =
      b2ReadyCfg S V c (x ++ u) ((x ++ u).length - 1 : ℤ) := by
  have hs : (b2GuessCfg S V c u).state = some (.inr (.inl none)) := by
    simp [b2GuessCfg, leftCfg, contGuessCfg, hc]
  unfold NDTM.stepWith
  rw [hs]
  dsimp only [b2Host]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, b2ReadyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;>
        simp [b2GuessCfg, leftCfg, b2ReadyCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, b2ReadyCfg, b2Slots, h,
          sub_eq_add_neg]
    · by_cases h : i.val < V.k <;>
        simp [b2GuessCfg, leftCfg, b2ReadyCfg, b2Slots]

/-- The assembly rewind moves left across a populated cell while retaining
the entire assembled word and the completed scheduler configuration. -/
private lemma b2_ready_step (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℕ)
    (hj : j < y.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2ReadyCfg S V c y j) =
      b2ReadyCfg S V c y ((j : ℤ) - 1) := by
  have hr : (b2ReadyCfg S V c y j).workTapeSymbols
      (Fin.castAdd (V.k + 1) (Fin.last S.k)) = some y[j] := by
    simp [b2ReadyCfg, b2Slots, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 2) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1), hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;> simp [b2ReadyCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2Slots, h, sub_eq_add_neg]
    · by_cases h : i.val < V.k <;> simp [b2ReadyCfg, b2Slots]

/-- The assembly's left blank starts the verifier at its genuine initial
configuration: virtual head one, blank source tapes, and empty captured output.
This applies equally to an empty assembled input. -/
private lemma b2_ready_done (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2ReadyCfg S V c y (-1)) =
      b2VerifyCfg S V (V.tm.initCfg y) true c.inputPos c.workTapes c.workTapePos := by
  have hr : (b2ReadyCfg S V c y (-1)).workTapeSymbols
      (Fin.castAdd (V.k + 1) (Fin.last S.k)) = none := by
    simp [b2ReadyCfg, b2Slots, Cfg.workTapeSymbols]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 2) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1), hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2VerifyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, h, MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, MultiTapeTM.initCfg, Cfg.init]

/-- Assembly rewind takes exactly `j+1` transitions from head `j-1`, with
every physical choice ignored. Decreasing-head induction ends with the
proper verifier startup, including the empty-buffer case. -/
private lemma b2_ready_run (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℕ) (hj : j ≤ y.length)
    (w : List Bool) (hw : w.length = j + 1) :
    (b2Host S V).tm.runWith w (b2ReadyCfg S V c y ((j : ℤ) - 1)) =
      b2VerifyCfg S V (V.tm.initCfg y) true c.inputPos c.workTapes c.workTapePos := by
  induction j generalizing w with
  | zero =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : w = [] := by simpa using hw
      subst w
      simpa using b2_ready_done S V c y bit
  | succ j ih =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : ((j + 1 : ℕ) : ℤ) - 1 = j := by omega
      rw [NDTM.runWith_cons, he, b2_ready_step S V c y j (by omega)]
      exact ih (by omega) w (by simpa using hw)

/-- From an actual scheduler halt, `|x++u|+2` transitions install the
relocated verifier. The guessed suffix is already appended to the preserved
prefix, so assembly needs only a rewind and dispatch. -/
private lemma b2_assembly (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u w : List Bool)
    (hw : w.length = (x ++ u).length + 2) :
    (b2Host S V).tm.runWith w (b2GuessCfg S V c u) =
      b2VerifyCfg S V (V.tm.initCfg (x ++ u)) true c.inputPos c.workTapes c.workTapePos := by
  cases w with
  | nil => simp at hw
  | cons bit w =>
    rw [NDTM.runWith_cons, b2_guess_return S V c hc]
    exact b2_ready_run S V c (x ++ u) (x ++ u).length (le_refl _) w (by simpa using hw)

/-- Every branch of the verifier phase halts with its single verdict within
the source budget plus one. Actual first halts may depend on the assembled
certificate; the declared upper bound is common.
**Proof sketch.** Take the source's first halt, simulate the corresponding
choice prefix, and execute one verdict transition. All remaining choices
are absorbed by the halted host. Output uniqueness identifies the completed
source output with its specified singleton. -/
private lemma b2_verify_timed (S V : FinTM Bool) {x : List Bool}
    (y : List Bool) (b : Bool) (T : ℕ) (hV : V.ComputesInTime y [b] T)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (w : List Bool) (hw : w.length = T + 1) :
    let out := (b2Host S V).tm.runWith w
      (b2VerifyCfg S V (V.tm.initCfg y) true p tapes heads)
    out.state = none ∧ out.output = [b] := by
  classical
  have hex : ∃ t, (V.tm.runFrom (V.tm.initCfg y) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hV).1⟩
  let t := Nat.find hex
  let c := V.tm.runFrom (V.tm.initCfg y) t
  have ht : t ≤ T := Nat.find_min' hex ((computesInTime_iff _ _ _ _).mp hV).1
  have hc : c.state = none := Nat.find_spec hex
  have hcomp : V.ComputesInTime y c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hc, rfl⟩
  have ho : c.output = [b] := hcomp.output_unique hV
  have hp : (w.take t).length = t := List.length_take_of_le (by omega)
  obtain ⟨tag, _, hr⟩ := b2_verify_run S V (V.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (w.take t)
    (fun s hs => Nat.find_min hex (show s < t from hp ▸ hs))
  rw [hp] at hr
  have hlen : 0 < (w.drop t).length := by rw [List.length_drop]; omega
  cases hd : w.drop t with
  | nil => simp [hd] at hlen
  | cons bit rest =>
    have hf := b2_verify_finish S V c hc tag p tapes heads bit
    have hout : ((b2Host S V).tm.stepWith bit
        (b2VerifyCfg S V c tag p tapes heads)).output = [b] := by
      rw [hf.2, ho]
      cases b <;> simp
    have hsplit : w = w.take t ++ bit :: rest := by rw [← hd, List.take_append_drop]
    dsimp only
    rw [hsplit, NDTM.runWith_append, hr, NDTM.runWith_cons,
      NDTM.runWith_of_halt _ hf.1]
    exact ⟨hf.1, hout⟩

/-- Assembly and verification terminate on every suffix choice word at a
common bound and emit the verifier's single decision bit.
**Proof sketch.** Split the physical word at the exact assembly-rewind
length; the rest has the verifier budget plus its verdict transition. Apply
the two timed phase contracts in order. -/
private lemma b2_finish (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u : List Bool)
    (b : Bool) (T : ℕ) (hV : V.ComputesInTime (x ++ u) [b] T)
    (w : List Bool) (hw : w.length = (x ++ u).length + 2 + (T + 1)) :
    let out := (b2Host S V).tm.runWith w (b2GuessCfg S V c u)
    out.state = none ∧ out.output = [b] := by
  let a := (x ++ u).length + 2
  have hp : (w.take a).length = a := List.length_take_of_le (by dsimp [a]; omega)
  have ht : (w.drop a).length = T + 1 := by rw [List.length_drop, hw]; dsimp [a]; omega
  have hr := b2_assembly S V c hc u (w.take a) hp
  have hf := b2_verify_timed S V (x ++ u) b T hV c.inputPos c.workTapes
    c.workTapePos (w.drop a) ht
  dsimp only at hf ⊢
  rw [← hr, ← NDTM.runWith_append, List.take_append_drop] at hf
  exact hf

/-- The integrated host has both branch extraction and witness coverage at
one common budget. Guess positions are offset by the exact startup length;
administrative choices may all be false. Every branch, accepted or rejected,
halts with the verifier's single bit for an exact-length certificate.
**Proof sketch.** Split each full choice word into startup, the actual
scheduler interval, and a completion suffix. Native coverage gives the
unique scheduled certificate length. Startup, guessing, and completion run
contracts compose at their actual configurations. Conversely, choose any
covered guessing word and surround it by arbitrary administrative choices. -/
private lemma b2_host_contract (S M : FinTM Bool) (V : Language Bool)
    (x v : List Bool) (T A d : ℕ)
    (hS : (b2UnaryTM S).ComputesInTime x v T)
    (hlive : ∀ s < T, ((b2UnaryTM S).tm.runFrom
      ((b2UnaryTM S).tm.initCfg x) s).state ≠ none)
    (hM : M.DecidesInTime V (fun n => A * (n + 1) ^ d)) :
    let H := 2 * x.length + 2 + T +
      (x.length + v.length + 2 + (A * (x.length + v.length + 1) ^ d + 1))
    (∀ w : List Bool, w.length = H → ∃ u : List Bool, u.length = v.length ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)]) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = H ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)]) := by
  let c := (b2UnaryTM S).tm.runFrom ((b2UnaryTM S).tm.initCfg x) T
  have hc : c.state = none := ((computesInTime_iff _ _ _ _).mp hS).1
  let B := x.length + v.length + 2 + (A * (x.length + v.length + 1) ^ d + 1)
  have hcov := b2_guess_coverage S M x v T hS hlive
  have hpieces (a g z u : List Bool) (ha : a.length = 2 * x.length + 2)
      (hu : u.length = v.length) (hz : z.length = B)
      (hg : (b2Host S M).tm.runWith g
        (b2GuessCfg S M ((b2UnaryTM S).tm.initCfg x) []) = b2GuessCfg S M c u) :
      ((b2Host S M).tm.runWith (a ++ g ++ z) ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith (a ++ g ++ z) ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)] := by
    rw [NDTM.runWith_append, NDTM.runWith_append, b2_start S M x a ha, hg]
    exact b2_finish S M c hc u (MultiTapeTM.indicator V (x ++ u))
      (A * ((x ++ u).length + 1) ^ d) (hM (x ++ u)) z
      (by simpa only [List.length_append, hu] using hz)
  dsimp only
  constructor
  · intro w hw
    let a := w.take (2 * x.length + 2)
    let rest := w.drop (2 * x.length + 2)
    let g := rest.take T
    let z := rest.drop T
    have ha : a.length = 2 * x.length + 2 := List.length_take_of_le (by omega)
    have hr : rest.length = T + B := by dsimp [rest, B]; rw [List.length_drop, hw]; omega
    have hglen : g.length = T := List.length_take_of_le (by omega)
    have hz : z.length = B := by dsimp [z]; rw [List.length_drop, hr]; omega
    have he : a ++ g ++ z = w := by
      dsimp [a, g, z, rest]
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨u, hu, hg⟩ := hcov.1 g hglen
    exact ⟨u, hu, he ▸ hpieces a g z u ha hu hz hg⟩
  · intro u hu
    obtain ⟨g, hglen, hg⟩ := hcov.2 u hu
    let a := List.replicate (2 * x.length + 2) false
    let z := List.replicate B false
    refine ⟨a ++ g ++ z, ?_, hpieces a g z u (by simp [a]) hu (by simp [z]) hg⟩
    simp only [List.length_append, List.length_replicate, a, z, hglen, B]

/-- The complete native ledger fits the required polynomial envelope, even
at zero coefficient/degree and empty input. Startup and assembly contribute
`3n+Q(n)+5`; scheduler and verifier contribute their actual proved budgets.
**Proof sketch.** Set the envelope degree to `c+d+1`. Its base dominates
`n+1`, and its degree dominates both `c+1` and `d`, as well as one. Bound the
linear overhead by five times the base, then add all three coefficients. -/
private lemma b2_host_bound (C c B A d n T : ℕ)
    (hT : T ≤ B * (n + 1) ^ (c + 1)) :
    2 * n + 2 + T + (n + C * (n + 1) ^ c + 2 +
      (A * (n + C * (n + 1) ^ c + 1) ^ d + 1)) ≤
      (B + A + 5) * (n + C * (n + 1) ^ c + 1) ^ (c + d + 1) := by
  let m := n + C * (n + 1) ^ c + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hs : T ≤ B * m ^ (c + d + 1) := hT.trans
    (Nat.mul_le_mul_left B ((Nat.pow_le_pow_left (by dsimp [m]; omega) (c + 1)).trans
      (Nat.pow_le_pow_right hm (by omega : c + 1 ≤ c + d + 1))))
  have hv : A * m ^ d ≤ A * m ^ (c + d + 1) :=
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right hm (by omega))
  have hl : 3 * n + C * (n + 1) ^ c + 5 ≤ 5 * m ^ (c + d + 1) := by
    have hp : m ≤ m ^ (c + d + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hm (by omega : 1 ≤ c + d + 1)
    exact (show 3 * n + C * (n + 1) ^ c + 5 ≤ 5 * m by dsimp [m]; omega).trans
      (Nat.mul_le_mul_left 5 hp)
  change 2 * n + 2 + T + (n + C * (n + 1) ^ c + 2 + (A * m ^ d + 1)) ≤ _
  calc
    _ ≤ B * m ^ (c + d + 1) + A * m ^ (c + d + 1) + 5 * m ^ (c + d + 1) := by omega
    _ = _ := by dsimp [m]; ring

/-- The integrated reverse compiler decides the certificate language on all
branches within the required envelope.
**Proof sketch.** Instantiate the unary polynomial scheduler and use its
length-indexed first halt. The host contract gives all-branch termination,
exact-length extraction, and coverage at the complete phase ledger. The
certificate characterization turns its verifier outputs into language
acceptance. Enlarge to the common polynomial envelope using halting
absorption in both directions, including nonaccepting branches. -/
private lemma b2_compile (L : Language Bool) (C c : ℕ) (V : Language Bool)
    (hcert : ∀ x, x ∈ L ↔ ∃ u : List Bool,
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V)
    (M : FinTM Bool) (A d : ℕ)
    (hM : M.DecidesInTime V (fun n => A * (n + 1) ^ d)) :
    ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * (n + 1) ^ c + 1) ^ r) := by
  classical
  obtain ⟨S, B, hS⟩ := computesFunInTime_polyUnary C c
  obtain ⟨τ, hτ⟩ := b2_unary_first S (fun n => List.replicate (C * (n + 1) ^ c) true)
    (fun n => B * (n + 1) ^ (c + 1)) (fun n => by
      simpa only [List.length_replicate] using hS (List.replicate n true))
  refine ⟨B + A + 5, c + d + 1, b2Host S M, fun x => ?_⟩
  let H := 2 * x.length + 2 + τ x.length + (x.length + C * (x.length + 1) ^ c + 2 +
    (A * (x.length + C * (x.length + 1) ^ c + 1) ^ d + 1))
  have hc := b2_host_contract S M V x (List.replicate (C * (x.length + 1) ^ c) true)
    (τ x.length) A d (hτ x).2.1 (hτ x).2.2 hM
  simp only [List.length_replicate] at hc
  have hhalt : (b2Host S M).tm.HaltsWithin x H := by
    intro w hw
    obtain ⟨u, _, hh, _⟩ := hc.1 w hw
    exact hh
  have hacc : x ∈ L ↔ (b2Host S M).AcceptsWithin x H := by
    rw [hcert x]
    constructor
    · rintro ⟨u, hu, hv⟩
      obtain ⟨w, hw, hh, ho⟩ := hc.2 u hu
      refine ⟨w, hw, hh, ?_⟩
      rw [ho]
      simp [MultiTapeTM.indicator, hv]
    · rintro ⟨w, hw, _, ho⟩
      obtain ⟨u, hu, _, hout⟩ := hc.1 w hw
      refine ⟨u, hu, ?_⟩
      have he := hout.symm.trans ho
      by_contra hv
      simp [MultiTapeTM.indicator, hv] at he
  have ht := b2_host_bound C c B A d x.length (τ x.length) (hτ x).1
  exact ⟨hhalt.mono ht, hacc.trans (acceptsWithin_iff_of_halts hhalt ht).symm⟩

/-- **Guess the certificate** [AB09, Theorem 2.6, ⊇-direction of the union]: `NP` is
contained in the union of the fixed-degree nondeterministic time classes.

**Proof sketch.** Let `L ∈ NP` with parameters `(C, c, V)` and, via
`Complexity.mem_P_iff`, a machine `M_V` deciding `V` within `A·(m+1)^d`. The NDTM, on
input `x` of length `n`: (i) evaluate `Q n = C·(n+1)^c` in binary (the shared
polynomial-evaluation obligation) and initialize a countdown; (ii) **guessing phase**
— write exactly `Q n` guessed bits onto a guess tape, `δ₀` writing `false` and `δ₁`
writing `true` on each nondeterministic write step ([AB09]'s concrete recipe, p. 42),
interleaved with deterministic countdown bookkeeping (the phase boundaries are
identical across branches: only the guessed content diverges, never the timing); (iii) assemble `x ++ u` on an assembly tape (copy the
input, append the guess tape); (iv) run `M_V` **with its input relocated to the
assembly tape** — the input-relocation obligation: the fixed machine `M_V`'s
input-tape reads are served from a work tape through a binary head-position counter
with the window guard, symmetric to the simulation obligation of
`Complexity.ntime_poly_subset_NP`; (v) capture `M_V`'s output in a buffer (isolation,
as always) and emit the verdict: `[true]` if the buffer is exactly `[true]`, else
`[false]`, then halt. Outside the guessing phase the two transition functions
coincide, so every choice word drives the same phases and every branch halts within
the deterministic budget — `HaltsWithin` holds on all inputs. Acceptance: branches of
the guessing phase realize exactly the strings `u` with `|u| = Q n`, and the verdict
is `[true]` precisely when `x ++ u ∈ V` (`M_V` decides `V`), so some branch accepts
iff `x ∈ L`; non-members' branches all emit `[false] ≠ [true]`. Padding accepting
branches to the exact budget is `Turing.FinNDTM.AcceptsWithin.mono`. Total time is
polynomial in `n` — guessing `Q n` steps with `O(log Q n)`-bit countdowns, assembly
`O(n + Q n)`, and the relocated `M_V` run `A·(n + Q n + 1)^d` with polynomial
per-step bookkeeping — hence at most `a'·(n^e + 1)` for a fixed degree `e` (normalize
with `Complexity.succ_pow_le`), landing `L` in the degree-`e` component.

**Continuation checkpoint (E2-cont-B, incomplete).** `contGuessTM` and
`cont_guess_run` provide a native, silent emission-driven guessing phase;
`cont_guess_coverage` proves extraction and coverage at actual physical
write positions. `cont_poly_guess_phase` instantiates the audited unary
polynomial generator on the unary input of length `n`, giving a schedule
determined by `n` and covering zero coefficients. This standalone phase has
a live return state, not a completed decider. Preserving the original input,
installing the scheduler/countdown in a host, assembling `x++u`, and the
captured verifier phase with all-branch totality remain open. The exact
remaining machine-existence goal is exposed below; `cont_guess_normalize`
proves all final exponent/coefficient arithmetic and budget padding once that
machine contract is supplied.

**B2 completion.** The reverse host is now complete. `b2UnaryTM` normalizes
only input reads; `b2_unary_run` and `b2_unary_first` prove exact unary
lockstep and length-only first halts. Startup copies `x` before guessing;
`b2_guess_coverage` lifts the banked phase at its actual completion, and
`b2_host_contract` accounts for the startup offset in full branch words.
Guesses append directly after `x`; `b2_assembly` installs the relocated
verifier with blank tapes, and `b2_verify_timed` captures all output before
emitting one verdict. `b2_tables_coincide` is by construction. `b2_compile`
proves all-branch totality and acceptance at a common envelope with coefficient
`B+A+5` and degree `c+d+1`, then the banked normalization closes the target.
The emission scheduler implements the exact guess count; no upper bound is
used as a native clock and no untimed composition is used. -/
theorem NP_subset_iUnion_NTIME : NP ⊆ ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  rintro L ⟨C, c, V, hV, hcert⟩
  obtain ⟨A, d, M, hM⟩ := mem_P_iff.mp hV
  apply cont_guess_normalize L C c
  exact b2_compile L C c V hcert M A d hM

/-- **Theorem 2.6** [AB09]: `NP = ⋃ c, NTIME (n^c + 1)` — the verifier-certificate
definition and the nondeterministic-machine definition of `NP` coincide (with the
`+ 1` padding of the union recorded in the deviations list).

**Proof sketch.** Antisymmetry: `Complexity.NP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_poly_subset_NP` at every degree the
other. -/
theorem NP_eq_iUnion_NTIME : NP = ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  exact Set.Subset.antisymm NP_subset_iUnion_NTIME
    (Set.iUnion_subset fun c => ntime_poly_subset_NP c)

/-- **Exponential choice words are exponential certificates**: every fixed-exponent
`NTIME (2^(n^c))` class is contained in the certificate-form `Complexity.NEXP`.

**Proof sketch.** The exponential analogue of `Complexity.ntime_poly_subset_NP`, same
verifier machine, different arithmetic. Let `N` decide `L` within `T n = a·2^(n^c)`
(if `a = 0` the budget is `0` and no decider exists — `Turing.NDTM.HaltsWithin` fails
on the empty choice word — so the case is vacuous). Certificate parameters: `C = a`,
degree `c`, length `Q n = a·2^((n+1)^c) ≥ T n`. The verifier language is the same
accepting-run language over the split `y = x ++ u`; `n ↦ n + Q n` is strictly
increasing (in `n` alone already), the split search over `n ≤ m` writes each candidate
`Q n` in binary — `(n+1)^c + O(log a)` bits, polynomial in `m` (the check recorded in
the `Complexity.EXP_subset_NEXP` sketch) — and **rejects explicitly when no solution
exists**. The simulation runs `|u| = Q n ≤ m` steps of the fixed machine `N` at
polynomial bookkeeping per step — polynomial in `m`, which is the whole point of
exponential padding: `V ∈ P`. Forward/backward certificate correspondence is verbatim
the polynomial case (pad with `false`-bits; truncate to the length-`T n` prefix and
absorb). -/
theorem ntime_expPow_subset_NEXP (c : ℕ) : NTIME (fun n => 2 ^ n ^ c) ⊆ NEXP := by
  sorry

/-- **Guess the exponential certificate**: the certificate-form `Complexity.NEXP` is
contained in the union of the fixed-exponent `NTIME (2^(n^c))` classes.

**Proof sketch.** The exponential analogue of `Complexity.NP_subset_iUnion_NTIME`.
Given `(C, c, V)` for `L` with `E n = C·2^((n+1)^c)` and `M_V` deciding `V` within
`A·(m+1)^d`: evaluate `E n` in binary (`(n+1)^c + O(log C)` bits; writing `2^((n+1)^c)`
is a `1` followed by `(n+1)^c` zeros, produced by a counter in time polynomial in
`(n+1)^c`); guess exactly `E n` bits (`δ₀`/`δ₁` write `false`/`true` on each
nondeterministic write step, deterministic countdown bookkeeping interleaved, phase
boundaries identical across branches); assemble
`x ++ u`; run the relocated, captured `M_V`; emit the verdict. Every branch is total
and the phases cost `O(E n)` guessing steps at `O((n+1)^c)`-bit countdown decrements,
plus `A·(n + E n + 1)^d` relocated verifier steps with polynomial bookkeeping — in all
at most `2^(n^e)` for a fixed `e` (say `e = c + d + 2`) once `n` exceeds a fixed
threshold, with the finitely many inputs of smaller lengths absorbed into `NTIME`'s
constant (their maximal halting time is a number; the truncation argument of
`Complexity.NTIME.mono` keeps the acceptance equivalence at the padded budget). Land
`L` in the exponent-`e` component. -/
theorem NEXP_subset_iUnion_NTIME : NEXP ⊆ ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

/-- **The `NTIME` form of `NEXP`** [AB09, §2.6.2 reconciled with Exercise 2.27]:
`NEXP = ⋃ c, NTIME (2^(n^c))`. [AB09] *defines* `NEXP` by the right-hand side;
`Complexity.NEXP` is Exercise 2.27's certificate form, and this equality discharges
the reconciliation obligation recorded at its definition.

**Proof sketch.** Antisymmetry: `Complexity.NEXP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_expPow_subset_NEXP` at every exponent the
other. -/
theorem NEXP_eq_iUnion_NTIME : NEXP = ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

/-- **Padding scales collapses up** [AB09, Theorem 2.22, contrapositive form]: if
`P = NP` then `EXP = NEXP`.

**Proof sketch.** `EXP ⊆ NEXP` is `Complexity.EXP_subset_NEXP`. Conversely let
`L ∈ NEXP` with `(C, c, V)` and `E n = C·2^((n+1)^c)`; the padded language is
`L_pad = {Turing.pairEncode x (List.replicate (E |x|) true) : x ∈ L}`
([AB09]'s `⟨x, 1^(2^(|x|^c))⟩`, rendered with the audited self-delimiting pairing;
`|Turing.pairEncode x pad| = 2|x| + 2 + E |x|`). **`L_pad ∈ NP`**, through the (⇐)
direction of the bounded paired interface `Complexity.mem_NP_iff_exists_length_le` —
this is the route of [AB09, Exercise 2.27], no nondeterministic machines: parameters
`C' = 1`, `c' = 1` (the `NEXP` certificate `u` of `x` has `|u| = E |x| ≤ |x'|` for the
padded input `x'`), and verifier
`V' = {Turing.pairEncode x' u : x' = Turing.pairEncode x (List.replicate (E |x|) true)
for some x, |u| = E |x|, and x ++ u ∈ V}`. Deciding `V'` in time polynomial in
`|x'| + |u|`: parse the outer pair (`Turing.pairDecode` — self-delimiting, outermost
first; a parsing-machine obligation), parse `x'` into `(x, pad)`, evaluate `E |x|` in
binary — **before any validity assumption** its bit length is at most
`(|x|+1)^c + bits(C) + 1`, polynomial in the actual input length since the parsed
`x` is a substring of the input (`E n = 0` when `C = 0`); the logarithmic-in-`|x'|`
estimate holds only *after* the padding-length check and must not be used to budget
the evaluation itself (round-1 audit, finding 1) — check `pad` is all-`true` of
exactly that length and `|u|` equals it exactly (rejecting otherwise — malformed
`x'` lies in neither `L_pad` nor any `V'`-pair, keeping the equivalence for all
inputs; both exact checks are needed, the bounded outer witness condition replaces
neither), assemble `x ++ u` (length
`≤ |x'|`), and run `V`'s polynomial decider relocated-and-captured (the shared
obligations). By `P = NP`, `L_pad ∈ P`; let `M_pad` decide it within `A·(m+1)^d`.
**`L ∈ EXP`**: on `x`, evaluate `E |x|` and write the pad (`E |x|` symbols —
exponential time, which `EXP` affords), assemble `y = Turing.pairEncode x pad` by an
emission machine, run the relocated, captured `M_pad` on `y`, and forward the verdict.
Total time is polynomial in `|y| = 2|x| + 2 + E |x|`, hence at most `2^(n^e)` for a
fixed `e` beyond a fixed threshold, small lengths absorbed into `DTIME`'s constant:
`L ∈ EXP`. -/
theorem EXP_eq_NEXP_of_P_eq_NP (h : P = NP) : EXP = NEXP := by
  sorry

/-- **Theorem 2.22** [AB09]: if `EXP ≠ NEXP` then `P ≠ NP`.

**Proof sketch.** Contraposition of `Complexity.EXP_eq_NEXP_of_P_eq_NP`. -/
theorem P_ne_NP_of_EXP_ne_NEXP (h : EXP ≠ NEXP) : P ≠ NP := by
  sorry

end Complexity

## ===== TCSlib/Complexity/ClassNP/NP.lean =====

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

## ===== TCSlib/Complexity/ClassNP/Reductions.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karp reductions, NP-hardness, and NP-completeness

[AB09, §2.2, Definition 2.7]: `L ≤ₚ L'` when a polynomial-time computable
function maps members to members and non-members to non-members; `L'` is
`NP`-hard when every `NP` language reduces to it, `NP`-complete when it is also
in `NP`. Theorem 2.8 packages the basic laws: transitivity, and the collapse
consequences of an `NP`-hard language landing in `P`.

The module closes with [AB09, Exercise 2.8], the chapter's bridge back to
Chapter 1: `HALT` is `NP`-hard but — being undecidable — not in `NP`, hence not
`NP`-complete.

## Main definitions

* `Complexity.PolyTimeReducible` (scoped notation `≤ₚ`) — [AB09, Definition 2.7].
* `Complexity.NPHard`, `Complexity.NPComplete` — [AB09, Definition 2.7].

## Main results

* `Complexity.PolyTimeReducible.refl`, `Complexity.PolyTimeReducible.trans` —
  [AB09, Theorem 2.8.1 and Exercise 2.9].
* `Complexity.mem_P_of_polyTimeReducible` — downward closure of `P` under `≤ₚ`
  [AB09, Figure 2.1].
* `Complexity.P_eq_NP_of_NPHard_mem_P` — [AB09, Theorem 2.8.2].
* `Complexity.NPComplete.mem_P_iff` — [AB09, Theorem 2.8.3].
* `Complexity.HALT_NPHard`, `Complexity.HALT_not_mem_NP` — [AB09, Exercise 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7, Theorem 2.8,
  pp. 42-44; Exercises 2.8-2.9.)
-/

namespace Complexity

open Turing

/-- **Polynomial-time Karp reducibility** [AB09, Definition 2.7]: `L ≤ₚ L'` when
some polynomial-time computable `f` satisfies `x ∈ L ↔ f x ∈ L'` for every
string `x`. -/
def PolyTimeReducible (L L' : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyTimeReducible

/-- Karp reducibility is reflexive [AB09, Exercise 2.9]: the identity reduces
`L` to itself.

**Proof sketch.** `Complexity.polyTimeComputable_id` with the trivial membership
equivalence. -/
theorem PolyTimeReducible.refl (L : Language Bool) : L ≤ₚ L := by
  exact ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- **Karp reducibility is transitive** [AB09, Theorem 2.8.1].

**Proof sketch.** Compose the two reduction functions with
`Complexity.PolyTimeComputable.comp` and chain the membership equivalences —
the polynomial-composition observation of [AB09]'s proof lives inside `comp`. -/
theorem PolyTimeReducible.trans {L L' L'' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ≤ₚ L'') : L ≤ₚ L'' := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨g, hg, hL'⟩ := h'
  exact ⟨g ∘ f, hg.comp hf, fun x => (hL x).trans (hL' (f x))⟩

/-- **`P` is closed downward under `≤ₚ`** [AB09, Figure 2.1 and the remark after
Definition 2.7]: if `L ≤ₚ L'` and `L' ∈ P` then `L ∈ P`.

**Proof sketch.** Compose the reduction machine with a polynomial-time decider of
`L'` (`Complexity.mem_P_iff`, read pointwise as computing the total
singleton-indicator function) via the **timed** total composition
`Turing.FinTM.computesFunInTime_comp` — the untimed `exists_comp_partial`
carries no time bound (phase-1 audit, finding 4). The intermediate string `f x`
has polynomially bounded length
(`Complexity.PolyTimeComputable.output_length_le`), so the decider's budget on
it is polynomial in `|x|` by monotonicity of the explicit polynomial, and the
composite decides `L` since `x ∈ L ↔ f x ∈ L'`; return through
`Complexity.mem_P_of_dtime_le`.

The implementation packages the decider as a polynomial-time computable
singleton-indicator function and applies `PolyTimeComputable.comp`, whose
proof invokes the timed interface above with its intermediate-output bound.
Finally `succ_pow_le` converts the resulting `(n+1)^d` budget to the
`n^d+1` form consumed by `mem_P_of_dtime_le`. -/
theorem mem_P_of_polyTimeReducible {L L' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ∈ P) : L ∈ P := by
  classical
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h'
  have hg : PolyTimeComputable (fun y => [MultiTapeTM.indicator (L' : Set (List Bool)) y]) :=
    ⟨M, C, c, hM⟩
  obtain ⟨S, A, d, hS⟩ := hg.comp hf
  have hdec : S.DecidesInTime L (fun n => A * (n + 1) ^ d) := by
    intro x
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x =
        MultiTapeTM.indicator (L' : Set (List Bool)) (f x) := by
      simp only [MultiTapeTM.indicator, hL x]
    simpa only [Function.comp_apply, hi] using hS x
  refine mem_P_of_dtime_le (T := fun n => A * (n + 1) ^ d)
    ⟨1, S, ?_⟩ (A * 2 ^ d) d ?_
  · intro x
    simpa only [Nat.one_mul] using hdec x
  · intro n
    calc
      A * (n + 1) ^ d ≤ A * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left A (succ_pow_le n d)
      _ = A * 2 ^ d * (n ^ d + 1) := (Nat.mul_assoc _ _ _).symm

/-- **`NP`-hardness** [AB09, Definition 2.7]: every `NP` language Karp-reduces to
`L`. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, L' ≤ₚ L

/-- **`NP`-completeness** [AB09, Definition 2.7]: `L` is in `NP` and `NP`-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

/-- **If an `NP`-hard language is in `P`, then `P = NP`** [AB09, Theorem 2.8.2].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; conversely every
`L' ∈ NP` reduces to the `NP`-hard `L ∈ P`, so `L' ∈ P` by
`Complexity.mem_P_of_polyTimeReducible`. -/
theorem P_eq_NP_of_NPHard_mem_P {L : Language Bool}
    (hL : NPHard L) (h : L ∈ P) : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  intro L' hL'
  exact mem_P_of_polyTimeReducible (hL L' hL') h

/-- **An `NP`-complete language is in `P` iff `P = NP`** [AB09, Theorem 2.8.3].

**Proof sketch.** (⇒) is `Complexity.P_eq_NP_of_NPHard_mem_P` on the hardness
half; (⇐) rewrites `L ∈ NP` along `P = NP`. -/
theorem NPComplete.mem_P_iff {L : Language Bool} (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by
  constructor
  · exact P_eq_NP_of_NPHard_mem_P hL.2
  · intro h
    rw [h]
    exact hL.1


/-- Encode the simulated state and remembered bit. The inner `none` is a live
loop state, distinct from the outer `none` that denotes actual halting. -/
private def acceptState {Q : Type} (q : Option Q) (b : Bool) : Option (Option (Q × Bool)) :=
  match q with
  | some q => some (some (q, b))
  | none => if b then none else some none

/-- Update the bit before redirecting the successor state. In particular a bit
emitted by a halting transition is remembered. Physical output is suppressed. -/
private def acceptAction {k : ℕ} {Q : Type} (a : Action k Bool Q) (b : Bool) :
    Action k Bool (Option (Q × Bool)) :=
  ⟨a.inputTape, a.workTapes, none, acceptState a.state (a.output.getD b)⟩

/-- The halting recognizer associated to a Boolean-output decider. It uses the
same work tapes and either simulates a source state or stays in its live loop. -/
private def acceptTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := Option (M.State × Bool)
  tm :=
    { q₀ := some (M.tm.q₀, false)
      tr := fun q inp work => match q with
        | none => ⟨0, fun _ => (none, 0), none, some none⟩
        | some (q, b) => acceptAction (M.tm.tr q inp work) b }

/-- Configuration correspondence: the finite register holds the last emitted
bit (initially false), while the recognizer's real output stays empty. -/
private def acceptCfg (M : FinTM Bool) {x : List Bool} (cfg : Cfg M.k Bool M.State x) :
    Cfg (acceptTM M).k Bool (acceptTM M).State x :=
  ⟨acceptState cfg.state (cfg.output.getLast?.getD false), cfg.inputPos,
    cfg.workTapes, cfg.workTapePos, []⟩

/-- A live loop configuration never changes and therefore never halts. -/
private lemma acceptTM_loop (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg (acceptTM M).k Bool (acceptTM M).State x) (h : cfg.state = some none)
    (t : ℕ) : (acceptTM M).tm.runFrom cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, h, acceptTM, Action.apply]

/-- Capturing an action agrees with capturing its resulting configuration. -/
private lemma acceptCfg_apply (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (acceptAction a (cfg.output.getLast?.getD false)).apply (acceptCfg M cfg) =
      acceptCfg M (a.apply cfg) := by
  have hlast : (cfg.output ++ a.output.toList).getLast?.getD false =
      a.output.getD (cfg.output.getLast?.getD false) := by
    cases a.output <;> simp
  apply Cfg.ext
  · dsimp only [acceptCfg, acceptAction, Action.apply]
    rw [hlast]
  · rfl
  · rfl
  · rfl
  · rfl

/-- The control transform commutes with every step, including a halt that
emits the decision bit. Rejection maps to the stationary live loop. -/
private lemma acceptCfg_step (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    (acceptTM M).tm.step (acceptCfg M cfg) = acceptCfg M (M.tm.step cfg) := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    cases hb : cfg.output.getLast?.getD false with
    | false =>
      exact acceptTM_loop M (acceptCfg M cfg) (by simp [acceptCfg, acceptState, hs, hb]) 1
    | true =>
      exact MultiTapeTM.step_of_halt (by simp [acceptCfg, acceptState, hs, hb])
  | some q =>
    have hi : (acceptCfg M cfg).inputSymbol = cfg.inputSymbol := rfl
    have hw : (acceptCfg M cfg).workTapeSymbols = cfg.workTapeSymbols := rfl
    simp only [MultiTapeTM.step, acceptCfg, acceptState, hs]
    change (acceptAction (M.tm.tr q (acceptCfg M cfg).inputSymbol
      (acceptCfg M cfg).workTapeSymbols) (cfg.output.getLast?.getD false)).apply
        (acceptCfg M cfg) = _
    rw [hi, hw]
    exact acceptCfg_apply M cfg _

/-- Initialized runs commute with the control transformation, by the step
correspondence. This is the run invariant for the HALT reduction. -/
private lemma acceptTM_run (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    (acceptTM M).tm.runFrom ((acceptTM M).tm.initCfg x) t =
      acceptCfg M (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (acceptTM M).tm.initCfg x = acceptCfg M (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (acceptCfg M) (acceptCfg_step M)
    (M.tm.initCfg x) t

/-- The transformed machine halts exactly when the total source decider's bit
is true. This lemma assumes totality only for the source decider, never for the
deliberately divergent result.

**Proof sketch.** The run invariant says a transformed run can halt only when
the source has halted and its last bit is true. Determinism identifies that
completed output with the source decider's singleton output. Conversely, at a
completed accepting run the invariant immediately gives transformed halting. -/
private lemma acceptTM_halts_iff (M : FinTM Bool) (p : List Bool → Bool)
    (hM : M.Computes fun x => [p x]) (x : List Bool) :
    (∃ w t, (acceptTM M).ComputesInTime x w t) ↔ p x = true := by
  constructor
  · rintro ⟨w, t, ht⟩
    have hhalt := ((FinTM.computesInTime_iff _ _ _ _).mp ht).1
    rw [acceptTM_run] at hhalt
    change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
      ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none at hhalt
    have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := by
      cases h : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => rfl
      | some q => simp only [acceptState, h, reduceCtorEq] at hhalt
    have hcomp : M.ComputesInTime x (M.tm.runFrom (M.tm.initCfg x) t).output t :=
      (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨s, hMs⟩ := hM x
    have hout := hcomp.output_unique hMs
    rw [hs, hout] at hhalt
    simpa [acceptState] using hhalt
  · intro hp
    obtain ⟨t, ht⟩ := hM x
    obtain ⟨hs, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp ht
    refine ⟨[], t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [acceptTM_run]
    constructor
    · change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
        ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none
      rw [hs, hout]
      simp [acceptState, hp]
    · rfl

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def prefixTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def prefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma prefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (prefixTM w).tm.runFrom ((prefixTM w).tm.initCfg x) i =
      prefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [prefixCfg, prefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, prefixCfg, prefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma prefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (prefixTM w).tm.runFrom
      (prefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [prefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (prefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [prefixCfg]; omega) (by omega)
    change ((prefixTM w).tm.tr ⟨w.length, by omega⟩
      (prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [prefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, prefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- Prefixing computes `w ++ x` in exactly the bound `|w| + |x| + 1`,
including the final blank-reading halting step.

**Proof sketch.** Concatenate the fixed-word emission run and the input-copy
run; the input head then scans the right boundary, so one final step halts
without emitting anything further. This also covers empty prefix and input. -/
private lemma prefixTM_computes (w : List Bool) :
    (prefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, prefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', prefixTM_copy w x x.length (Nat.le_refl _)]
  simp [prefixTM, prefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]

/-- The fixed-code pairing machine has the audited budget
`2|α| + |x| + 3`: two emissions per code bit, two for the delimiter, one per
input bit, and one final blank-reading step. -/
private lemma fixedPair_computes (α : List Bool) :
    (prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true])).ComputesFunInTime
      (fun x => pairEncode α x) (fun n => 2 * α.length + n + 3) := by
  have hlen : (α.flatMap fun b => [b, b]).length = 2 * α.length := by
    induction α with
    | nil => rfl
    | cons b α ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  intro x
  have h := prefixTM_computes ((α.flatMap fun b => [b, b]) ++ [false, true]) x
  have ht : ((α.flatMap fun b => [b, b]) ++ [false, true]).length + x.length + 1 =
      2 * α.length + x.length + 3 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  simpa only [pairEncode, ht] using h

/-- The fixed-code pairing machine is polynomial-time computable. -/
private lemma fixedPair_polyTime (α : List Bool) :
    PolyTimeComputable (fun x => pairEncode α x) := by
  refine ⟨prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true]),
    2 * α.length + 3, 1, fun x => (fixedPair_computes α x).mono ?_⟩
  simp only [Nat.pow_one, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega


/-- **`HALT` is `NP`-hard** [AB09, Exercise 2.8] — for **every** representation
scheme, effective or not: the reduction embeds one *fixed* code, so only
`Turing.MachineCode.decode_encode` is used (phase-1 audit, finding 11; compare
Chapter 1's Theorem 1.10/1.11 split, where only the evaluator direction needs
effectivity).

**Proof sketch** (the audit's repaired construction, finding 6 — the earlier
divergent-searcher route is unusable because
`Turing.FinTM.one_work_tape_binary` requires a *total* function). Fix `L ∈ NP`.
(1) Obtain a **total** exponential-time decider `D` of `L` from the repaired
`Complexity.NP_subset_EXP`. (2) Normal-form `D` with
`Turing.FinTM.one_work_tape_binary` (legal: `D` is total). (3) Modify the
one-work-tape machine's finite control with a register remembering the Boolean
emission — including a bit emitted on the halting transition — and replace its
halt: halt iff the remembered bit is `true`, otherwise enter a stationary
one-state live loop (such a deliberately divergent state exists: emit nothing,
move nothing, return the same live state). This control modification needs its
own run/halting lemma — a named fill obligation. The result `S` halts on `x`
iff `x ∈ L`. (4) Code `S` with `Turing.exists_codeTM` (no totality hypothesis)
and set `α := c.encode S`. The reduction maps `x ↦ Turing.pairEncode α x`: a
fixed doubled prefix of length `2|α| + 2` followed by the verbatim input,
computable by an emit-then-copy machine in `2|α| + |x| + 3` steps (a small new
machine or prefixing lemma — the audited `pairDiagTM` computes the diagonal
pair, not this fixed-prefix function). `Complexity.HALT_pairEncode_eq_true_iff`
and `Turing.MachineCode.decode_encode` turn membership of the image in `HALT`
into "`S` halts on `x`", which is `x ∈ L`. -/
theorem HALT_NPHard (c : MachineCode) :
    NPHard {s | HALT c s = true} := by
  classical
  intro L hL
  obtain ⟨d, a, D, hD⟩ := Set.mem_iUnion.mp (NP_subset_EXP hL)
  let p : List Bool → Bool := MultiTapeTM.indicator (L : Set (List Bool))
  have hdec : D.ComputesFunInTime (fun x => [p x]) (fun n => a * 2 ^ n ^ d) := hD
  obtain ⟨M, b, hk, hM⟩ := FinTM.one_work_tape_binary D _ _ hdec
  obtain ⟨S, hS⟩ := exists_codeTM (acceptTM M) hk
  refine ⟨fun x => pairEncode (c.encode S) x, fixedPair_polyTime _, fun x => ?_⟩
  change x ∈ L ↔ HALT c (pairEncode (c.encode S) x) = true
  rw [HALT_pairEncode_eq_true_iff, c.decode_encode]
  simp only [hS]
  rw [acceptTM_halts_iff M p hM.computes x]
  simp [p, MultiTapeTM.indicator]

/-- **`HALT` is not in `NP`** [AB09, Exercise 2.8] — so, despite being `NP`-hard,
it is not `NP`-complete: `NP` languages are decidable, `HALT` is not.

**Proof sketch.** If `HALT`'s language were in `NP`, it would be in `EXP` by
the repaired `Complexity.NP_subset_EXP`, so some machine would decide it — and
a decider's output is exactly `[HALT c s]` (off the pair image `HALT` is
`false` and the rejection bit matches, per the totalization convention), making
`fun s => [HALT c s]` computable
(`Complexity.Computable` via `Turing.FinTM.ComputesFunInTime.computes`),
contradicting `Complexity.HALT_not_computable`. The audit certified this chain
valid once `NP_subset_EXP` is repaired. The `Turing.EffectiveMachineCode`
hypothesis is a **proof-route restriction, not a mathematical necessity**
(round-2 audit, finding 3 — the pre-repair docstring's trivial-machine
"counterexample" violates `decode_encode` and is unlawful): this proof reuses
Chapter 1's `HALT_not_computable`, whose own proof runs the universal
evaluator and hence needs effectivity. The round-2 audit exhibited a direct
diagonalization (diagonal pairing, the searcher's control transform with the
halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator) proving `HALT`
undecidable for **every** lawful `Turing.MachineCode`; whether to add that
diagonal lemma and generalize this statement is a recorded human-review
design question (`AroraBarakChapter2Plan.md`, open design questions). Until
decided, this statement stays at the generality its cited API supports. -/
theorem HALT_not_mem_NP (c : EffectiveMachineCode) :
    {s | HALT c.toMachineCode s = true} ∉ NP := by
  classical
  intro h
  apply HALT_not_computable c
  obtain ⟨d, a, M, hM⟩ := Set.mem_iUnion.mp (NP_subset_EXP h)
  have hi : MultiTapeTM.indicator
      ({s | HALT c.toMachineCode s = true} : Set (List Bool)) = HALT c.toMachineCode := by
    funext s
    simp only [MultiTapeTM.indicator, Set.mem_setOf_eq]
    split
    · rename_i hb; exact hb.symm
    · rename_i hb; exact (Bool.eq_false_iff.mpr hb).symm
  have hdec : M.ComputesFunInTime (fun s => [HALT c.toMachineCode s])
      (fun n => a * 2 ^ n ^ d) := by
    simpa only [FinTM.DecidesInTime, hi] using hM
  exact ⟨M, hdec.computes⟩

end Complexity

## ===== TCSlib/Complexity/ClassNP/TMSAT.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.Universal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TMSAT: the first NP-complete language

[AB09, Theorem 2.9]: the language
`TMSAT = {⟨α, x, 1^n, 1^t⟩ : ∃ u ∈ {0,1}^n, M_α outputs 1 on ⟨x, u⟩ within t
steps}` is `NP`-complete — the "generic" `NP`-complete problem, read off the
definition of `NP` itself. This module defines `TMSAT` over the audited
Chapter-1 machine-code layer and states Theorem 2.9, together with the
polynomial time-constructibility statement the hardness reduction's unary
components rely on.

## Design and deviations from [AB09]

* **The tuple is right-nested `Turing.pairEncode`**:
  `⟨α, x, 1^n, 1^t⟩` is rendered
  `pairEncode α (pairEncode x (pairEncode 1^n 1^t))`, with `1^k` the string
  `List.replicate k true`. The pairing is self-delimiting and injective
  (`Turing.pairEncode_injective`), so the four components are recoverable and
  unique — strings not of this shape are simply not members.
* **"`M_α` outputs `1` on input `⟨x, u⟩` within `t` steps"** is rendered
  `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t` — completed
  output exactly `[true]` by step `t` (halting is absorbing), the audited
  output-convention of the whole development, against the total decoding of a
  `Turing.MachineCode`. The unary components make `n` and `t` at most the
  input length — [AB09]'s footnote 2: padding the input is what entitles the
  verifier and the reduction to run in time polynomial in `n` and `t`.
* **The generality split refines the audited `HALT` treatment**
  (`Complexity.HALT_NPHard` at `Turing.MachineCode`,
  `Complexity.HALT_not_mem_NP` at `Turing.EffectiveMachineCode`): the language
  and its `NP`-hardness need only a lawful code (`decode` totality and
  `decode_encode`; the reduction writes a *fixed* code string), while
  membership in `NP` runs the universal machine over an input-supplied `α` and
  therefore takes an effective scheme **with a polynomially bounded canonizer**
  — the hypothesis `Complexity.PolyBound c.canonizerTime` on the membership
  and completeness statements. Effectivity alone is **not** enough (round-1
  audit, finding 1, Argument A): `Turing.EffectiveMachineCode` bounds the
  canonizer's computability, not its cost, and a lawful effective scheme can
  plant arbitrarily expensive decidable information behind short codes,
  pushing its `TMSAT` outside `EXP ⊇ NP`. `NP`-completeness carries the same
  hypothesis.
* **`Complexity.timeConstructible_poly` is a new statement about a Chapter-1
  notion** (`Complexity.TimeConstructible`, `ClassP/TimeConstructible.lean`) —
  stated here rather than by editing the frozen audited file, and **flagged for
  this phase's audit** exactly as `Complexity.compl_mem_P` was in phase 1. The
  exponent is `c + 1` because time-constructibility requires `T n ≥ n`, which
  degree `0` would violate.

## Main definitions

* `Complexity.TMSAT` — [AB09, Theorem 2.9's language].

## Main results

* `Complexity.timeConstructible_poly` — `n ↦ C·(n+1)^(c+1)` is
  time-constructible (`C > 0`); the plan's supporting obligation for the
  reduction's unary components. [AB09, §1.3]
* `Complexity.timed_universal_quantitative` — the phase-3-mandated new public
  bridge with an explicit code-length coefficient; its proof is escalated
  under the epoch-2 brief's private-API protocol.
* `Complexity.TMSAT_mem_NP` — for schemes with polynomially bounded
  canonizers, the certificate is `u` itself; verification is timed universal
  simulation. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPHard` — the generic reduction: send `x` to
  `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPComplete` — [AB09, Theorem 2.9], under the same
  polynomial-canonizer hypothesis as membership.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.9 with footnote 2, pp. 43-44;
  §1.3 for time constructibility.)
-/

namespace Complexity

open Turing

/-- **The language `TMSAT`** [AB09, Theorem 2.9]: quadruples
`⟨α, x, 1^n, 1^t⟩` — right-nested `Turing.pairEncode`, unary third and fourth
components — such that some certificate `u` of length exactly `n` makes the
machine denoted by `α` (total decoding of the scheme `c`) halt on the paired
input `⟨x, u⟩` within `t` steps with completed output exactly `[true]`. -/
def TMSAT (c : MachineCode) : Language Bool :=
  {y | ∃ (α x u : List Bool) (n t : ℕ),
    y = pairEncode α
          (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) ∧
    u.length = n ∧
    (c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t}

/-! ### Exact unary polynomial generation

The following private machine enumerates a fixed-dimensional box of side
`|x| + 1`. Its output is a unary polynomial, so composing it with the public
linear-time binary length counter gives an exact binary polynomial value.
No private declaration from the Chapter-1 counter is used.
-/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive PolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance polyControlFintype (c C : ℕ) : Fintype (PolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance polyControlDecidableEq (c C : ℕ) : DecidableEq (PolyControl c C) :=
  (proxy_equiv% (PolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def polyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def polyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : PolyControl c C) : Action (c + 1) Bool (PolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def polyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := PolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then polyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then polyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else polyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then polyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def polyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => polyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma polyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (polyMove i d s').apply (polyCfg x q s h o) =
      polyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [polyMove, polyCfg, Action.apply, hj]
  · simp [polyMove, polyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma poly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      polyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        polyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma poly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      polyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, polyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [polyCfg] using polyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, polyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma poly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (polyUnaryTM c C).tm.step
      (polyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      polyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, polyUnaryTM, polyCfg, i.isLt, ↓reduceDIte]
  simpa [polyCfg] using polyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def polyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (polyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma poly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (polyCost q C i + 2) + q + 2) =
      polyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (polyUnaryTM c C).tm.runFrom
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (polyCost q C i + 2) =
        polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (polyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', polyCfg, Cfg.workTapeSymbols, polyTape, hj]
      have hs : (polyUnaryTM c C).tm.step (polyCfg x q (.loop ⟨i, hi⟩) h' o) =
          polyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [polyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) _ = _
        rw [show polyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [polyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) 1 =
            polyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          poly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (polyUnaryTM c C).tm.runFrom
            (polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (polyCost q C i) =
            polyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (polyCost q C (i - 1) + 2) + q + 2 =
              polyCost q C i := by
            calc
              _ = polyCost q C (i - 1 + 1) := rfl
              _ = polyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show polyCost q C i + 2 = 1 + polyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (polyUnaryTM c C).tm.step
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          polyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, Cfg.workTapeSymbols, polyCfg, Function.update_self,
          polyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, poly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (polyCost q C i + 2) + q + 2 =
          (polyCost q C i + 2) + (r * (polyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma polyTape_write (q : ℕ) :
    Function.update (polyTape q) (q : ℤ) (some true) = polyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [polyTape]
  · rw [Function.update_of_ne hz]
    unfold polyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma polyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    polyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [polyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      polyCost q C (r + 1) = q * (polyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def polyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => polyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma poly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x) i =
      polyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, polyCopyCfg, polyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (polyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [polyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact polyTape_write i
    · funext k
      simp [polyUnaryTM, polyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma poly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      polyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        polyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma poly_start (c C : ℕ) (x : List Bool) :
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (polyUnaryTM c C).tm.step
      (polyCopyCfg c C x x.length (le_refl _)) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (polyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [polyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact polyTape_write x.length
    · funext k
      simp [polyUnaryTM, polyCopyCfg, polyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', poly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact poly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary polynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma poly_unary_computes (c C : ℕ) :
    (polyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := poly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (polyUnaryTM c C).tm.runFrom
      (polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (polyCost (x.length + 1) C (c + 1)) =
      polyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [polyCost, hout] using hl
  have hbase : (polyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + polyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, poly_start, hloop]
    simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (polyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring

/-- **Polynomial bounds are time constructible**: for `C > 0`, the function
`n ↦ C·(n+1)^(c+1)` is `Complexity.TimeConstructible`. (A **new statement about
the Chapter-1 notion**, flagged for this phase's audit — see the deviations
list; the exponent `c + 1` keeps `T n ≥ n`, which degree `0` would violate.)
This is the plan's supporting obligation for the `TMSAT` reduction's unary
components.

**Proof sketch.** The bound `n ≤ n + 1 ≤ C·(n+1)^(c+1)` holds since `C ≥ 1`.
The machine: scan the input once, incrementing a little-endian binary counter
per cell to obtain `n` (the audited `Complexity.timeConstructible_id` fill is
the in-repo precedent; its private counter layer is a template, not a citable
API — phase-1 audit, finding 5); then compute `(n+1)^(c+1)` by `c + 1`
successive schoolbook binary multiplications and multiply by the constant `C`
(a fixed number of multiplications on operands of `O((c+1)·log(n+2) + log(C+1))`
bits, each polynomial in the bit length); emit the result as
`(T |x|).bits` (little-endian, the `Complexity.TimeConstructible` output
convention). Budget: the scan is `n` steps and the arithmetic polylogarithmic,
against the constant-slack budget `c'·(C·(n+1)^(c+1) + 1)` — ample.

**Implementation note (epoch 2).** The formal proof uses an exact unary
box-enumeration machine followed by the public linear-time binary length
counter, rather than formalizing schoolbook multiplication. Each of `c+1`
unary loop tapes has length `n+1`; each box point emits exactly `C` bits.
The generator costs at most `(C+5(c+1)+4)(n+1)^(c+1)`; timed composition with
`timeConstructible_id` preserves linear time in the polynomial's value.
This is a proof-route deviation only; the frozen statement is unchanged. -/
theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
    TimeConstructible fun n => C * (n + 1) ^ (c + 1) := by
  have hdom (n : ℕ) : (n + 1) ^ (c + 1) ≤ C * (n + 1) ^ (c + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((n + 1) ^ (c + 1)) hC
  refine ⟨fun n => ?_, ?_⟩
  · have hp : n + 1 ≤ (n + 1) ^ (c + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
        (show 1 ≤ c + 1 by omega)
    exact (Nat.le_succ n).trans (hp.trans (hdom n))
  · obtain ⟨_, a, ha, M, hM⟩ := timeConstructible_id
    have hcounter : M.ComputesFunInTime (fun x => x.length.bits) (fun n => a * (n + 1)) :=
      hM
    obtain ⟨N, b, hN⟩ := FinTM.computesFunInTime_comp (poly_unary_computes c C) hcounter
      (by intro m n h; exact Nat.mul_le_mul_left a (Nat.add_le_add_right h 1))
    let A := C + 5 * (c + 1) + 4
    refine ⟨(b + 1) * (a + 1) * (A + 1),
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _), N, ?_⟩
    intro x
    have hb := hN x
    simp only [Function.comp_apply, List.length_replicate] at hb
    apply hb.mono
    have hmajor : A * (x.length + 1) ^ (c + 1) + 1 ≤
        (A + 1) * (C * (x.length + 1) ^ (c + 1) + 1) := by
      have hm := Nat.mul_le_mul_left A (hdom x.length)
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    change b * (A * (x.length + 1) ^ (c + 1) +
        a * (A * (x.length + 1) ^ (c + 1) + 1) + 1) ≤ _
    calc
      _ = b * (a + 1) * (A * (x.length + 1) ^ (c + 1) + 1) := by ring
      _ ≤ (b + 1) * (a + 1) *
          ((A + 1) * (C * (x.length + 1) ^ (c + 1) + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (a + 1) (Nat.le_succ b)) hmajor
      _ = _ := by ring

/-! ### Quantitative timed-universal bridge -/

/-- The canonizer's completed serialization cannot be longer than its run. -/
private lemma tmsat_serialization_length (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)).2
  simpa only [hout] using c.canonizer.tm.output_length_le α (c.canonizerTime α.length)

/-- Flattening a nonempty word for each element cannot shorten a list. -/
private lemma tmsat_flatMap_length {A B : Type} (f : A → List B)
    (hf : ∀ a, 1 ≤ (f a).length) (l : List A) : l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hf a
    omega

/-- Every transition record contains at least its two-bit input-head action. -/
private lemma tmsat_action_nonempty {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    1 ≤ (actionBits a).length := by
  have hs : 2 ≤ (signBits a.inputTape).length := by
    cases a.inputTape <;> exact Nat.le_refl 2
  change 1 ≤ (signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state).length
  simp only [List.length_append]
  omega

/-- The canonical serialization bounds the bit-header length, initial-state
index, and total number of states.

**Proof sketch.** The header contains the first two fields. Each state has a
nonempty transition record in the serialized table, so its number of records
also bounds the state count. This uses the public serialization definition. -/
private lemma tmsat_serialization_parameters (M : CodeTM) :
    (Nat.bits M.numStates).length ≤ M.serialize.length ∧
      M.tm.q₀.val ≤ M.serialize.length ∧ M.numStates + 1 ≤ M.serialize.length := by
  let f := fun q : Fin (M.numStates + 1) =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)
  have hf (q : Fin (M.numStates + 1)) : 1 ≤ (f q).length := by
    dsimp only [f]
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    have := tmsat_action_nonempty (M.tm.tr q none (fun _ => none))
    omega
  have htable : M.numStates + 1 ≤ ((List.finRange (M.numStates + 1)).flatMap f).length := by
    simpa only [List.length_finRange] using tmsat_flatMap_length f hf
      (List.finRange (M.numStates + 1))
  have hlen : M.serialize.length = 2 * (Nat.bits M.numStates).length + 2 +
      (M.tm.q₀.val + 1 + ((List.finRange (M.numStates + 1)).flatMap f).length) := by
    change (pairEncode (Nat.bits M.numStates)
      ((List.replicate M.tm.q₀.val true ++ [false]) ++
        (List.finRange (M.numStates + 1)).flatMap f)).length = _
    simp only [universal_pair_length, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
  rw [hlen]
  omega

/-- The concrete coefficient displayed in the private timed-simulator proof
is bounded by the mandated public bridge's closed coefficient.

**Proof sketch.** The serialization, header length, initial index, and state
count are each bounded by the canonizer time. Expanding the concrete startup
and block coefficients gives one canonizer term plus thirteen such bounded
terms and constant fifty. This is solely an arithmetic bound on the displayed
expression, not a bound on `timed_universal`'s arbitrary existential witness. -/
private lemma tmsat_concrete_coefficient (c : EffectiveMachineCode) (α : List Bool) :
    3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14 ≤ 3 * α.length + 14 * c.canonizerTime α.length + 50 := by
  have hlen := tmsat_serialization_length c α
  obtain ⟨hbits, hstart, hstates⟩ := tmsat_serialization_parameters (c.decode α)
  unfold universalBlockBound
  omega

/-- A single timed simulator, selected before the code and input, preserves
both successful completion and timeout with the explicit budget
`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.

**The phase-3-mandated bridge statement: new public surface for the epoch-2
audit.** Its coefficient is the displayed function of the code length; no
bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.

**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
timed simulator's construction, bound the decoded serialization length by the
canonizer's output-time bound, and bound the state/header sizes by that
serialization. The existing proof's coefficient is then at most the displayed
coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
`Universal.lean` are private. The public API exposes only the existential
coefficient, so the construction cannot be reused through that API. This single
bridge declaration is intentionally admitted under the brief's escalation
protocol: the maintainer must export a quantitative concrete bounded-answer
lemma from Chapter 1 (including its timeout branch) and discharge this proof.
Chapter-1 sources are unchanged.

**Discharged (2026-10-03, maintainer serial merge).** Chapter 1 now exports
`Turing.timed_universal_concrete`: the concrete simulator's bounded-answer
theorem with the private startup expression expanded into public vocabulary
and both clauses preserved. This proof is that export, the arithmetic bound
`tmsat_concrete_coefficient` on its displayed coefficient, and
`Turing.FinTM.ComputesInTime.mono`. The escalation paragraph above is
retained as audit history; its final sentence described the pre-export
state, and the export is flagged for the shared infrastructure audit
round. -/
theorem timed_universal_quantitative (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  obtain ⟨hsucc, htimeout⟩ := hU α x t
  have hle : (3 * α.length + c.canonizerTime α.length +
      (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length +
      2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14) * (t + 1) ^ 2 ≤
      (3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (tmsat_concrete_coefficient c α)
  exact ⟨fun output hout => (hsucc output hout).mono hle,
    fun hnone => (htimeout hnone).mono hle⟩

/-- The exact success-tagged output or timeout answer of a bounded source run. -/
private def tmsatAnswer (c : MachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  let cfg := (c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t
  if cfg.state = none then true :: cfg.output else [false]

/-- Both clauses of the quantitative bridge yield a completed answer for every
well-formed timed request, including divergent source computations.

**Proof sketch.** Inspect the source configuration at the deadline. A halted
configuration witnesses completed computation with its full output. A live
configuration rules out every completed output, activating the timeout clause. -/
private lemma tmsat_simulator_total (c : EffectiveMachineCode) (U : FinTM Bool)
    (hU : ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool, (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)))
    (α x : List Bool) (t : ℕ) :
    U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (tmsatAnswer c.toMachineCode α x t)
      ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2) := by
  by_cases hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none
  · have hs := (FinTM.computesInTime_iff (c.decode α).toFinTM x
      (((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output) t).mpr ⟨hh, rfl⟩
    simpa only [tmsatAnswer, if_pos hh] using (hU α x t).1 _ hs
  · have hs : ∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t := by
      intro output ho
      exact hh ((FinTM.computesInTime_iff _ _ _ _).mp ho).1
    simpa only [tmsatAnswer, if_neg hh] using (hU α x t).2 hs

/-- Acceptance compares the entire captured answer with `[true,true]`;
timeouts and successful runs with any other completed output are rejected. -/
private lemma tmsatAnswer_accept (c : MachineCode) (α x : List Bool) (t : ℕ) :
    tmsatAnswer c α x t = [true, true] ↔
      (c.decode α).toFinTM.ComputesInTime x [true] t := by
  rw [FinTM.computesInTime_iff]
  dsimp only [tmsatAnswer]
  split <;> simp_all [CodeTM.toFinTM]

/-- The polynomial canonizer hypothesis gives one polynomial budget, uniform
over every code length and unary deadline bounded by the instance length.

**Proof sketch.** Bound both the linear code-length term and the canonizer
majorant by a power of degree `max 1 e`. Absorb the constant term into the
same positive power and multiply by the deadline's quadratic bound. No
monotonicity of the canonizer time itself is assumed. -/
private lemma tmsat_simulation_budget (c : EffectiveMachineCode)
    (hc : PolyBound c.canonizerTime) :
    ∃ A d : ℕ, ∀ m r t : ℕ, r ≤ m → t ≤ m →
      (3 * r + 14 * c.canonizerTime r + 50) * (t + 1) ^ 2 ≤ A * (m + 1) ^ d := by
  obtain ⟨C, e, he⟩ := hc
  refine ⟨3 + 14 * C + 50, max 1 e + 2, ?_⟩
  intro m r t hr ht
  have hp : 1 ≤ (m + 1) ^ max 1 e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hrp : r ≤ (m + 1) ^ max 1 e := by
    calc r ≤ m + 1 := by omega
      _ = (m + 1) ^ 1 := by simp
      _ ≤ (m + 1) ^ max 1 e := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_left _ _)
  have hH : c.canonizerTime r ≤ C * (m + 1) ^ max 1 e := by
    calc c.canonizerTime r ≤ C * (r + 1) ^ e := he r
      _ ≤ C * (m + 1) ^ e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e)
      _ ≤ C * (m + 1) ^ max 1 e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right _ _))
  have hcoef : 3 * r + 14 * c.canonizerTime r + 50 ≤
      (3 + 14 * C + 50) * (m + 1) ^ max 1 e := by
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  calc
    _ ≤ ((3 + 14 * C + 50) * (m + 1) ^ max 1 e) * (m + 1) ^ 2 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by rw [Nat.mul_assoc, ← Nat.pow_add]

/-- The right-nested quadruple used by `TMSAT`, with exact unary fields. -/
private def tmsatQuad (α x : List Bool) (n t : ℕ) : List Bool :=
  pairEncode α (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true)))

/-- All four tuple components fit inside the full encoded instance. -/
private lemma tmsat_quad_bounds (α x : List Bool) (n t : ℕ) :
    α.length ≤ (tmsatQuad α x n t).length ∧ x.length ≤ (tmsatQuad α x n t).length ∧
      n ≤ (tmsatQuad α x n t).length ∧ t ≤ (tmsatQuad α x n t).length := by
  simp only [tmsatQuad, universal_pair_length, List.length_replicate]
  omega

/-- The verifier specification uses an exact odd-length split, parses the
quadruple, and tests only the requested prefix of the padded certificate. -/
private def tmsatVerifier (c : MachineCode) : Language Bool :=
  {z | ∃ (y w α x : List Bool) (n t : ℕ),
    z = y ++ w ∧ w.length = y.length + 1 ∧ y = tmsatQuad α x n t ∧
      (c.decode α).toFinTM.ComputesInTime (pairEncode x (w.take n)) [true] t}

/-- Exact certificates force odd total length and recover the split position uniquely. -/
private lemma tmsat_split_length (y w : List Bool) (hw : w.length = y.length + 1) :
    (y ++ w).length % 2 = 1 ∧ ((y ++ w).length - 1) / 2 = y.length := by
  simp only [List.length_append, hw]
  omega

/-- The exact `m+1`-bit certificate convention is equivalent to the language's
original `n`-bit witness. No certificate-length majorization changes the source run.

**Proof sketch.** Pad the original witness with false bits and recover it by
taking its first `n` bits. Conversely, equality of the two concatenations and
their exact certificate lengths forces equal split positions, so the accepted
prefix has length exactly `n`. The tuple's unary field bounds `n` by `m`. -/
private lemma tmsat_certificate_equiv (c : MachineCode) (y : List Bool) :
    y ∈ TMSAT c ↔ ∃ w : List Bool, w.length = y.length + 1 ∧ y ++ w ∈ tmsatVerifier c := by
  constructor
  · rintro ⟨α, x, u, n, t, hy, hu, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    let w := u ++ List.replicate (y.length + 1 - n) false
    have hw : w.length = y.length + 1 := by
      simp only [w, List.length_append, List.length_replicate, hu]
      omega
    refine ⟨w, hw, y, w, α, x, n, t, rfl, hw, hy, ?_⟩
    have htake : w.take n = u := List.take_left' hu
    rw [htake]
    exact hs
  · rintro ⟨w, hw, y', w', α, x, n, t, he, hw', hy, hs⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, hw, hw'] at hlen
    obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
    refine ⟨α, x, w.take n, n, t, hy, ?_, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    rw [List.length_take, Nat.min_eq_left (by omega : n ≤ w.length)]

/-- Timed buffered composition needs the second machine to terminate only on
the first machine's image. Its bound is measured against the original input.

**Proof sketch.** Capture the preprocessing output on the composition buffer,
rewind and dispatch through the public `bufferedComp_start` theorem, then
relocate the second run through `bufferedSecondCfg_run`. Output length is at
most preprocessing time, so capture and rewind cost at most twice that time
plus two. This also permits a timed universal machine that is partial on
malformed requests, provided preprocessing always constructs a valid request. -/
private lemma tmsat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
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
  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- Linear-time catalog contracts are instances of the polynomial calculus. -/
private lemma tmsat_pt_linear (f : List Bool → List Bool)
    (h : ∃ (M : FinTM Bool) (C : ℕ),
      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f := by
  obtain ⟨M, C, hM⟩ := h
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- A fixed word is emitted from finite control. -/
private lemma tmsat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  exact tmsat_pt_linear _ (FinTM.computesFunInTime_const w)

/-- Total first projection; callers independently guard grammar validity. -/
private def tmsatFst (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- Total second projection; callers independently guard grammar validity. -/
private def tmsatSnd (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The library's pair-to-concatenation function, including malformed inputs. -/
private def tmsatConcat (z : List Bool) : List Bool :=
  match pairDecode z with | some (a,b) => a ++ b | none => []

/-- The library's payload-only map; it never inspects the retained head. -/
private def tmsatMap (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with | some (a,b) => pairEncode a (g b) | none => []

/-- Polynomial payload maps follow C1, with a monotone polynomial runtime.
The linear administrative term is absorbed at degree `max 1 e`. -/
private lemma tmsat_pt_map {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (tmsatMap g) := by
  obtain ⟨G, C, e, hG⟩ := hg
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by intro m n h; exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e))
  refine ⟨M, a * (C + 1), max 1 e, fun x => (hM x).mono ?_⟩
  have hlin : x.length + 1 ≤ (x.length + 1) ^ max 1 e := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (Nat.le_max_left 1 e)
  have hp := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_max_right 1 e))
  simp only [Nat.succ_eq_add_one] at hp
  calc
    _ ≤ a * ((C + 1) * (x.length + 1) ^ max 1 e) :=
      Nat.mul_le_mul_left a (by rw [Nat.add_mul, Nat.one_mul]; omega)
    _ = _ := by ring

/-- Assemble two computed values by the canonical §9c recipe.

**Proof sketch.** Build `H x = pairEncode (f x) []`, retain the input in
`s x = pairEncode x (H x)`, then retain `s x` while computing `g` from its
first projection. Concatenation and second projection remove the two
administrative encodings, leaving exactly `pairEncode (f x) (g x)`. -/
private lemma tmsat_pt_pair {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
  have hd := tmsat_pt_linear _ FinTM.computesFunInTime_pairDup
  have hp := tmsat_pt_linear _ FinTM.computesFunInTime_pairFst
  have hs := tmsat_pt_linear _ FinTM.computesFunInTime_pairSnd
  have hc := tmsat_pt_linear _ FinTM.computesFunInTime_pairConcat
  have hH := ((tmsat_pt_map (tmsat_pt_const [])).comp hd).comp hf
  have hS := (tmsat_pt_map hH).comp hd
  have hT := ((tmsat_pt_map (hg.comp hp)).comp hd).comp hS
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, tmsatMap, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  have he (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  rw [he, he]
  simp [pairDecode_pairEncode]

/-- Polynomial-time branches on the original input, using W3's captured
single-bit decision. All three budgets fit their maximum degree. -/
private lemma tmsat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨P, A, a, hP⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hP hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have ha := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show a ≤ e by exact Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show b ≤ e by omega))
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show c ≤ e by omega))
  have h1 : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [Nat.succ_eq_add_one] at ha hb hc
  calc
    _ ≤ K * ((A + B + C + 1) * (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (by simp only [Nat.add_mul, Nat.one_mul]; omega)
    _ = _ := by ring

/-- Equality with an entire fixed answer is a polynomial-time bit test. -/
private lemma tmsat_pt_eq (w : List Bool) :
    PolyTimeComputable (fun x => [decide (x = w)]) := by
  have h := tmsat_pt_linear _ (FinTM.computesFunInTime_ifEq w [true] [false])
  convert h using 1
  funext x
  by_cases hx : x = w <;> simp [hx]

/-- A fixed-width increment never successfully returns the empty word. -/
private lemma tmsat_inc_nonempty (w : List Bool) : incFixed w ≠ some [] := by
  cases w with
  | nil => simp [incFixed]
  | cons b w => cases b <;> cases h : incFixed w <;> simp [incFixed, h]

/-- Overflow is exactly the all-true unary shape, including length zero. -/
private lemma tmsat_inc_none (w : List Bool) :
    incFixed w = none ↔ w = List.replicate w.length true := by
  induction w with
  | nil => simp [incFixed]
  | cons b w ih => cases b <;> simp [incFixed, List.replicate_succ, ih]

/-- The exact all-true shape is decided by P11 overflow and whole-word equality. -/
private lemma tmsat_pt_unary :
    PolyTimeComputable (fun x => [decide (x = List.replicate x.length true)]) := by
  have h := (tmsat_pt_eq []).comp (tmsat_pt_linear _ FinTM.computesFunInTime_incFixed)
  convert h using 1
  funext x
  have he : (incFixed x).getD [] = [] ↔ x = List.replicate x.length true := by
    rw [← tmsat_inc_none]
    cases hi : incFixed x with
    | none => simp
    | some w =>
      have hw : w ≠ [] := by intro hw; subst w; exact tmsat_inc_nonempty x hi
      simp [hw]
  simp only [Function.comp_apply, he]

/-- Count doubled prefix cells on a unary work tape, then emit at most that
many native payload bits while moving the work head left. The output stays
silent until the separator; the public use supplies only constructed pairs. -/
private def tmsatTakeTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := { q₀ := 0, tr := fun q inp w =>
    if q = 0 then
      match inp with
      | some b => ⟨1, fun _ => (none, 0), none, some (if b then 2 else 1)⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩
    else if q = 1 then
      match inp with
      | some false => ⟨1, fun _ => (some (some true), 1), none, some 0⟩
      | some true => ⟨1, fun _ => (none, -1), none, some 3⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩
    else if q = 2 then
      match inp with
      | some true => ⟨1, fun _ => (some (some true), 1), none, some 0⟩
      | _ => ⟨0, fun _ => (none, 0), none, none⟩
    else
      match w 0, inp with
      | some _, some b => ⟨1, fun _ => (none, -1), some b, some 3⟩
      | _, _ => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Prefix-extractor configurations record both the allocated unary interval
and its current head; the native input index is the number of consumed bits. -/
private def tmsatTakeCfg (x : List Bool) (q : Option (Fin 4))
    (i : ℕ) (hi : i ≤ x.length) (m : ℕ) (h : ℤ) (out : List Bool) :
    Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i+1, by omega⟩, fun _ => polyTape m, fun _ => h, out⟩

/-- Exact one-step input lookup for the indexed extractor configuration. -/
private lemma tmsat_take_read (x : List Bool) (q : Option (Fin 4))
    (i : ℕ) (hi : i ≤ x.length) (m : ℕ) (h : ℤ) (out : List Bool) :
    (tmsatTakeCfg x q i hi m h out).inputSymbol = x[i]? := by
  exact FinTM.inputSymbol_at _ i hi rfl

/-- Two equal prefix bits append precisely one unary counter cell. -/
private lemma tmsat_take_double (x : List Bool) (i m : ℕ) (b : Bool)
    (hi : i + 2 ≤ x.length) (h₀ : x[i]? = some b) (h₁ : x[i+1]? = some b) :
    tmsatTakeTM.tm.runFrom (tmsatTakeCfg x (some 0) i (by omega) m m []) 2 =
      tmsatTakeCfg x (some 0) (i+2) hi (m+1) (m+1) [] := by
  have hs : tmsatTakeTM.tm.step (tmsatTakeCfg x (some 0) i (by omega) m m []) =
      tmsatTakeCfg x (some (if b then 2 else 1)) (i+1) (by omega) m m [] := by
    change (tmsatTakeTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read, h₀]
    change (⟨1, fun _ => (none, 0), none, some (if b then 2 else 1)⟩ :
      Action 1 Bool (Fin 4)).apply _ = _
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · rfl
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tmsatTakeTM.tm.tr (if b then (2 : Fin 4) else (1 : Fin 4)) _ _).apply _ = _
  rw [tmsat_take_read, h₁]
  cases b <;>
    change (⟨1, fun _ => (some (some true), 1), none, some 0⟩ :
      Action 1 Bool (Fin 4)).apply _ = _
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · funext j; exact polyTape_write m
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl

/-- The separator consumes two native bits and places the counter at its last cell. -/
private lemma tmsat_take_separator (x : List Bool) (i m : ℕ)
    (hi : i + 2 ≤ x.length) (h₀ : x[i]? = some false) (h₁ : x[i+1]? = some true) :
    tmsatTakeTM.tm.runFrom (tmsatTakeCfg x (some 0) i (by omega) m m []) 2 =
      tmsatTakeCfg x (some 3) (i+2) hi m ((m : ℤ)-1) [] := by
  have hs : tmsatTakeTM.tm.step (tmsatTakeCfg x (some 0) i (by omega) m m []) =
      tmsatTakeCfg x (some 1) (i+1) (by omega) m m [] := by
    change (tmsatTakeTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read, h₀]
    change (⟨1, fun _ => (none, 0), none, some 1⟩ : Action 1 Bool (Fin 4)).apply _ = _
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · rfl
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tmsatTakeTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  rw [tmsat_take_read, h₁]
  change (⟨1, fun _ => (none, -1), none, some 3⟩ : Action 1 Bool (Fin 4)).apply _ = _
  apply Cfg.ext
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
  · rfl
  · funext j; simp [Action.apply, tmsatTakeCfg, sub_eq_add_neg]
  · rfl

/-- The aligned parser installs exactly the first component's length.

**Proof sketch.** Induct on the remaining doubled prefix, preserving an
arbitrary already-counted prefix. Each pair costs two steps; the separator
costs two more. No native payload bit has yet been emitted. -/
private lemma tmsat_take_parse (a b : List Bool) :
    ∀ (x pre : List Bool) (m : ℕ) (hx : x = pre ++ pairEncode a b),
    tmsatTakeTM.tm.runFrom
      (tmsatTakeCfg x (some 0) pre.length (by simp [hx, pairEncode]) m m [])
      (2*a.length+2) =
    tmsatTakeCfg x (some 3) (pre.length+2*a.length+2)
      (by simp [hx, universal_pair_length]; omega)
      (m+a.length) ((m+a.length : ℕ)-1 : ℤ) [] := by
  induction a with
  | nil =>
    intro x pre m hx
    have h₀ : x[pre.length]? = some false := by simp [hx, pairEncode]
    have h₁ : x[pre.length+1]? = some true := by simp [hx, pairEncode]
    simpa using tmsat_take_separator x pre.length m (by simp [hx, pairEncode]) h₀ h₁
  | cons v a ih =>
    intro x pre m hx
    have hx' : x = (pre ++ [v,v]) ++ pairEncode a b := by
      simpa [pairEncode, List.append_assoc] using hx
    have hs := tmsat_take_double x pre.length m v
      (by simp [hx', List.length_append])
      (by simp [hx', List.append_assoc]) (by simp [hx', List.append_assoc])
    conv_lhs => arg 2; rw [show 2*(v::a).length+2 = 2+(2*a.length+2) by simp; omega]
    rw [MultiTapeTM.runFrom_add, hs]
    have h := ih x (pre ++ [v,v]) (m+1) hx'
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add,
      Nat.mul_one, Nat.cast_add, Nat.cast_one, Nat.reduceAdd] using h

/-- The payload phase emits the exact requested prefix, even if the request
exceeds the payload length; it stops at either boundary.

**Proof sketch.** Induct on the number of emitted bits up to the minimum of
the counter and payload lengths. Every step preserves the unary tape and
moves its head left. The next step sees either the left blank or the native
right boundary and halts without an additional bit. -/
private lemma tmsat_take_payload (x pre b : List Bool) (hx : x = pre ++ b) (m : ℕ) :
    ∀ j (hj : j ≤ min m b.length),
      tmsatTakeTM.tm.runFrom
        (tmsatTakeCfg x (some 3) pre.length (by simp [hx]) m ((m:ℤ)-1) []) j =
      tmsatTakeCfg x (some 3) (pre.length+j) (by simp [hx] ; omega)
        m ((m:ℤ)-j-1) (b.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [tmsatTakeCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change (tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read]
    have hr : x[pre.length+j]? = some b[j] := by
      simp only [hx, List.getElem?_append_right (by omega : pre.length ≤ pre.length+j),
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem (show j < b.length by omega)]
    rw [hr]
    have hw : (tmsatTakeCfg x (some 3) (pre.length+j) (by simp [hx] ; omega)
        m ((m:ℤ)-j-1) (b.take j)).workTapeSymbols 0 = some true := by
      simp [tmsatTakeCfg, Cfg.workTapeSymbols, polyTape,
        show 0 ≤ (m:ℤ)-j-1 ∧ (m:ℤ)-j-1 < m by omega] ; omega
    simp only [tmsatTakeTM, show (3:Fin 4) ≠ 0 by decide, if_false,
      show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; simp only [hx, List.length_append]; omega)
    · rfl
    · funext i; simp [Action.apply, tmsatTakeCfg]; omega
    · simp only [Action.apply, tmsatTakeCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- On every constructed pair, prefix extraction takes at most input length
plus one steps. Malformed-input behavior is never invoked by the assembly. -/
private lemma tmsat_take_computes (a b : List Bool) :
    tmsatTakeTM.ComputesInTime (pairEncode a b) (b.take a.length)
      ((pairEncode a b).length+1) := by
  let x := pairEncode a b
  let pre := (a.flatMap fun v => [v,v]) ++ [false,true]
  have hx : x = pre ++ b := rfl
  have hp : pre.length = 2*a.length+2 := by
    have h := universal_pair_length a ([] : List Bool)
    simpa [pre, pairEncode] using h
  have hs := tmsat_take_parse a b x [] 0 rfl
  simp only [List.length_nil, Nat.zero_add, Nat.cast_zero] at hs
  have hi : tmsatTakeTM.tm.initCfg x = tmsatTakeCfg x (some 0) 0 (by omega) 0 0 [] := by
    apply Cfg.ext <;> simp [tmsatTakeCfg, tmsatTakeTM]
    funext i z
    simp [polyTape]
  have hrun : tmsatTakeTM.tm.runFrom (tmsatTakeTM.tm.initCfg x)
      (2*a.length+2+min a.length b.length) =
      tmsatTakeCfg x (some 3) (pre.length+min a.length b.length)
        (by simp [hx] ) a.length
        ((a.length:ℤ)-min a.length b.length-1) (b.take (min a.length b.length)) := by
    rw [MultiTapeTM.runFrom_add, hi, hs]
    simpa only [List.length_nil, Nat.zero_add, hp] using
      tmsat_take_payload x pre b hx a.length (min a.length b.length) (by omega)
  have ht : tmsatTakeTM.ComputesInTime x (b.take a.length)
      (2*a.length+2+min a.length b.length+1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun]
    change ((tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧
      ((tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _).output = b.take a.length
    rw [tmsat_take_read]
    have hend :
      polyTape a.length ((a.length:ℤ)-min a.length b.length-1) = none ∨
        x[pre.length+min a.length b.length]? = none := by
      by_cases h : a.length ≤ b.length
      · left; simp [Nat.min_eq_left h, polyTape]
      · right; simp [Nat.min_eq_right (by omega : b.length ≤ a.length), hx]
    rcases hend with hw | hr
    · simp [tmsatTakeTM, tmsatTakeCfg, Cfg.workTapeSymbols, hw, Action.apply,
        List.take_eq_take_min]
    · simp [tmsatTakeTM, tmsatTakeCfg, Cfg.workTapeSymbols, hr, Action.apply,
        List.take_eq_take_min]
  apply ht.mono
  dsimp [x]
  rw [universal_pair_length]
  omega

/-- The prefix extractor is used only on pairs made by the §9c assembly.
Its time is bounded by that preprocessor's actual output-length guarantee. -/
private lemma tmsat_pt_take {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => (g x).take (f x).length) := by
  obtain ⟨M, C, e, hM⟩ := tmsat_pt_pair hf hg
  have hT (x : List Bool) : tmsatTakeTM.ComputesInTime (pairEncode (f x) (g x))
      ((g x).take (f x).length) (C * (x.length+1)^e+1) := by
    apply (tmsat_take_computes (f x) (g x)).mono
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    have hl := M.tm.output_length_le x (C * (x.length+1)^e)
    rw [ho] at hl
    dsimp only at hl
    omega
  obtain ⟨N, hN⟩ := tmsat_comp_on_image M tmsatTakeTM _ (fun x => (g x).take (f x).length)
    (fun n => C*(n+1)^e) (fun n => C*(n+1)^e+1) hM hT
  refine ⟨N, 3*(C+1), e, fun x => (hN x).mono ?_⟩
  have hp : 1 ≤ (x.length+1)^e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  dsimp only
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  omega

/-- Conjunction preserves short-circuit guard order: the second test runs
only after the first succeeded. -/
private lemma tmsat_pt_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  have h := tmsat_pt_cond hp hq (tmsat_pt_const [false])
  convert h using 1
  funext x
  cases p x <;> rfl

/-- A successful parser returns the unique original pair encoding.
The proof follows the aligned two-bit grammar, without identifying parse
failure with an empty first or second component. -/
private lemma tmsat_pair_inverse (z : List Bool) :
    ∀ a b, pairDecode z = some (a,b) → z = pairEncode a b := by
  induction z using List.twoStepInduction with
  | nil => intro a b h; simp [pairDecode] at h
  | singleton v => intro a b h; cases v <;> simp [pairDecode] at h
  | cons_cons v w rest ih _ =>
    intro a b h
    cases v <;> cases w
    · obtain ⟨⟨u,v⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      rw [ih u v hp]
      rfl
    · cases h; rfl
    · simp [pairDecode] at h
    · obtain ⟨⟨u,v⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      rw [ih u v hp]
      rfl

/-- On valid inputs the projections reconstruct the pair. -/
private lemma tmsat_pair_valid (z : List Bool) (h : (pairDecode z).isSome = true) :
    z = pairEncode (tmsatFst z) (tmsatSnd z) := by
  cases hd : pairDecode z with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨a,b⟩
    simpa only [tmsatFst, tmsatSnd, hd, Option.map_some, Option.getD_some] using
      tmsat_pair_inverse z a b hd

/-- The exact odd split is the P10 search at coefficient and degree one. -/
private def tmsatSplit (z : List Bool) : List Bool :=
  match solveSplit 1 1 z.length with
  | some i => pairEncode (z.take i) (z.drop i)
  | none => []

/-- A successful split has precisely the required length equation. -/
private lemma tmsat_split_some (N i : ℕ) (h : solveSplit 1 1 N = some i) :
    i + (i+1) = N := by
  have he := List.find?_some h
  simpa [Nat.pow_one] using he

/-- If the exact length equation has a solution, P10 returns that solution.
Any returned index satisfies the same strictly increasing linear equation. -/
private lemma tmsat_split_exists (N i : ℕ) (h : i+(i+1)=N) :
    solveSplit 1 1 N = some i := by
  cases hs : solveSplit 1 1 N with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp; omega)
    simp [h] at hn
  | some j =>
    have hj := tmsat_split_some N j hs
    congr 1
    omega

/-- The exact split gives back the original instance and padded certificate. -/
private lemma tmsat_split_append (y w : List Bool) (hw : w.length=y.length+1) :
    tmsatSplit (y++w) = pairEncode y w := by
  unfold tmsatSplit
  rw [tmsat_split_exists (y++w).length y.length (by simp [hw])]
  simp

/-- Both halves of a successful odd split retain their original native lengths. -/
private lemma tmsat_split_components (z : List Bool)
    (h : (pairDecode (tmsatSplit z)).isSome = true) :
    z = tmsatFst (tmsatSplit z) ++ tmsatSnd (tmsatSplit z) ∧
    (tmsatSnd (tmsatSplit z)).length = (tmsatFst (tmsatSplit z)).length+1 := by
  cases hs : solveSplit 1 1 z.length with
  | none => simp [tmsatSplit, hs, pairDecode] at h
  | some i =>
    have hi := tmsat_split_some z.length i hs
    simp only [tmsatSplit, hs, tmsatFst, tmsatSnd, pairDecode_pairEncode,
      Option.map_some, Option.getD_some]
    refine ⟨(List.take_append_drop i z).symm, ?_⟩
    simp only [List.length_take, List.length_drop]
    omega

/-- The parsed instance is the first exact-split component. -/
private def tmsatY (z : List Bool) : List Bool := tmsatFst (tmsatSplit z)

/-- The padded certificate is the second exact-split component. -/
private def tmsatW (z : List Bool) : List Bool := tmsatSnd (tmsatSplit z)

/-- The retained code field. -/
private def tmsatCode (z : List Bool) : List Bool := tmsatFst (tmsatY z)

/-- The retained source input field. -/
private def tmsatInput (z : List Bool) : List Bool := tmsatFst (tmsatSnd (tmsatY z))

/-- The unary certificate-length field, before shape validation. -/
private def tmsatWidth (z : List Bool) : List Bool := tmsatFst (tmsatSnd (tmsatSnd (tmsatY z)))

/-- The unary deadline field, before shape validation. -/
private def tmsatClock (z : List Bool) : List Bool := tmsatSnd (tmsatSnd (tmsatSnd (tmsatY z)))

/-- Grammar guards precede projections at all three quadruple spine levels;
then both unary fields are checked in full, including the empty word. -/
private def tmsatGood (z : List Bool) : Bool :=
  (pairDecode (tmsatSplit z)).isSome &&
  ((pairDecode (tmsatY z)).isSome &&
  ((pairDecode (tmsatSnd (tmsatY z))).isSome &&
  ((pairDecode (tmsatSnd (tmsatSnd (tmsatY z)))).isSome &&
  (decide (tmsatWidth z = List.replicate (tmsatWidth z).length true) &&
   decide (tmsatClock z = List.replicate (tmsatClock z).length true)))))

/-- Successful guards reconstruct the exact quadruple and split equation. -/
private lemma tmsat_good_spec (z : List Bool) (h : tmsatGood z = true) :
    z = tmsatY z ++ tmsatW z ∧ (tmsatW z).length = (tmsatY z).length+1 ∧
    tmsatY z = tmsatQuad (tmsatCode z) (tmsatInput z)
      (tmsatWidth z).length (tmsatClock z).length := by
  simp only [tmsatGood, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hy, hx, hn, hwidth, hclock⟩ := h
  obtain ⟨hz, hw⟩ := tmsat_split_components z hs
  refine ⟨hz, hw, ?_⟩
  have h₀ := tmsat_pair_valid (tmsatY z) hy
  have h₁ := tmsat_pair_valid (tmsatSnd (tmsatY z)) hx
  have h₂ := tmsat_pair_valid (tmsatSnd (tmsatSnd (tmsatY z))) hn
  change tmsatY z = pairEncode (tmsatCode z)
    (pairEncode (tmsatInput z) (pairEncode (List.replicate _ true) (List.replicate _ true)))
  rw [← hwidth, ← hclock]
  exact h₀.trans (congrArg (pairEncode (tmsatCode z))
    (h₁.trans (congrArg (pairEncode (tmsatInput z)) h₂)))

/-- Every well-formed quadruple with its padded witness passes every guard,
and all fields are recovered literally. -/
private lemma tmsat_good_quad (α x w : List Bool) (n t : ℕ)
    (hw : w.length = (tmsatQuad α x n t).length+1) :
    let z := tmsatQuad α x n t ++ w
    tmsatGood z = true ∧ tmsatCode z = α ∧ tmsatInput z = x ∧
      (tmsatWidth z).length = n ∧ (tmsatClock z).length = t ∧ tmsatW z = w := by
  dsimp only
  simp only [tmsatGood, tmsatCode, tmsatInput, tmsatWidth, tmsatClock, tmsatW, tmsatY]
  simp only [tmsat_split_append _ _ hw]
  simp [tmsatQuad, tmsatFst, tmsatSnd, pairDecode_pairEncode]

/-- Computed fields and ordered validation use P10, P6, P11, and W3.
Each projection consumes the preceding computed word; validity is still
checked separately before its result can enter an accepted request. -/
private lemma tmsat_fields_poly :
    PolyTimeComputable tmsatCode ∧ PolyTimeComputable tmsatInput ∧
    PolyTimeComputable tmsatWidth ∧ PolyTimeComputable tmsatClock ∧
    PolyTimeComputable tmsatW ∧ PolyTimeComputable (fun z => [tmsatGood z]) := by
  obtain ⟨S, A, hS⟩ := FinTM.computesFunInTime_splitSolve 1 1
  have hsplit : PolyTimeComputable tmsatSplit := ⟨S,A,3,hS⟩
  have hf : PolyTimeComputable tmsatFst := tmsat_pt_linear _ FinTM.computesFunInTime_pairFst
  have hs : PolyTimeComputable tmsatSnd := tmsat_pt_linear _ FinTM.computesFunInTime_pairSnd
  have hv := tmsat_pt_linear _ FinTM.computesFunInTime_pairValid
  have hy : PolyTimeComputable tmsatY := hf.comp hsplit
  have h₁ := hs.comp hy
  have h₂ := hs.comp h₁
  have hn : PolyTimeComputable tmsatWidth := hf.comp h₂
  have ht : PolyTimeComputable tmsatClock := hs.comp h₂
  refine ⟨hf.comp hy, hf.comp h₁, hn, ht, hs.comp hsplit, ?_⟩
  exact tmsat_pt_and (hv.comp hsplit) (tmsat_pt_and (hv.comp hy)
    (tmsat_pt_and (hv.comp h₁) (tmsat_pt_and (hv.comp h₂)
      (tmsat_pt_and (tmsat_pt_unary.comp hn) (tmsat_pt_unary.comp ht)))))

/-- Invalid requests are replaced by a well-formed zero-deadline request,
so the simulator is used only on its proved totality domain. -/
private def tmsatRequest (z : List Bool) : List Bool :=
  if tmsatGood z then
    pairEncode (pairEncode (Nat.bits (tmsatClock z).length) (tmsatCode z))
      (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
  else pairEncode (pairEncode [] []) []

/-- The exact completed answer associated with preprocessing. -/
private def tmsatResult (c : MachineCode) (z : List Bool) : List Bool :=
  if tmsatGood z then
    tmsatAnswer c (tmsatCode z)
      (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
      (tmsatClock z).length
  else tmsatAnswer c [] [] 0

/-- Construct the guarded timed request by the canonical §9c pairing recipe.

**Proof sketch.** Retain the whole request as the head of a pair while C1
runs the binary length counter on the unary clock payload. Pair the extracted
binary clock with the recovered code, and the recovered source input with
the exact prefix extractor's output. W3 chooses that request only after all
guards succeed, otherwise emitting the fixed zero-deadline request. -/
private lemma tmsat_request_poly : PolyTimeComputable tmsatRequest := by
  obtain ⟨ha,hx,hn,ht,hw,hgood⟩ := tmsat_fields_poly
  have hb := tmsat_pt_linear _ FinTM.computesFunInTime_lengthBits
  have hs := tmsat_pt_linear _ FinTM.computesFunInTime_pairSnd
  have hclock : PolyTimeComputable (fun z => Nat.bits (tmsatClock z).length) := by
    have h := hs.comp ((tmsat_pt_map hb).comp (tmsat_pt_pair polyTimeComputable_id ht))
    convert h using 1
    funext z
    simp [Function.comp_apply, tmsatMap, pairDecode_pairEncode]
  exact tmsat_pt_cond hgood
    (tmsat_pt_pair (tmsat_pt_pair hclock ha) (tmsat_pt_pair hx (tmsat_pt_take hn hw)))
    (tmsat_pt_const (pairEncode (pairEncode [] []) []))

/-- Valid code lengths and unary deadlines are bounded by the original
verifier input length, so the simulator consumes the proved uniform budget. -/
private lemma tmsat_good_bounds (z : List Bool) (h : tmsatGood z = true) :
    (tmsatCode z).length ≤ z.length ∧ (tmsatClock z).length ≤ z.length := by
  obtain ⟨hz, hw, hy⟩ := tmsat_good_spec z h
  have hb := tmsat_quad_bounds (tmsatCode z) (tmsatInput z)
    (tmsatWidth z).length (tmsatClock z).length
  rw [← hy] at hb
  have hlen := congrArg List.length hz
  simp only [List.length_append] at hlen
  omega

/-- The guarded simulator's whole-answer test is exactly the existential
verifier specification, including rejection of every invalid request.

**Proof sketch.** Successful guards reconstruct the original split and
quadruple, and `tmsatAnswer_accept` identifies the source acceptance event.
Conversely every witness of the specification passes all guards and is
recovered literally. A failed guard uses deadline zero, where the source
machine cannot have halted. -/
private lemma tmsat_result_accept (c : MachineCode) (z : List Bool) :
    tmsatResult c z = [true,true] ↔ z ∈ tmsatVerifier c := by
  constructor
  · intro h
    by_cases hg : tmsatGood z = true
    · obtain ⟨hz, hw, hy⟩ := tmsat_good_spec z hg
      simp only [tmsatResult, hg, ↓reduceIte, tmsatAnswer_accept] at h
      exact ⟨tmsatY z, tmsatW z, tmsatCode z, tmsatInput z,
        (tmsatWidth z).length, (tmsatClock z).length, hz, hw, hy, h⟩
    · have hzero : ¬(c.decode []).toFinTM.ComputesInTime [] [true] 0 :=
        FinTM.not_computesInTime_zero _ _ _
      simp only [tmsatResult, if_neg hg, tmsatAnswer_accept] at h
      exact (hzero h).elim
  · rintro ⟨y,w,α,x,n,t,hz,hw,hy,hs⟩
    subst y
    subst z
    obtain ⟨hg,ha,hx,hn,ht,hw'⟩ := tmsat_good_quad α x w n t hw
    simp only [tmsatResult, hg, ↓reduceIte, ha, hx, hn, ht, hw', tmsatAnswer_accept]
    exact hs

/-- **`TMSAT ∈ NP` for polynomially canonizable schemes** [AB09, Theorem 2.9,
membership]: the certificate is `u` itself, and verification is timed
universal simulation. The hypothesis `Complexity.PolyBound c.canonizerTime`
is **load-bearing and cannot be dropped** (round-1 audit, finding 1,
Argument A): `Turing.EffectiveMachineCode` constrains the canonizer's
*computability*, not its cost, and there is a lawful effective scheme — the
base scheme behind a one-bit tag, with the tagged branch decoding `[1] ++ z`
to a one-step machine that outputs the bit `A z` of a decidable language
`A ∉ EXP` — whose `TMSAT` decides `A` on the trivial instances
`⟨[1] ++ z, [], 1^0, 1^1⟩`; membership in `NP ⊆ EXP` would contradict
`A ∉ EXP`. The polynomial canonizer bound is what restores a uniform
simulation budget.

**Proof sketch.** Certificate parameters `(1, 1)`: length exactly `m + 1` on
inputs of length `m` (the declared `n` satisfies `n ≤ m`, since `1^n` sits
inside `y`; the certificate is `u` padded to `m + 1` bits, `u` recovered as the
first `n` bits — no marker needed, `n` is read off `y`). The verifier language:
`V = {y ++ w : |w| = |y| + 1`, `y` parses as a quadruple
`⟨α, x, 1^n, 1^t⟩`, and the machine `α` denotes accepts `⟨x, w.take n⟩` within
`t` steps`}`. `V ∈ P` by a machine with the named fill obligations: (i)
unique-split recovery — a well-formed input has length `m + (m + 1) = 2m + 1`,
**odd**, so the machine **rejects even lengths** and splits an odd length `N`
at `(N − 1) / 2` (round-1 audit, finding 4, correcting the drafted parity);
(ii) the **quadruple parser** — three nested `pairDecode` passes (the aligned
two-bit grammar; the `UniversalStartup` parsing layer is the in-repo
precedent) plus all-`true` shape checks on the third and fourth components,
rejecting any failure; (iii) **unary-to-binary clock conversion**:
`Turing.timed_universal`'s clock input is `Nat.bits t`, so the verifier
converts the unary `1^t` by counter increments (`Nat.bits 0 = []` at the
`t = 0` edge, where every instance is negative —
`Turing.FinTM.not_computesInTime_zero`); (iv) **assembly and relocated
simulation**: build `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x
(w.take n))` on a work tape and run the timed universal machine `U` of
`Turing.timed_universal c` relocated-and-captured (the standing obligations);
`U` answers `true :: output` or `[false]` by design and its branches are
exhaustive, so acceptance is exactly the complete captured answer
`[true, true]` — a timeout, or any completed output other than `[true]`,
rejects; (v) the verdict with buffered output. **Budget** — where the
hypothesis enters: `U` completes within `C_α·(t+1)^2` steps, and the round-1
audit's inspection of the `Universal` module's bound definitions gives, with
`r = |α|` and `H = c.canonizerTime r`, the chain `C_α ≤ 3r + 14·H + 50` (the
decoded serialization's length `L` bounds the header/state parameters and is
itself at most `H`, the canonizer writing it within its time budget —
`Turing.MultiTapeTM.output_length_le`); `PolyBound c.canonizerTime` then
bounds `C_α` by a polynomial in `r ≤ m` uniformly, and with `t ≤ m` the whole
simulation is polynomial in `m`: `V ∈ P` via `Complexity.mem_P_of_dtime_le`.
**Named fill obligation (new public bridge)**: the public
`Turing.timed_universal` exposes its constant only existentially per code, so
the fill needs a quantitative public form of the bound (an addition to the
audited `Universal` surface, to be requested through the standing shared-file
mechanism and flagged for its audit round — the round-1 finding's repair
guidance; a prose obligation alone cannot discharge the budget). Membership
equivalence: forward, a `TMSAT` witness `u` pads to `m + 1` bits (absorbing
halting keeps the accepting run); backward, a certificate's first `n` bits are
a witness — `Turing.timed_universal`'s two branches convert between `U`'s
answers and `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t`
exactly, and `Turing.pairEncode_injective` pins the parsed components to the
defining existential's.

**Continuation implementation note.** The exact odd split is P10 at `(1,1)`.
P6 guards each nested parse before extraction; P11 overflow plus whole-word
equality checks both unary fields. The private prefix machine reads exactly
the declared number of witness bits. C1 applies the binary length counter
only to a clock payload while retaining the request, and the canonical §9c
recipe assembles the timed input. Invalid inputs become a valid zero-deadline
request; the proved quantitative bridge, both answer clauses, and the existing
uniform budget close the simulation. Whole-word equality with `[true,true]`
produces the final verdict. -/
theorem TMSAT_mem_NP (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    TMSAT c.toMachineCode ∈ NP := by
  obtain ⟨U, hU⟩ := timed_universal_quantitative c
  obtain ⟨A, d, hbudget⟩ := tmsat_simulation_budget c hc
  have htotal := tmsat_simulator_total c U hU
  have hV : tmsatVerifier c.toMachineCode ∈ P := by
    -- D-MEM closed: guards, exact prefix extraction, valid request assembly,
    -- both simulator outcomes, and whole-answer equality are all checked.
    classical
    obtain ⟨M, C, e, hM⟩ := tmsat_request_poly
    have hs (z : List Bool) : U.ComputesInTime (tmsatRequest z)
        (tmsatResult c.toMachineCode z) (A*(z.length+1)^d) := by
      by_cases hg : tmsatGood z = true
      · obtain ⟨ha,ht⟩ := tmsat_good_bounds z hg
        simpa only [tmsatRequest, tmsatResult, hg, ↓reduceIte] using
          (htotal (tmsatCode z)
            (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
            (tmsatClock z).length).mono (hbudget z.length _ _ ha ht)
      · simpa only [tmsatRequest, tmsatResult, if_neg hg, show Nat.bits 0 = [] by simp] using
          (htotal [] [] 0).mono (hbudget z.length 0 0 (by omega) (by omega))
    obtain ⟨N,hN⟩ := tmsat_comp_on_image M U tmsatRequest (tmsatResult c.toMachineCode)
      (fun n => C*(n+1)^e) (fun n => A*(n+1)^d) hM hs
    have hresult : PolyTimeComputable (tmsatResult c.toMachineCode) := by
      refine ⟨N,2*C+A+2,max e d,fun z => (hN z).mono ?_⟩
      have he := Nat.mul_le_mul_left (2*C)
        (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_left e d))
      have hd := Nat.mul_le_mul_left A
        (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_right e d))
      have h1 : 1 ≤ (z.length+1)^max e d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      dsimp only
      simp only [Nat.succ_eq_add_one, Nat.mul_assoc] at he hd
      simp only [Nat.add_mul, Nat.mul_assoc]
      omega
    obtain ⟨D,B,b,hD⟩ := (tmsat_pt_eq [true,true]).comp hresult
    apply mem_P_iff.mpr
    refine ⟨B,b,D,fun z => ?_⟩
    have hout : [decide (tmsatResult c.toMachineCode z = [true,true])] =
        [MultiTapeTM.indicator (tmsatVerifier c.toMachineCode : Set (List Bool)) z] := by
      simp only [tmsat_result_accept]
      simp [MultiTapeTM.indicator]
    simpa only [Function.comp_apply, hout] using hD z

  refine ⟨1, 1, tmsatVerifier c.toMachineCode, hV, ?_⟩
  intro y
  simpa only [Nat.pow_one, Nat.one_mul] using tmsat_certificate_equiv c.toMachineCode y

/-- The audited deadline formula majorizes the normalized wrapper runtime.
The certificate length remains exactly `C*(n+1)^c` throughout this inequality.

**Proof sketch.** The paired input plus one cell is bounded by
`(C+3)(n+1)^max(1,c)`. Raise to the wrapper degree, absorb its additive one
into the positive power, and square for the one-work-tape normalization.
Only the deadline is enlarged. -/
private lemma tmsat_deadline_bound (K B e C c n : ℕ) :
    K * (B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1) ^ 2 ≤
      ((K + 1) * (B + 1) ^ 2 * (C + 3) ^ (2 * e)) *
        (n + 1) ^ (2 * e * max 1 c) := by
  have hlin : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left 1 c)
  have hpow : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right 1 c)
  have hsize : 2 * n + 2 + C * (n + 1) ^ c + 1 ≤
      (C + 3) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hpow
    rw [Nat.add_mul]
    omega
  have hepow : (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e ≤
      (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ ((C + 3) * (n + 1) ^ max 1 c) ^ e := Nat.pow_le_pow_left hsize e
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) e]
  have hpos : 1 ≤ (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.succ_pos _))
  have hinner : B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1 ≤
      (B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ B * ((C + 3) ^ e * (n + 1) ^ (e * max 1 c)) +
          (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
        Nat.add_le_add (Nat.mul_le_mul_left B hepow) hpos
      _ = _ := by ring
  calc
    _ ≤ (K + 1) * ((B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hinner 2)
    _ = _ := by
      simp only [Nat.mul_pow, ← Nat.pow_mul]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Constant strings are polynomial-time computable by finite emission chains. -/
private lemma tmsat_constant_poly (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_const w
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- The exact binary certificate length is polynomial-time computable,
including zero coefficients and degree zero.

**Proof sketch.** Follow the audited three-way split: coefficient zero emits
the empty word; positive coefficient and degree zero emits its fixed binary
representation from finite control; positive coefficient and positive degree
uses `timeConstructible_poly C (c-1)`. Only the runtime is enlarged. -/
private lemma tmsat_exact_certificate_bits (C c : ℕ) :
    PolyTimeComputable (fun x : List Bool => (C * (x.length + 1) ^ c).bits) := by
  by_cases hC : C = 0
  · simpa [hC] using tmsat_constant_poly []
  · by_cases hc : c = 0
    · simpa [hc] using tmsat_constant_poly C.bits
    · obtain ⟨_, a, _, M, hM⟩ := timeConstructible_poly C (c - 1) (by omega)
      have he : c - 1 + 1 = c := by omega
      simp only [he] at hM
      refine ⟨M, a * (C + 1), c, fun x => (hM x).mono ?_⟩
      have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
      calc
        _ ≤ a * ((C + 1) * (x.length + 1) ^ c) :=
          Nat.mul_le_mul_left a (by rw [Nat.add_mul, Nat.one_mul]; omega)
        _ = _ := by ring

/-- The wrapper's total output function rejects malformed pairs and otherwise
forwards the verifier's verdict on the concatenated components. -/
private noncomputable def tmsatWrapperOutput (V : Language Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | none => [false]
  | some (x, u) => [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)]

/-- Three applications of pairing injectivity pin every quadruple component;
unary equality pins the two natural-number fields by taking lengths. -/
private lemma tmsat_quad_injective (α x : List Bool) (n t : ℕ)
    (β y : List Bool) (m s : ℕ) (he : tmsatQuad α x n t = tmsatQuad β y m s) :
    α = β ∧ x = y ∧ n = m ∧ t = s := by
  have h₁ : (α, pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) =
      (β, pairEncode y (pairEncode (List.replicate m true) (List.replicate s true))) :=
    pairEncode_injective he
  obtain ⟨hα, hrest⟩ := Prod.mk.inj h₁
  have h₂ : (x, pairEncode (List.replicate n true) (List.replicate t true)) =
      (y, pairEncode (List.replicate m true) (List.replicate s true)) :=
    pairEncode_injective hrest
  obtain ⟨hx, hlast⟩ := Prod.mk.inj h₂
  have h₃ : (List.replicate n true, List.replicate t true) =
      (List.replicate m true, List.replicate s true) := pairEncode_injective hlast
  obtain ⟨hn, ht⟩ := Prod.mk.inj h₃
  refine ⟨hα, hx, ?_, ?_⟩
  · simpa only [List.length_replicate] using congrArg List.length hn
  · simpa only [List.length_replicate] using congrArg List.length ht

/-- Given a fixed coded wrapper with the prescribed deadline, the reduction
has exactly the original NP language as its preimage.

**Proof sketch.** Forward, use the original exact-length certificate and the
wrapper's accepting verdict. Backward, nested pairing injectivity forces the
code, input, certificate length, and deadline to be precisely the emitted ones.
Completed-output uniqueness then identifies acceptance with the verifier's
verdict, even if the chosen deadline exceeds the actual halting time. -/
private lemma tmsat_reduction_correct (c : MachineCode) (L V : Language Bool)
    (C e : ℕ) (α : List Bool) (T : ℕ → ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V)
    (hM : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ e →
      (c.decode α).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T x.length)) :
    ∀ x : List Bool, x ∈ L ↔ tmsatQuad α x (C * (x.length + 1) ^ e) (T x.length) ∈ TMSAT c := by
  classical
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu, hv⟩ := (hL x).mp hx
    refine ⟨α, x, u, C * (x.length + 1) ^ e, T x.length, rfl, hu, ?_⟩
    simpa only [MultiTapeTM.indicator, if_pos hv] using hM x u hu
  · rintro ⟨β, y, u, n, t, he, hu, hs⟩
    obtain ⟨rfl, rfl, hn, ht⟩ := tmsat_quad_injective α x
      (C * (x.length + 1) ^ e) (T x.length) β y n t he
    rw [← hn] at hu
    rw [← ht] at hs
    refine (hL _).mpr ⟨u, hu, ?_⟩
    have ho := hs.output_unique (hM _ u hu)
    by_contra hv
    simp [MultiTapeTM.indicator, hv] at ho

/-- Exact unary certificate generation follows the predecessor's three-case
binary-value discipline; the library emits the same value directly.

**Proof sketch.** Coefficient zero emits the empty word. Positive coefficient
and degree zero emits its fixed unary word. Otherwise P5 uses exponent
`c-1+1=c`, whose harvested unary loop parameter is `c-1`. No value is enlarged. -/
private lemma tmsat_certificate_unary (C c : ℕ) :
    PolyTimeComputable (fun x => List.replicate (C*(x.length+1)^c) true) := by
  by_cases hC : C = 0
  · simpa [hC] using tmsat_pt_const []
  · by_cases hc : c = 0
    · simpa [hc] using tmsat_pt_const (List.replicate C true)
    · obtain ⟨M,A,hM⟩ := FinTM.computesFunInTime_polyUnary C (c-1+1)
      have he : c-1+1 = c := by omega
      rw [he] at hM
      exact ⟨M,A,c+1,hM⟩

/-- **`TMSAT` is `NP`-hard** [AB09, Theorem 2.9, hardness]: the generic
reduction — for `L ∈ NP`, send `x` to `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`.

**Proof sketch.** Let `L ∈ NP` with parameters `(C₀, c₀, V)` and certificate
length `Q n = C₀·(n+1)^(c₀)`, and, via `Complexity.mem_P_iff`, a machine `M_V`
deciding `V` within `A·(m+1)^d`. **The encoded machine**: a wrapper `M'` that,
on input `z`, parses `z` as `Turing.pairEncode x u` (the pairing parser
obligation; on non-pairs, output `[false]` — `M'` is total), assembles
`x ++ u`, and runs `M_V` relocated-and-captured, forwarding the verdict. `M'`
computes a total function within an explicit polynomial; normalize by the
audited chain `Turing.FinTM.one_work_tape_binary` (its total-function
hypothesis holds) and `Turing.exists_codeTM`, and let `α₀ := c.encode M''` be
the resulting **fixed code string** (this is why plain `Turing.MachineCode`
suffices — the audited `Complexity.HALT_NPHard` recipe). Let
`T' n` the **explicit** deadline formula below. **The reduction map**
`f x := pairEncode α₀ (pairEncode x (pairEncode 1^{Q |x|} 1^{T' |x|}))`.
`Complexity.PolyTimeComputable f` by the named obligations: emit the doubled
fixed string `α₀` from finite control (emission chains), double-and-copy `x`,
and write the two unary runs by binary countdown, under the **exact-value
discipline** of the round-1 audit (finding 3): the certificate length `Q` must
be emitted **exactly** — majorizing it changes the language (at
`C₀ = c₀ = 0` and `L = V = {[true]}`, replacing `Q = 0` by `n + 1` flips the
empty input's membership) — by cases: `C₀ = 0` emits the empty run;
`C₀ > 0, c₀ = 0` emits the fixed constant `C₀` from finite control;
`C₀ > 0, c₀ > 0` computes the exact binary value by
`Complexity.timeConstructible_poly C₀ (c₀ - 1)`. The **deadline may be
majorized** (enlarging `t` only relaxes the budget of a total machine whose
verdict is fixed): with a wrapper bound `B·(s+1)^e` (`B, e ≥ 1`) on inputs of
length `s`, normalization multiplier `K`, and `s = 2n + 2 + Q n` on the
relevant inputs, take the audit's formula — `r := max 1 c₀`,
`D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`; then
`s + 1 ≤ (C₀+3)·(n+1)^r` gives `K·(B·(s+1)^e + 1)^2 ≤ T' n` at every `n`, and
`Complexity.timeConstructible_poly D (2er - 1)` computes `T'`'s exact binary
value (`2er ≥ 1`). Output length: `|f x| = 2|α₀| + 2|x| + 2·Q |x| + T' |x| +
6`, an explicit polynomial. **Correctness**: `f x ∈ TMSAT c` iff — by
`Turing.pairEncode_injective`, which pins the quadruple's components — some
`u` with `|u| = Q n` has `M''.toFinTM.ComputesInTime (pairEncode x u) [true]
(T' n)`; by `M''`'s semantics and budget this holds iff `x ++ u ∈ V` (the
wrapper's verdict is the `V`-indicator, completed outputs are unique —
`Turing.FinTM.ComputesInTime.output_unique`), and the `NP` membership
equivalence for `L` turns "some such `u`" into `x ∈ L`. Conclude
`Complexity.NPHard` by the definition, one reduction per `L ∈ NP`.

**Continuation implementation note.** P6 validity, guarded P13 concatenation,
and W3 implement the total wrapper. Emission uses the proved unary generators
directly, in place of converting the retained exact binary witnesses back by
countdown. The certificate still follows exactly the same three-case table:
zero coefficient, zero degree, and positive coefficient/degree. The deadline
uses the unchanged in-file generator at loop parameter `2er-1` and coefficient
`D`, hence exponent exactly `2er`. The canonical §9c construction retains `x`
and assembles the two exact unary runs; P6 fixed-code pairing supplies the
outermost layer. Neither harvested generator is modified or removed. -/
theorem TMSAT_NPHard (c : MachineCode) : NPHard (TMSAT c) := by
  classical
  intro L hL
  obtain ⟨C₀, c₀, V, hV, hL⟩ := hL
  obtain ⟨A, d, M_V, hM_V⟩ := mem_P_iff.mp hV
  have hwrap : ∃ (W : FinTM Bool) (B e : ℕ), 0 < B ∧ 0 < e ∧
      W.ComputesFunInTime (tmsatWrapperOutput V) (fun s => B * (s + 1) ^ e) := by
    -- D-WRAP closed: guard P13's parse, capture the verifier on the
    -- concatenated components, and reject malformed inputs via W3.
    have hv : PolyTimeComputable
        (fun z => [MultiTapeTM.indicator (V : Set (List Bool)) z]) := ⟨M_V,A,d,hM_V⟩
    have hp := tmsat_pt_linear _ FinTM.computesFunInTime_pairValid
    have hc : PolyTimeComputable tmsatConcat :=
      tmsat_pt_linear _ FinTM.computesFunInTime_pairConcat
    have hw : PolyTimeComputable (tmsatWrapperOutput V) := by
      have h := tmsat_pt_cond hp (hv.comp hc) (tmsat_pt_const [false])
      convert h using 1
      funext z
      cases hd : pairDecode z with
      | none => simp [tmsatWrapperOutput, hd]
      | some ab => cases ab; simp [tmsatWrapperOutput, tmsatConcat, hd]
    obtain ⟨W,C,j,hW⟩ := hw
    refine ⟨W,C+1,max 1 j,Nat.succ_pos _,Nat.le_max_left _ _,fun z => (hW z).mono ?_⟩
    exact Nat.mul_le_mul (Nat.le_succ C)
      (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_right 1 j))

  obtain ⟨W, B, e, hB, he, hW⟩ := hwrap
  obtain ⟨M₁, K, hk, h₁⟩ := FinTM.one_work_tape_binary W (tmsatWrapperOutput V)
    (fun s => B * (s + 1) ^ e) hW
  obtain ⟨M'', hcode⟩ := exists_codeTM M₁ hk
  let α₀ := c.encode M''
  let r := max 1 c₀
  let D := (K + 1) * (B + 1) ^ 2 * (C₀ + 3) ^ (2 * e)
  let T' := fun n => D * (n + 1) ^ (2 * e * r)
  have hD : 0 < D :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.succ_pos _)))
      (Nat.pow_pos (by omega))
  have hexp : 1 ≤ 2 * e * r := by
    have hr : 0 < r := Nat.le_max_left 1 c₀
    have her := Nat.mul_pos he hr
    rw [Nat.mul_assoc]
    omega
  have hdeadline : TimeConstructible T' := by
    have h := timeConstructible_poly D (2 * e * r - 1) hD
    have heq : 2 * e * r - 1 + 1 = 2 * e * r := by omega
    simpa only [heq] using h
  have hcertificate := tmsat_exact_certificate_bits C₀ c₀
  have hnormalized (x u : List Bool) (hu : u.length = C₀ * (x.length + 1) ^ c₀) :
      (c.decode α₀).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T' x.length) := by
    have hrun := (hcode (pairEncode x u) (tmsatWrapperOutput V (pairEncode x u)) _).2
      (h₁ (pairEncode x u))
    simp only [tmsatWrapperOutput, pairDecode_pairEncode] at hrun
    rw [show c.decode α₀ = M'' from c.decode_encode M'']
    apply hrun.mono
    simpa only [universal_pair_length, hu] using tmsat_deadline_bound K B e C₀ c₀ x.length
  have hemit : PolyTimeComputable
      (fun x => tmsatQuad α₀ x (C₀ * (x.length + 1) ^ c₀) (T' x.length)) := by
    -- D-EMIT closed: exact unary values are assembled using §9c;
    -- the existing binary witnesses record the same exact values.
    have hq := tmsat_certificate_unary C₀ c₀
    have ht : PolyTimeComputable (fun x => List.replicate (T' x.length) true) := by
      have h := poly_unary_computes (2*e*r-1) D
      have hexact : 2*e*r-1+1 = 2*e*r := by omega
      rw [hexact] at h
      exact ⟨polyUnaryTM (2*e*r-1) D,D+5*(2*e*r)+4,2*e*r,h⟩
    have hinner := tmsat_pt_pair polyTimeComputable_id (tmsat_pt_pair hq ht)
    have houter := tmsat_pt_linear _ (FinTM.computesFunInTime_pairEncodeFixed α₀)
    exact houter.comp hinner

  exact ⟨_, hemit, tmsat_reduction_correct c L V C₀ c₀ α₀ T' hL hnormalized⟩

/-- **Theorem 2.9** [AB09]: `TMSAT` is `NP`-complete — over an effective
scheme with a polynomially bounded canonizer, the hypothesis its membership
half requires and cannot drop (round-1 audit, findings 1-2: without it, the
Argument-A scheme's `TMSAT` is `NP`-hard yet outside `NP`, so the completeness
conjunction fails).

**Proof sketch.** `Complexity.TMSAT_mem_NP` (with the same hypothesis `hc`)
and `Complexity.TMSAT_NPHard` at `c.toMachineCode`, assembled by the
definition of `Complexity.NPComplete`. -/
theorem TMSAT_NPComplete (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    NPComplete (TMSAT c.toMachineCode) := by
  exact ⟨TMSAT_mem_NP c hc, TMSAT_NPHard c.toMachineCode⟩

end Complexity

## ===== TCSlib/Complexity/TuringMachine/Nondeterministic.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic Multi-Tape Turing Machines

[AB09, §2.1.2]: a nondeterministic Turing machine (NDTM) is a standard TM with **two**
transition functions `δ₀` and `δ₁`; at every step the machine chooses which of the two to
apply. A finite run is therefore governed by a *choice word* — one bit per step — and the
run function is indexed by it. This module defines the raw machine, its choice-word
semantics in the style of the deterministic `Turing.MultiTapeTM.runFrom`, the all-branch
halting predicate that time bounds quantify over, the bundled finite layer `FinNDTM`, and
the embedding of deterministic machines. Acceptance and the class `NTIME` live one layer
up, in `TCSlib.Complexity.ClassNP.NTIME`, because they fix the binary alphabet.

## Design and deviations from [AB09]

* **Two total transition functions, `Bool`-indexed**: the single field
  `tr : Bool → …` carries [AB09]'s `δ₀` as `tr false` and `δ₁` as `tr true`. Both
  functions are total, so no configuration is ever *stuck* — every choice word of every
  length drives a complete run. (This is the load-bearing difference from a
  relational model such as cslib's `MultiTapeNTM`, surveyed and deliberately not
  ported — see the plan's decision log: with binary choice the accepting choice word
  *is* the polynomial-length certificate of [AB09, Theorem 2.6], while arbitrary
  branching relations have no canonical certificate encoding.)
* **Choice words are finite lists** (`List Bool`), consumed left to right, one bit per
  step: `runWith w cfg` is the configuration after `|w|` steps under the choices `w`.
  The alternative — infinite choice streams `ℕ → Bool` with a separate step count — is
  equivalent for every notion built here (only the first `t` bits of a stream are ever
  consulted); the list form makes the choice word a finite string that can be a
  certificate. **Design question (c) for the phase-2 audit.**
* **No `q_accept` state.** [AB09] equips NDTMs with a distinguished accepting state;
  our machines signal through their output tape, exactly as the deterministic
  development does (`Turing.FinTM.DecidesInTime` reads acceptance off the output
  `[true]`/`[false]`). Acceptance-by-output is defined in
  `TCSlib.Complexity.ClassNP.NTIME` and is **design question (a) for the phase-2
  audit**.
* **Halting is absorbing under every choice**: stepping a halted configuration is the
  identity regardless of the choice bit, mirroring the deterministic `step`. Extending
  a choice word beyond the halting time therefore never changes the reached
  configuration — the lemma `runWith_of_halt` below. This is what the exact-length
  quantifiers lean on, *directionally*: accepting witnesses pad to any larger exact
  length, and all-branch halting at a larger budget follows by splitting at the old
  one (`HaltsWithin.mono`). It does **not** make every bounded-length rewriting valid —
  "every word of length at most `t` is halted" already fails at the empty word — and
  the correct bounded readings are recorded in `TCSlib.Complexity.ClassNP.NTIME`
  (round-1 audit, finding 2).
* The model reuses the vendored configuration layer (`Turing.Cfg`, `Turing.Action`)
  unchanged: an NDTM step applies an `Action` exactly as a deterministic step does; only
  the *selection* of the action is new.

## Main definitions

* `Turing.NDTM` — the binary-choice nondeterministic machine. [AB09, §2.1.2]
* `Turing.NDTM.stepWith`, `Turing.NDTM.runWith` — one step under a choice bit; the run
  under a choice word. [AB09, §2.1.2]
* `Turing.NDTM.HaltsWithin` — every choice word of length `t` halts the machine on the
  given input; the totality condition of [AB09]'s "runs in `T(n)` time".
* `Turing.FinNDTM` — the bundled finite layer, mirroring `Turing.FinTM`.
* `Turing.MultiTapeTM.toNDTM`, `Turing.FinTM.toFinNDTM` — a deterministic machine as an
  NDTM whose two transition functions coincide.

## Main results

* `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt` — the choice-word run
  algebra (proved; pure unfoldings, the nondeterministic counterparts of the vendored
  `runFrom` lemmas).
* `Turing.NDTM.HaltsWithin.mono` — all-branch halting is monotone in the time bound.
* `Turing.MultiTapeTM.toNDTM_runWith` — the embedded deterministic machine ignores its
  choices: every choice word of length `t` reproduces `runFrom` at time `t`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, pp. 41-42.)
* cslib (https://github.com/leanprover/cslib), `MultiTape/Nondeterministic.lean` at
  commit a3747758: a relational nondeterministic model (related work, not ported — see
  `AroraBarakChapter2Plan.md`, decision log).
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A binary-choice nondeterministic multi-tape Turing machine [AB09, §2.1.2]: a
machine with **two** total transition functions, carried as the `Bool`-indexed field
`tr` — `tr false` is [AB09]'s `δ₀` and `tr true` is `δ₁`. Tapes, actions, and
configurations are exactly those of the deterministic `Turing.MultiTapeTM`; as there,
`Symbol` and `State` need not be finite at this layer (the bundled finite layer is
`Turing.FinNDTM` below). -/
structure NDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- the two transition functions, indexed by the nondeterministic choice: `tr false`
  is `δ₀`, `tr true` is `δ₁`; each maps the state, input symbol, and work-head symbols
  to an action, exactly as the deterministic transition function does -/
  tr (choice : Bool) (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace NDTM

variable {input : List Symbol} {tm : NDTM k Symbol State}

/-- One step under the choice bit `b`: apply the action selected by transition function
`tr b`, or stay put when already halted. Halting is absorbing under **every** choice —
the halted branch does not consult `b` — mirroring `Turing.MultiTapeTM.step`. -/
def stepWith (b : Bool) (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration corresponding to an input string — identical to the
deterministic initialization (blank work tapes, input head on the first symbol). -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w`, one
choice bit per step, consumed left to right: `|w|` steps in total. This is the
nondeterministic counterpart of `Turing.MultiTapeTM.runFrom`; a "branch" of the
computation tree of [AB09, §2.1.2] is the run under one choice word. -/
def runWith : List Bool → Cfg k Symbol State input → Cfg k Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => runWith w (tm.stepWith b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil {cfg : Cfg k Symbol State input} : tm.runWith [] cfg = cfg := rfl

/-- Consuming one choice bit is one step: the run under `b :: w` is the run under `w`
from the configuration one `stepWith b` ahead. -/
lemma runWith_cons {b : Bool} {w : List Bool} {cfg : Cfg k Symbol State input} :
    tm.runWith (b :: w) cfg = tm.runWith w (tm.stepWith b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the counterpart of `Turing.MultiTapeTM.runFrom_add`. -/
lemma runWith_append (w w' : List Bool) (cfg : Cfg k Symbol State input) :
    tm.runWith (w ++ w') cfg = tm.runWith w' (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- Stepping a halted configuration is the identity, under either choice. -/
@[simp]
lemma stepWith_of_halt {b : Bool} {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.stepWith b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under **every** choice word — the
counterpart of `Turing.MultiTapeTM.runFrom_of_halt`. Extending a choice word beyond the
halting time therefore never changes the reached configuration. -/
@[simp]
lemma runWith_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none)
    {w : List Bool} : tm.runWith w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt h]; exact ih

/-- The machine halts on `input` within `t` steps **along every branch**: after any `t`
nondeterministic choices the configuration is halted. This is the totality condition in
[AB09]'s "runs in `T(n)` time" (§2.1.2: *every* sequence of choices reaches the halting
state within the bound), rendered over choice words of length exactly `t`; by
`Turing.NDTM.runWith_of_halt` the exact-length quantifier already covers all longer
words, and `Turing.NDTM.HaltsWithin.mono` makes this precise. -/
def HaltsWithin (tm : NDTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Given `w` with `|w| = t' ≥ t`, split `w = w.take t ++ w.drop t`
(`List.take_append_drop`) with `|w.take t| = t` (`List.length_take`, since `t ≤ t'`).
By the hypothesis the run under `w.take t` is halted; `Turing.NDTM.runWith_append`
factors the run under `w` through it, and `Turing.NDTM.runWith_of_halt` absorbs the
remaining choices, so the state at `w` equals the halted state at `w.take t`. -/
theorem HaltsWithin.mono {tm : NDTM k Symbol State} {input : List Symbol} {t t' : ℕ}
    (h : tm.HaltsWithin input t) (hle : t ≤ t') : tm.HaltsWithin input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (tm := tm) (w.take t) (w.drop t) (tm.initCfg input)
  rw [List.take_append_drop, runWith_of_halt _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end NDTM

/-- A nondeterministic machine bundled with a finite state type, mirroring
`Turing.FinTM`: the instances are data (`Fintype`/`DecidableEq`, not `Finite`) for the
same reason as there — a machine that is to be encoded as a string must enumerate its
transition tables. All headline nondeterministic-complexity definitions
(`Turing.FinNDTM.DecidesInTime`, `Complexity.NTIME`) are stated over this layer. -/
structure FinNDTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic machine -/
  tm : NDTM k Symbol State

attribute [instance] FinNDTM.fintypeState FinNDTM.decEqState

/-- A deterministic machine as a nondeterministic one whose two transition functions
coincide: both choices apply the deterministic transition. This is the embedding behind
`DTIME ⊆ NTIME` ([AB09, §2.1.2]: a TM is an NDTM that ignores its choices). -/
def MultiTapeTM.toNDTM (tm : MultiTapeTM k Symbol State) : NDTM k Symbol State :=
  ⟨tm.q₀, fun _ => tm.tr⟩

/-- The embedded deterministic machine starts where the original does. -/
@[simp]
lemma MultiTapeTM.toNDTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNDTM.initCfg input = tm.initCfg input := rfl

/-- The embedded deterministic machine ignores its choices: running `toNDTM` under any
choice word `w` is running the original machine for `|w|` steps.

**Proof sketch.** Induction on `w` generalizing the configuration. For one step,
`Turing.NDTM.stepWith` on `toNDTM` and `Turing.MultiTapeTM.step` are the same match on
the state — halted branches are both the identity, and on a live state both apply the
action `tm.tr q …` since `toNDTM.tr b = tm.tr` for either `b`. The cons case is then
`Turing.NDTM.runWith_cons` against `Turing.MultiTapeTM.runFrom_succ_eq_step` (the step
count on the right is `|w| + 1`, `List.length_cons`). -/
theorem MultiTapeTM.toNDTM_runWith (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.runWith w cfg = tm.runFrom cfg w.length := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    rw [NDTM.runWith_cons, List.length_cons, runFrom_succ_eq_step]
    exact ih (tm.step cfg)

/-- A bundled deterministic machine as a bundled nondeterministic one — the `FinTM`
layer of `Turing.MultiTapeTM.toNDTM`, with the same tapes and state type. -/
def FinTM.toFinNDTM {Symbol : Type} (M : FinTM Symbol) : FinNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toNDTM⟩

end Turing

## ===== TCSlib/Complexity/ClassNP/NTIME.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic deciding and the classes NTIME

[AB09, §2.1.2, Definition 2.5]: a language `L` is in `NTIME T` when some binary-choice
NDTM decides it within time `c · T` — on every input, **every** branch halts within the
budget, and the input is in `L` exactly when **some** branch accepts. This module fixes
the binary alphabet (as `TCSlib.Complexity.ClassP.DTIME` does for the deterministic
classes), defines acceptance, the deciding predicate, and `NTIME`, and states the
deterministic embedding `DTIME ⊆ NTIME`.

## Design and deviations from [AB09]

* **Acceptance is by output, not by a `q_accept` state**: a branch *accepts* when it has
  halted with output exactly `[true]`. [AB09] gives NDTMs a distinguished accepting
  state; our machine model (single halting state, append-only output tape)
  distinguishes outcomes by output, and the deterministic `Turing.FinTM.DecidesInTime`
  already reads `[true]`/`[false]` off the output tape — acceptance-by-output keeps the
  two layers aligned, at the price that a branch halting with output `[]`, `[false]`,
  or any string other than the singleton `[true]` is non-accepting. Nothing constrains
  the outputs of non-accepting branches. **Design question (a) for the phase-2
  audit.**
* **The totality bound quantifies over all inputs and all branches**
  ([AB09, §2.1.2] verbatim: "for every input `x` and every sequence of nondeterministic
  choices"): `Turing.FinNDTM.DecidesInTime` demands `HaltsWithin` on **every** input —
  members and non-members alike — conjoined per input with the acceptance equivalence.
  Placing the halting quantifier per input (rather than as one global conjunct) is
  presentational; demanding it on non-members is not, and is the standard reading.
  **Design question (b) for the phase-2 audit.**
* **Exact-length choice words**: both `AcceptsWithin` and `HaltsWithin` quantify over
  choice words of length exactly `t`; the equivalent bounded-length readings differ by
  quantifier shape (round-1 audit, finding 2). For **acceptance** the bounded
  existential is equivalent: some `w` with `|w| ≤ t` reaching a halted configuration
  with output `[true]` pads with `false`-bits to exact length
  (`Turing.NDTM.runWith_of_halt`). For **all-branch halting** the bounded reading is
  prefix-shaped: every word of length `t` has a halted prefix `w.take r` with `r ≤ t`
  (forward take `r = t`; backward absorb the suffix) — **not** "every word of length
  at most `t` is already halted", which fails at the empty word against the live
  initial state. Moreover, under `HaltsWithin x t` the run of any longer word `w`
  *equals* the run of `w.take t` — the whole configuration, not merely the halting
  flag — which is what the backward (truncation) directions of `Complexity.NTIME.mono`
  and the compilation sketches use.
* As with `Complexity.DTIME`, the constant `c` in `NTIME` ranges over all of `ℕ`; the
  value `c = 0` gives the unsatisfiable budget `0` (no machine is halted at time `0`)
  and contributes nothing, matching [AB09]'s `c > 0` without a positivity side
  condition.

## Main definitions

* `Turing.FinNDTM.AcceptsWithin` — some branch of length `t` halts with output
  `[true]`. [AB09, §2.1.2: "`M(x) = 1`"]
* `Turing.FinNDTM.DecidesInTime` — all-branch halting plus the acceptance
  characterization of membership. [AB09, §2.1.2]
* `Complexity.NTIME` — the class of languages decided nondeterministically in time
  `c · T`. [AB09, Definition 2.5]

## Main results

* `Turing.FinNDTM.AcceptsWithin.mono` — acceptance is monotone in the branch length.
* `Complexity.NTIME.mono` — `NTIME` is monotone in the time bound.
* `Complexity.DTIME_subset_NTIME` — deterministic time is nondeterministic time.
  [AB09, §2.1.2]
* `Complexity.NTIME_eq_empty_of_exists_zero` — a vanishing time bound gives the empty
  class, as for `DTIME`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, Definition 2.5, pp. 41-42.)
-/

namespace Turing.FinNDTM

/-- The machine `N` *accepts* `x` within `t` steps: **some** choice word of length `t`
leaves the machine halted with output exactly `[true]`. This is [AB09, §2.1.2]'s
"`M(x) = 1`" with acceptance read off the output tape in place of the `q_accept` state
(see the deviations list; design question (a)). A branch halted with any other output —
including `[]` and `[false]` — is non-accepting. -/
def AcceptsWithin (N : FinNDTM Bool) (x : List Bool) (t : ℕ) : Prop :=
  ∃ w : List Bool, w.length = t ∧
    (N.tm.runWith w (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith w (N.tm.initCfg x)).output = [true]

/-- Acceptance is monotone in the branch length: an accepting branch stays accepting
when the choice word is extended.

**Proof sketch.** Pad the accepting word `w` to `w ++ List.replicate (t' - t) false`
(length `t'` by `List.length_append` and `List.length_replicate`, since `t ≤ t'`);
`Turing.NDTM.runWith_append` factors the padded run through the halted configuration
reached by `w`, and `Turing.NDTM.runWith_of_halt` absorbs the padding, preserving both
the halted state and the output `[true]`. -/
theorem AcceptsWithin.mono {N : FinNDTM Bool} {x : List Bool} {t t' : ℕ}
    (h : N.AcceptsWithin x t) (hle : t ≤ t') : N.AcceptsWithin x t' := by
  obtain ⟨w, hw, hhalt, hout⟩ := h
  refine ⟨w ++ List.replicate (t' - t) false, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hw, Nat.add_sub_of_le hle]
  · rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
    exact ⟨hhalt, hout⟩

/-- The machine `N` *decides* the language `L` within time `T`, nondeterministically:
on every input `x`, every branch of length `T |x|` has halted
(`Turing.NDTM.HaltsWithin` — [AB09]'s totality condition, demanded on members and
non-members alike), and `x ∈ L` exactly when some such branch accepts.
[AB09, §2.1.2 with Definition 2.5] -/
def DecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    N.tm.HaltsWithin x (T x.length) ∧ (x ∈ L ↔ N.AcceptsWithin x (T x.length))

end Turing.FinNDTM

namespace Complexity

open Turing

/-- The class of languages decidable nondeterministically in time `c · T` for some
constant `c`: a language `L` is in `NTIME T` iff some finite binary-alphabet NDTM
decides it within `c · T n` steps on inputs of length `n`, in the sense of
`Turing.FinNDTM.DecidesInTime`. [AB09, Definition 2.5] -/
def NTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInTime L fun n => c * T n}

/-- `NTIME` is monotone in the time bound.

**Proof sketch.** The same machine works at the larger budget `c · T₂ n ≥ c · T₁ n`.
All-branch halting transfers by `Turing.NDTM.HaltsWithin.mono`. The acceptance
equivalence transfers in both directions: forward by
`Turing.FinNDTM.AcceptsWithin.mono` (pad the accepting word); backward by truncation —
given an accepting word `w` at the larger budget, its prefix `w.take (c * T₁ n)` has
halted (all-branch halting at the smaller budget), and `Turing.NDTM.runWith_append` on
`w = w.take _ ++ w.drop _` with `Turing.NDTM.runWith_of_halt` shows the full run equals
the truncated one, so the truncated word already accepts. -/
theorem NTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : NTIME T₁ ⊆ NTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  refine ⟨c, N, ?_⟩
  intro x
  obtain ⟨hhalt, haccept⟩ := hN x
  have hle := Nat.mul_le_mul_left c (h x.length)
  refine ⟨hhalt.mono hle, ?_⟩
  constructor
  · intro hx
    exact (haccept.mp hx).mono hle
  · rintro ⟨w, hw, _, hout⟩
    apply haccept.mpr
    have hlen : (w.take (c * T₁ x.length)).length = c * T₁ x.length :=
      List.length_take_of_le (hle.trans_eq hw.symm)
    have hprefix := hhalt (w.take (c * T₁ x.length)) hlen
    refine ⟨w.take (c * T₁ x.length), hlen, hprefix, ?_⟩
    have hrun := NDTM.runWith_append (tm := N.tm)
      (w.take (c * T₁ x.length)) (w.drop (c * T₁ x.length)) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hprefix] at hrun
    rw [← hrun]
    exact hout

/-- **Deterministic time is nondeterministic time** [AB09, §2.1.2]: a TM is an NDTM
that ignores its choices, so `DTIME T ⊆ NTIME T`.

**Proof sketch.** Given `M` deciding `L` within `c · T n`, take
`Turing.FinTM.toFinNDTM M`. By `Turing.MultiTapeTM.toNDTM_runWith`, the run under
**any** choice word of length `t` is `M`'s deterministic run to time `t`, so: every
branch of length `c · T n` is halted because `M`'s computation has halted by then
(`Turing.FinTM.DecidesInTime` unfolded through `Turing.FinTM.computesInTime_iff`),
giving `HaltsWithin`; and some branch of that length is halted with output `[true]` iff
`M`'s output at that time is `[true]`, which by the indicator contract
(`Turing.MultiTapeTM.indicator`) holds iff `x ∈ L` — for `x ∉ L` the output is
`[false] ≠ [true]` on every branch, so no branch accepts. -/
theorem DTIME_subset_NTIME (T : ℕ → ℕ) : DTIME T ⊆ NTIME T := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, ?_⟩
  intro x
  obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp (hM x)
  have hrun (w : List Bool) :
      M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
        M.tm.runFrom (M.tm.initCfg x) w.length :=
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  constructor
  · intro w hw
    rw [hrun, hw]
    exact hhalt
  · constructor
    · intro hx
      refine ⟨List.replicate (c * T x.length) false, List.length_replicate .., ?_, ?_⟩
      · rw [hrun, List.length_replicate]
        exact hhalt
      · rw [hrun, List.length_replicate, hout]
        simp only [MultiTapeTM.indicator, if_pos hx]
    · rintro ⟨w, hw, _, hwout⟩
      rw [hrun, hw, hout] at hwout
      by_contra hx
      simp only [MultiTapeTM.indicator, if_neg hx] at hwout
      cases hwout

/-- If the time bound vanishes at even one input length, the class is empty, exactly as
for `Complexity.DTIME_eq_empty_of_exists_zero`: the initial configuration is not
halted, so all-branch halting already fails at budget `c * 0 = 0`.

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate
`Turing.FinNDTM.DecidesInTime` at the input `List.replicate n false`
(`List.length_replicate`); its `HaltsWithin` conjunct applied to the empty choice word
(`Turing.NDTM.runWith_nil`) asserts that the initial configuration is halted,
contradicting `Turing.Cfg.init`'s state `some q₀`. -/
theorem NTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : NTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro L ⟨c, N, hN⟩
  have hhalt := (hN (List.replicate n false)).1
  simp only [List.length_replicate, hn, Nat.mul_zero] at hhalt
  have hzero : (some N.tm.q₀ : Option N.State) = none := hhalt [] rfl
  cases hzero

end Complexity

## ===== TCSlib/Complexity/ClassNP/PolyTime.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time computable functions

The function class `FP` underlying every Karp reduction of [AB09, ch. 2]: a function
`f : {0,1}* → {0,1}*` is polynomial-time computable when some machine of this
development computes it within a bound `C · (n + 1)^c`. This module fixes the
polynomial normal form (`Complexity.PolyBound`), the class
(`Complexity.PolyTimeComputable`), and the closure calculus that the chapter's
reductions assemble with — identity, composition, and the output-length bound.

## Design

* **Normal form `C · (n + 1)^c`.** Chapter 1's `P` uses `n^c + 1`; for *function*
  bounds the `(n + 1)^c` shape is closed under the compositions the calculus
  performs and is a monotone majorant by construction (both forms bound the same
  class, by `Complexity.succ_pow_le` and its converse direction). The choice is a
  recorded phase-1 design question.
* **Closure lemmas are need-driven.** Only the combinators the mandatory core
  consumes are stated here; concatenation, constant prefixing, and unary padding
  arrive with the phases that first use them (plan §2), never speculatively.

## Main definitions

* `Complexity.PolyBound` — `p` is bounded by `C · (n + 1)^c`.
* `Complexity.PolyTimeComputable` — `f` is computed by some machine within a
  polynomial bound ([AB09]'s implicit class FP).

## Main results

* `Complexity.polyTimeComputable_id` — the identity is polynomial-time computable.
* `Complexity.PolyTimeComputable.output_length_le` — a polynomial-time computable
  function has polynomially bounded output length.
* `Complexity.PolyTimeComputable.comp` — closure under composition
  [AB09, proof of Theorem 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7 and Theorem 2.8.)
-/

namespace Complexity

open Turing

/-- The bound `p : ℕ → ℕ` is *polynomially bounded*: `p n ≤ C · (n + 1)^c` for some
constants `C, c`. A **numerical helper only**: the *majorant* `C (n+1)^c` is
monotone, but `p` itself need be neither monotone nor computable — which is
exactly why this predicate never appears in a class definition (phase-1 audit,
finding 1: an abstract length function can smuggle undecidable information
through length arithmetic). Class definitions use explicit formulas instead. -/
def PolyBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * (n + 1) ^ c

/-- A function on binary strings is *polynomial-time computable* when some finite
binary-alphabet machine computes it within `C · (n + 1)^c` steps on inputs of
length `n` — the function class FP implicit throughout [AB09, ch. 2]. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c

/-- The identity function is polynomial-time computable.

**Proof sketch.** `Turing.FinTM.computesFunInTime_id` supplies a machine computing
`id` within a linear bound; enlarge the bound into the `C · (n + 1)^c` normal form
pointwise via `Turing.FinTM.ComputesInTime.mono` (there is no
`ComputesFunInTime`-level monotonicity lemma — phase-1 audit, finding 9). -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_id
  refine ⟨M, C, 1, fun x => (hM x).mono ?_⟩
  simp only [Nat.pow_one]
  exact Nat.le_refl _

/-- A polynomial-time computable function has polynomially bounded output length:
`|f x| ≤ C · (|x| + 1)^c` for some constants `C, c` uniform over all inputs.

**Proof sketch.** A machine emits at most one symbol per step
(`Turing.MultiTapeTM.output_length_le`), so the completed output of a computation
within `t` steps has length at most `t`; instantiate `t` at the machine's own
polynomial budget on each input. -/
theorem PolyTimeComputable.output_length_le {f : List Bool → List Bool}
    (h : PolyTimeComputable f) :
    ∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c := by
  obtain ⟨M, C, c, hM⟩ := h
  refine ⟨C, c, fun x => ?_⟩
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
  simpa only [hout] using M.tm.output_length_le x (C * (x.length + 1) ^ c)

/-- The timed-composition budget is bounded by a polynomial of degree
`max c (c * c')`, uniformly in all natural coefficients, degrees, and lengths.

**Proof sketch.** Since `(n+1)^c ≥ 1`, the inner argument is at most
`(C+1)(n+1)^c`. Raising to `c'` gives the second term degree `c*c'`.
Enlarge both degrees to their maximum, absorb the constant term using
`(n+1)^(max c (c*c')) ≥ 1`, and distribute the common power. -/
private lemma comp_time_bound (a C c C' c' n : ℕ) :
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
      a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c (n + 1) hpos
  have hfirst : (n + 1) ^ c ≤ (n + 1) ^ max c (c * c') :=
    Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have hsecond : (C * (n + 1) ^ c + 1) ^ c' ≤
      (C + 1) ^ c' * (n + 1) ^ max c (c * c') := by
    calc
      (C * (n + 1) ^ c + 1) ^ c' ≤ ((C + 1) * (n + 1) ^ c) ^ c' :=
        Nat.pow_le_pow_left (by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_left hone _) c'
      _ = (C + 1) ^ c' * (n + 1) ^ (c * c') := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ (C + 1) ^ c' * (n + 1) ^ max c (c * c') :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (Nat.le_max_right _ _))
  calc
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
        a * (C * (n + 1) ^ max c (c * c') +
          C' * ((C + 1) ^ c' * (n + 1) ^ max c (c * c')) +
          (n + 1) ^ max c (c * c')) :=
      Nat.mul_le_mul_left a (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left C hfirst) (Nat.mul_le_mul_left C' hsecond))
        (Nat.one_le_pow _ _ hpos))
    _ = a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]

/-- Polynomial-time computable functions are closed under composition
[AB09, proof of Theorem 2.8: polynomials compose].

**Proof sketch.** Let `Mf` compute `f` within `C · (n + 1)^c` and `Mg` compute `g`
within `C' · (n + 1)^c'`. `Turing.FinTM.computesFunInTime_comp` composes the
machines with a factor-`2` overhead, running `Mg` on the intermediate output
`f x`, whose length is at most `C · (n + 1)^c` because a machine emits at most one
symbol per step (`Turing.MultiTapeTM.output_length_le`). The total budget
`2 · (C (n+1)^c + C' (C (n+1)^c + 1)^{c'} + 1)` is again of the form
`C'' · (n + 1)^{c''}` with `c'' = max c (c · c')` — the `max` covers `c' = 0`,
where the first machine's term still grows as `(n+1)^c` (phase-1 audit,
finding 7); since `(n+1)^c ≥ 1`, the whole budget is absorbed as
`a (C + C'(C+1)^{c'} + 1) (n+1)^{max c (c·c')}`. This is Theorem 2.8's
polynomial-composition observation. -/
theorem PolyTimeComputable.comp {f g : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) :
    PolyTimeComputable (g ∘ f) := by
  obtain ⟨Mf, C, c, hf⟩ := hf
  obtain ⟨Mg, C', c', hg⟩ := hg
  have hmono : Monotone (fun n : ℕ => C' * (n + 1) ^ c') := by
    intro m n hmn
    exact Nat.mul_le_mul_left C' (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) c')
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_comp hf hg hmono
  refine ⟨M, a * (C + C' * (C + 1) ^ c' + 1), max c (c * c'),
    fun x => (hM x).mono ?_⟩
  exact comp_time_bound a C c C' c' x.length

end Complexity

## ===== TCSlib/Complexity/ClassP/P.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  obtain ⟨a, M, hM⟩ := hL
  refine dtime_poly_subset_P d ⟨a * c, M, fun x => (hM x).mono ?_⟩
  calc a * T x.length ≤ a * (c * (x.length ^ d + 1)) :=
        Nat.mul_le_mul (le_refl a) (hT x.length)
    _ = a * c * (x.length ^ d + 1) := by ring

/-- The key pointwise inequality behind the padding normalization:
`(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)` for every `n` and `d`. -/
lemma succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * (n ^ d + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _)
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := Nat.mul_pow 2 n d
      _ ≤ 2 ^ d * (n ^ d + 1) := Nat.mul_le_mul (le_refl _) (Nat.le_succ _)

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content: forward, a witness for the degree-`c`
component gives a bound `a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`; backward, `succ_pow_le`
turns a `C · (n + 1) ^ d` decider into a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing
in the degree-`d` component. (`audits/phase1-findings.md`, "Polynomial-time
normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨c, hs⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, M, hM⟩ := hs
    refine ⟨2 * a, c, M, fun x => (hM x).mono ?_⟩
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 0 < (x.length + 1) ^ c := Nat.pow_pos (Nat.succ_pos _)
    calc a * (x.length ^ c + 1)
        ≤ a * ((x.length + 1) ^ c + (x.length + 1) ^ c) :=
          Nat.mul_le_mul (le_refl a) (Nat.add_le_add h1 h2)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  · rintro ⟨C, d, M, hM⟩
    refine Set.mem_iUnion.mpr ⟨d, C * 2 ^ d, M, fun x => (hM x).mono ?_⟩
    calc C * (x.length + 1) ^ d
        ≤ C * (2 ^ d * (x.length ^ d + 1)) :=
          Nat.mul_le_mul (le_refl C) (succ_pow_le x.length d)
      _ = C * 2 ^ d * (x.length ^ d + 1) := by ring

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := fun _ hL =>
  mem_P_of_dtime_le hL 1 1 fun n => by
    rw [one_mul]
    exact Nat.le_add_left 1 (n ^ 1)

end Complexity

## ===== briefs/ch2-epoch2-batchA.md =====

# Ch2 fill campaign — Epoch 2, Batch A: the `NP ⊆ EXP` enumerator

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-A`), record
  the base commit hash you branched from in `REPORT.md`, and never rebase
  onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-A.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling one proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2. Statement layer audited across
four closed gates; epoch 1 filled 27 of 59 admissions and closed its gate in
one round (`audits/ch2-epoch1-resolutions.md`). This batch is one target —
the **brute-force certificate enumerator**, [AB09, Claim 2.4] — and it is one
of the chapter's two biggest technique risks: a looping machine that lays out
candidate certificates, simulates a verifier call per round with captured
output, resets, and increments, under a timed loop invariant. The in-file
proof sketch (the audited route) names every machine obligation; the audit
record below completes the contract list. In-repo precedents, all proved:
`Turing.universalCaptureTM` (`UniversalStartup.lean` — capture/suppress/
redirect), the `Simulation.lean` lockstep gadgets, `Composition.lean`'s
buffered timed composition, and epoch 1's budget-arithmetic patterns.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/EXP.lean` — target: `NP_subset_EXP` (line 123).
  `P_subset_EXP` and `EXP_subset_NEXP` in the same file are **not yours**
  (the former is filled; the latter is epoch 3).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get` (narrowing to the order list's Mathlib
  roots is fine — the epoch-1 reports' pattern). **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (53 modules).
- Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/EXP`
  per edit, then every later module in the order list. Final: the full
  53-module sweep, **zero `error:` lines**.
- **Axiom prints**: `#print axioms Complexity.NP_subset_EXP` on the final
  fresh tree; the footprint must be **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets are fine
  (epoch-1 disposition D1) — and `sorryAx` must not appear: this batch has
  **no sanctioned admitted dependency**.

## Ground rules (binding)

1. **File ownership.** Only `EXP.lean`, and only the one target's proof plus
   `private` helpers. Shared wishes go under "Requested shared lemmas" in
   `REPORT.md` with a `private` local copy. List every new declaration — the
   epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere. Docstring sketch appendices allowed, flagged.
3. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
4. No touching sorries outside the target. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.
7. **Continuation budget**: this is a 12-point target. If your budget
   exhausts, deliver a partial zip whose `REPORT.md` states exactly which
   obligations are proved, which are stated `private` with `sorry` (allowed
   **only** in a partial delivery, each listed), and where the frontier is —
   the maintainer issues a continuation brief (the chapter-1 `universal` B2
   precedent).

## The audited route

The docstring sketch at `EXP.lean:123` is binding: evaluate the explicit
width `Q n = C(n+1)^c`; all-`false` initial candidate; per round assemble
`x ++ u`, run the verifier **captured**, test the bit, reset, increment as a
fixed-width counter; reject on overflow after the `2^(Q n)`-th round;
enumeration over **exactly** the definition's length. The private
`counterInc` layer of `ClassP/TimeConstructible.lean` is a **template, not a
citable API** — re-derive privately what you need (phase-1 finding 5).
The budget shape to land: `a · 2^(Q n) · (n + Q n + 1)^d ≤ 2^(n^e)` for a
fixed `e`, small lengths absorbed into `DTIME`'s constant.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/ch2-phase1-round3-findings.md` (via
`audits/ch2-phase1-resolutions.md`):

> **Enumerator: completeness of the repaired obligation list.** I found no
> further unnamed substantive construction obligation at this sketch's
> level. A fill agent will need auxiliary lemmas, but they fall under the
> named contracts:
>
> | Named obligation | Contract needed in the fill |
> |---|---|
> | Width evaluation and initialization | Compute `Q(n)`, retain `x`, and construct the initial all-false candidate of exactly that width. Initialization has polynomial cost. |
> | Fixed-width increment and overflow | Visit every width-`Q(n)` word once until acceptance or exhaustion; preserve width, and terminate after the final rejection. For width zero, process the unique empty word before reporting exhaustion. |
> | Buffering, retention, and verifier-call simulation | Present exactly `x++u` as the simulated read-only input with correct initial head/boundary behavior, while protecting the retained instance and candidate. |
> | Capture and return | Suppress every physical verifier emission; capture its bit, including an emission on the halting transition; return control instead of halting the enumerator. Test the updated captured bit. Emit exactly one final answer. |
> | Restart | Restore verifier control, simulated heads, work tapes, and captured bit. Clear the bounded visited region and restore buffer/head bookkeeping within a polynomial budget. |
> | Timed loop invariant | Combine candidate coverage, correct calls, empty real output before finalization, and polynomial call/reset cost into termination, the singleton-output decision contract, and the stated exponential budget. |
>
> The precedent is real: `UniversalStartup.lean:405`, `universalCaptureTM`,
> sets physical emission to `none` while storing the source emission, and
> turns a source halt into a live administrative state before transfer. In
> particular, the halting action's output is captured before transfer. That
> wrapper stores output on a tape and transfers to its particular
> interpreter; the enumerator must implement the named finite-control-bit
> variant and restart behavior. The repaired sketch correctly calls it a
> **pattern**, rather than claiming it supplies the whole loop.
>
> The two-round adversarial trace now behaves correctly: a rejected first
> candidate contributes no physical `[false]`; an accepted second candidate
> still contributes no physical verifier output; finalization emits only
> `[true]`. If all candidates reject, finalization emits only `[false]`.
> Capturing first and then examining the simulated halt covers a decider
> that emits its only bit on its last transition.

Your `REPORT.md` must map each of the six contract rows to the lemma(s)
discharging it.

## Out-of-scope sorries you will see (leave untouched)

`EXP_subset_NEXP` (your own file — epoch 3); `mem_NP_iff_exists_length_le`,
`HALT_NPHard`, `HALT_not_mem_NP` (2C, concurrent); the `Nondeterminism.lean`
compilations (2B); the `TMSAT.lean` four (2D); everything in E3/E4
(`SAT.lean`, `Tautology.lean`, `CookLevin/*`).

## REPORT.md checklist

- [ ] Target filled; the six-contract mapping table.
- [ ] Base commit hash recorded; new declarations listed (public: none
      expected; privates all).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:` lines) + axiom print (at most the
      standard triple; no `sorryAx`).
- [ ] Diff touches only `EXP.lean`.

## Known pitfalls at this pin (hard-won)

- `Function.update_of_ne` (not `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right`/`dite_eq_left` don't exist (`split <;> simp <;> omega`).
- After `cases hs : cfg.state`, `dsimp only` before rewriting.
- Avoid bare `simp` with folded forms (`initCfg` is `@[simp]`).
- `omega` needs beta-reduced, non-`Fin`-projection goals.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`/`…_step` peel opposite
  ends; `Cfg.inputSymbol` is a double `dite`; work tapes are ℤ-indexed
  `Option Symbol` via `Function.update`; `moveInputPos` clamps.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]`.
- For `2^(Q n)`-round budgets: `Nat.one_le_two_pow`, `Nat.pow_le_pow_right`,
  and epoch-1's `comp_time_bound` pattern (private; re-derive what you need).

## ===== briefs/ch2-epoch2-batchB.md =====

# Ch2 fill campaign — Epoch 2, Batch B: the Theorem-2.6 compilations

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-B`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-B.zip` with `REPORT.md`, the full modified source file, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

You are filling the two directions of [AB09, Theorem 2.6] — the equivalence
of the verifier-certificate and nondeterministic-machine definitions of
`NP` — plus their one-line assembly. Statement layer audited (four closed
gates); epoch 1 closed in one round and proved the NDTM run calculus your
proofs will consume (`runWith` algebra, `AcceptsWithin.mono`,
`HaltsWithin.mono`, `toNDTM_runWith`, all in the tree, proved). The two
directions are mirror-image machine constructions: ⊆ simulates a **fixed**
NDTM deterministically with the choice word read from the certificate
suffix; ⊇ guesses the certificate bitwise and runs the verifier machine
relocated-and-captured. Both docstring sketches name every obligation; the
phase-2 audit's invariant tables below are binding.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `ntime_poly_subset_NP` (line 101, 10 pts)
  2. `NP_subset_iUnion_NTIME` (line 132, 8 pts)
  3. `NP_eq_iUnion_NTIME` (line 142, 1 pt — antisymmetry of 1 and 2)

  The padding cluster in the same file (`ntime_expPow_subset_NEXP`,
  `NEXP_subset_iUnion_NTIME`, `NEXP_eq_iUnion_NTIME`,
  `EXP_eq_NEXP_of_P_eq_NP`, `P_ne_NP_of_EXP_ne_NEXP`) is **epoch 3 — not
  yours**.

## Environment and verification

As the epoch-1 briefs: pinned toolchain, `lake exe cache get` once,
**never `lake build`**; bootstrap the 53-module order list once; iterate
`bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/Nondeterminism`
plus the later modules; final full sweep with zero `error:` lines.
**Axiom prints** for the three targets: **at most**
`[propext, Classical.choice, Quot.sound]` (subsets fine — disposition D1);
`sorryAx` must not appear — this batch has **no sanctioned admitted
dependency** (everything cited by the sketches is proved: `mem_P_iff`,
`mem_P_of_dtime_le`, `succ_pow_le`, the epoch-1 run calculus).

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4, full force): exclusive ownership of
the one file; helpers `private`, all new declarations listed; statement
freeze with escalation over alteration; no out-of-scope sorries touched;
docstrings stay; precise imports. **Continuation budget**: 19 points
combined; if exhausted, partial delivery per the B2 precedent with the
frontier stated precisely (any `sorry` in a partial delivery listed, allowed
only there).

## Binding rule inherited from the phase-2 audit

**No untimed composition and no bare computability substitutions**
(`audits/ch2-phase2-findings.md`, note 3): every machine step of both
compilations carries its explicit time bound through the timed interfaces;
nothing may route through `exists_comp_partial` or an untimed
`Computes`-level argument.

## Inherited invariant tables (verbatim; binding on the fill)

From `audits/ch2-phase2-findings.md`, for the ⊆-direction simulation
(`ntime_poly_subset_NP`, obligation (iii)–(v)):

> | Component | Required behavior and adversarial check |
> |---|---|
> | Source input | With shifted source head position `p`, read blank at `p=0,n+1`, and otherwise read `x[p−1]`. Update `p` by the source `moveInputPos`, clamping to `0,…,n+1`. A move to the right boundary must not expose the first certificate bit. Repeated outward moves must remain clamped, so a later inward move returns correctly. Initial position is 1 even when `x=[]`. |
> | Choice tape | Before source step number `j`, use exactly the certificate bit at position `j`. Administrative simulator transitions do not consume source choices. A halted source remains unchanged; either finishing the clock with absorbed steps or stopping early preserves the verdict. |
> | Source state and tapes | Store the fixed machine's finite state in finite control and keep its work tapes separate from counters, choice storage, and buffers. Simulation bookkeeping must not alter the represented source configuration. |
> | Output | Suppress physical output during simulation. Capture every source emission, including an emission on the halting transition, before testing the final buffer. Emit exactly one verifier decision bit. A halted output `[true,false]`, `[]`, or `[false]` rejects; a live output `[true]` also rejects. |

And for the ⊇-direction (`NP_subset_iUnion_NTIME`), the audit's
**adversarial reconstruction: certificates to choice words** — its five
steps are the binding branch-correspondence contract:

> 1. Compute the input length and the explicit `Q(n)`; initialize the guess
>    countdown. At each guess-writing transition, the current choice bit is
>    written as the next certificate bit. All intervening transitions ignore
>    their choice bit. The countdown and phase control are separate from
>    guessed data, so the times of the guess-writing transitions depend on
>    the input length, not their values.
> 2. For every `u` of length exactly `Q(n)`, assign its successive bits to
>    those guess-writing positions of a branch word and set unused choices
>    arbitrarily. This realizes `u`. Conversely, every sufficiently long
>    branch word yields exactly one such `u`, because precisely `Q(n)`
>    writes occur. Thus the construction has both witness coverage and
>    witness extraction; it does not incorrectly equate the first `Q(n)`
>    physical choices with the certificate. If `C=0`, there are no
>    guess-writing positions and the sole certificate is `[]`.
> 3. Assemble `x++u` and start the verifier from its proper initial
>    configuration with blank simulated work tapes, empty captured output,
>    and virtual input head 1. Its virtual read-only input is the assembly
>    tape, with the corresponding length's boundary guard and clamping. The
>    two NDTM tables coincide throughout this simulation. Capture output and
>    emit a single final verdict. The deterministic verifier's totality
>    holds for every assembled string, so every branch terminates, whether
>    or not `x∈L`.
> 4. A branch accepts exactly when its extracted certificate satisfies
>    `x++u∈V`; existential branch acceptance is therefore equivalent to
>    membership in `L`. Extend a terminated branch to the declared common
>    budget by absorption. Conversely, every branch at that budget has
>    completed the construction and yields a legitimate certificate. The
>    later verifier phase may have certificate-dependent running time; the
>    needed assertion is a **common upper bound**, not equal actual halting
>    times.
> 5. For fixed positive constants `K,r` absorbing arithmetic, assembly, and
>    simulation costs, a bound of the form `H(n) ≤ K(n+Q(n)+1)^r` suffices.
>    It can incorporate any fixed-degree bookkeeping cost. Put
>    `e = r·max(1,c)`. Then, at every `n`,
>    `n+Q(n)+1 ≤ (C+1)(n+1)^{max(1,c)}` and
>    `H(n) ≤ K(C+1)^r (n+1)^e ≤ K(C+1)^r 2^e (n^e+1)`.

Your `REPORT.md` must map the table rows and the five steps to the lemmas
discharging them.

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3, listed above);
`NP_subset_EXP` (2A, concurrent); `mem_NP_iff_exists_length_le` and the
HALT pair (2C); the `TMSAT.lean` four (2D); everything in E3/E4.

## REPORT.md checklist

- [ ] Three targets filled in order; the invariant-table and five-step
      mappings.
- [ ] Base hash recorded; all new declarations listed.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints (at most the triple; no
      `sorryAx`).
- [ ] Diff touches only `Nondeterminism.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchB.md` §pitfalls, same pin), plus:
- The two NDTM transition tables coincide outside the guessing phase —
  make that a definitional fact of your construction, not a lemma fought
  after the fact.
- `Turing.FinNDTM.AcceptsWithin.mono` (proved, epoch 1) does the final
  budget-padding; don't re-derive absorption.
- Phase boundaries must be input-length-functions only; any
  value-dependence of timing breaks witness extraction (step 2).

## ===== briefs/ch2-epoch2-batchC.md =====

# Ch2 fill campaign — Epoch 2, Batch C: Exercise 2.1 and the HALT pair

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-C`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-C.zip` with `REPORT.md`, the full modified sources, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

Three targets. **Exercise 2.1** (`mem_NP_iff_exists_length_le`) is the
audited equivalence between the exact-length concatenation form of `NP` and
the bounded-length paired form — its reverse construction was built *by the
auditor* across three rounds and transcribed into the docstring; your job is
to follow it, not redesign it. The **HALT pair** rides on `NP_subset_EXP`
(batch 2A, concurrent — see the sanctioned-dependency rule below): hardness
by embedding one fixed code via the audited control-modification recipe, and
non-membership by the decidability contradiction. Epoch 1's calculus
(`compl_mem_P`, `mem_P_of_polyTimeReducible`, …) and Chapter 1's machines
(`one_work_tape_binary`, `exists_codeTM`, `pairEncode` machinery) are proved
and at your disposal.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassNP/NP.lean` — `mem_NP_iff_exists_length_le`
  (line 131, 8 pts) **only**.
- `TCSlib/Complexity/ClassNP/Reductions.lean` — `HALT_NPHard` (line 180,
  6 pts) and `HALT_not_mem_NP` (line 206, 4 pts) **only**.

## Environment and verification

As the epoch-1 briefs: pinned toolchain; `lake exe cache get` once; **never
`lake build`**; bootstrap the 53-module list; iterate per owned module plus
the later modules; final full sweep, zero `error:` lines.
**Axiom prints**: at most `[propext, Classical.choice, Quot.sound]`
(subsets fine — disposition D1). **Sanctioned `sorryAx`, this batch only:**
`HALT_NPHard` and `HALT_not_mem_NP` may show `sorryAx` **solely** through
`Complexity.NP_subset_EXP` (batch 2A's concurrent target — rely on its
frozen statement; at epoch merge the dependency closes, as epoch 1's did).
`mem_NP_iff_exists_length_le` must be clean. Any other `sorryAx` root is a
defect; verify the root as batch E1-A did (kernel-environment traversal or
equivalent) and say so in `REPORT.md`.

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4): exclusive ownership, named targets
only; `private` helpers, all listed; statement freeze, escalation over
alteration; no out-of-scope sorries; docstrings stay; precise imports.
Combined 18 points — continuation per the B2 precedent if needed.

## Targets and their binding routes

1. **`mem_NP_iff_exists_length_le`** (NP.lean:131). The docstring carries
   the full audited construction; it is binding, in particular:
   - (⇒) the paired verifier with the **same** bound; the `pairDecode`
     grammar scan; the length-equality check against the explicit formula.
   - (⇐) exact length `R n = (C+1)(n+1)^c` — this coefficient/degree choice
     is the **repaired** one (round-2 finding 1 refuted `C(n+1)^c + 1`);
     the marker/strip discipline: pad to `u ++ [true] ++ false-run`, split
     at the **last** `true`, and *reject when no length-equation solution
     exists* (round-3 finding 1 — e.g. `y = []`).
   - Inherited verbatim from `audits/ch2-phase1-round3-findings.md`:
     > These checks also show why the original-bound test remains
     > necessary: the larger region can contain a marker after too many
     > witness bits. Merely fitting inside `R(n)` does not authorize that
     > witness.
     So the verifier **must** re-check `|u| ≤ C(n+1)^c` after stripping.
   - The audited edge cases to keep provable: `C = 0`, `c = 0`, `x = []`,
     `u = []`, all-`false` region, malformed strings.
2. **`HALT_NPHard`** (Reductions.lean:180). The docstring's four-step
   repaired construction (finding 6) is binding: total exponential decider
   from `NP_subset_EXP` (statement; sorried until merge) →
   `one_work_tape_binary` (legal: total) → the control modification
   (remember the emitted bit **including a bit emitted on the halting
   transition**; halt iff `true`, else enter the stationary live loop) with
   its own run/halting lemma → `exists_codeTM`, fixed `α`, and the
   emit-then-copy prefix machine (`2|α| + |x| + 3` steps; `pairDiagTM` is
   the diagonal precedent, not this function). Only
   `Turing.MachineCode.decode_encode` may be used of the scheme — the
   statement quantifies over **every** `MachineCode`.
3. **`HALT_not_mem_NP`** (Reductions.lean:206). The decidability
   contradiction chain exactly as sketched; note the docstring's
   **proof-route restriction** paragraph is load-bearing audit history —
   do not "improve" the statement's generality (that is a recorded
   human-review question, not a fill decision).

## Out-of-scope sorries you will see (leave untouched)

`NP_subset_EXP`, `EXP_subset_NEXP` (EXP.lean — 2A / epoch 3); the
`Nondeterminism.lean` compilations and padding cluster (2B / epoch 3); the
`TMSAT.lean` four (2D); everything in E3/E4.

## REPORT.md checklist

- [ ] Three targets filled; for Ex 2.1, a line per audited edge case saying
      where it is discharged; for HALT, the control-modification lemma
      named.
- [ ] Base hash recorded; new declarations listed.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints, with the two sanctioned
      `NP_subset_EXP`-rooted `sorryAx` cases called out and root-verified.
- [ ] Diff touches only the two owned files, only the named targets.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchA.md` §pitfalls, same pin), plus:
- `pairEncode`/`pairDecode`: the doubled-prefix grammar is Chapter 1's;
  its proved lemmas (`pairEncode_injective`, `decode_encode`,
  `HALT_pairEncode_eq_true_iff`) are the citable API — do not re-derive.
- Splitting at the **last** `true`: `List.getLast?`/reverse-find patterns
  need care with `beq` vs `=`; keep the strip function `private` with its
  own spec lemma.
- `n ↦ n + R n` strict monotonicity is the uniqueness engine for the
  split search — prove it once, `private`, reuse in both directions.
- The stationary live loop state: one state, no emission, no movement,
  same state — its non-halting run lemma is two lines by induction; don't
  entangle it with the capture machinery.

## ===== briefs/ch2-epoch2-batchD.md =====

# Ch2 fill campaign — Epoch 2, Batch D: TMSAT and the timed_universal bridge

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-D`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-D.zip` with `REPORT.md`, the full modified sources, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

The epoch's heavy batch (30 points; **continuation budget anticipated** —
the chapter-1 `universal` B2 precedent; see ground rule 7). Four targets:
polynomial time-constructibility, `TMSAT ∈ NP`, `TMSAT` `NP`-hardness, and
their completeness assembly — [AB09, Theorem 2.9]. This batch also carries
the campaign's **one planned mid-fill statement addition**: a public
quantitative bridge exposing `timed_universal`'s constant, specified by the
phase-3 audit and governed by the protocol below. Chapter 1's
`timed_universal`, `universal`, `one_work_tape_binary`, `exists_codeTM`,
the `MachineCode`/`EffectiveMachineCode` layer, and epoch 1's calculus are
all proved and citable.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/TMSAT.lean` — targets, in order:
  1. `timeConstructible_poly` (line 120, 7 pts)
  2. the **bridge statement** (see protocol below), then `TMSAT_mem_NP`
     (line 182, 12 pts)
  3. `TMSAT_NPHard` (line 228, 10 pts)
  4. `TMSAT_NPComplete` (line 240, 1 pt)

## The bridge protocol (read carefully — this is the unusual part)

The phase-3 audit requires `TMSAT_mem_NP` to rest on a **new public
quantitative bridge** for the Chapter-1 simulator. Inherited **verbatim**
from `audits/ch2-phase3-resolutions.md` (note 3 disposition):

> the fill obligation is pinned as the auditor specifies — a public
> quantitative bridge for **one simulator chosen before the code and
> input**, preserving both the success and timeout clauses of
> `timed_universal`; the suggested bridge form
> `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoids importing `PolyBound`
> into Chapter 1 and is recorded for the fill brief, which must not infer a
> bound on the existing statement's arbitrary existential witness.

Mechanics, under the file-ownership rule:

1. **State** the bridge in `TMSAT.lean`, clearly sectioned, with a
   docstring flagging it as *the phase-3-mandated bridge statement, new
   public surface, for the epoch-2 audit*. The quantifier shape is binding:
   the simulator (and its constant) is fixed **before** the code `α` and
   the input — never per-(α, input); both the success clause and the
   timeout clause of `timed_universal` must be preserved; the suggested
   constant form above is a suggestion, any explicit closed form in
   `|α|`, `canonizerTime(|α|)`, and `(t+1)²`-shape is acceptable if it
   provably works.
2. **Prove it.** The intended route is re-running `timed_universal`'s
   construction quantitatively, from `Universal.lean`'s **public** API. You
   must NOT derive it by bounding the existing statement's existential
   witness — that inference is unsound (the witness is arbitrary) and the
   audit explicitly forbids it.
3. If the public API is insufficient (the proof needs `Universal.lean`
   internals), **escalate**: state the bridge, leave its proof `sorry`
   (allowed only for this one declaration, prominently reported), record
   precisely which internal fact is needed, and proceed with
   `TMSAT_mem_NP` **on top of the stated bridge**. The maintainer then
   handles the Chapter-1-side addition serially at epoch merge, flagged
   for its own audit — Chapter-1 files are not yours to modify.
4. The bridge must not import `PolyBound` (or any Chapter-2 notion) into
   anything Chapter-1-shaped; it lives in `TMSAT.lean` and speaks only
   Chapter-1 vocabulary plus explicit arithmetic.

## Binding disciplines inherited from the phase-3 records

- **`PolyBound` budget chain** (`TMSAT_mem_NP`): the certificate length and
  the verifier budget chain through `hc : PolyBound c.canonizerTime`
  explicitly; both the success and timeout clauses of the bridge are used —
  a candidate that runs out of deadline must *reject*, not diverge.
- **Exact-value emission discipline** (`TMSAT_NPHard`; round-1 finding 3,
  carried in the docstring): the certificate length `Q` is emitted
  **exactly**, by the docstring's three-way case split (`C₀ = 0` → empty
  run; `C₀ > 0, c₀ = 0` → fixed constant from finite control;
  `C₀ > 0, c₀ > 0` → `timeConstructible_poly C₀ (c₀ - 1)`). Majorizing `Q`
  changes the language — the docstring's `C₀ = c₀ = 0` counterexample is
  the audit's own.
- **Deadline majorization formula** (same docstring, binding): `r := max 1
  c₀`, `D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`, computed
  exactly by `timeConstructible_poly D (2er - 1)`. The deadline **may** be
  majorized; the certificate length may **not**.
- The docstring sketches of all four targets are the audited routes; your
  `REPORT.md` maps each named obligation (pairing parser, wrapper
  totality, relocation-and-capture, emission chains, binary countdowns,
  `pairEncode_injective` pinning) to its discharging lemma.

## Environment and verification

As the epoch-1 briefs: pinned toolchain; `lake exe cache get`; **never
`lake build`**; bootstrap the 53-module list; iterate
`bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/TMSAT` plus the
later modules; final full sweep, zero `error:` lines. **Axiom prints** for
the four targets **and the bridge**: at most
`[propext, Classical.choice, Quot.sound]` (subsets fine — disposition D1);
`sorryAx` only in the single escalation case of bridge-protocol step 3, and
then rooted **only** at the bridge statement (verify the root; report it).

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4): exclusive ownership of
`TMSAT.lean`; `private` helpers, every new declaration listed (the bridge
is deliberately **public** — the one exception, mandated above); statement
freeze on all existing declarations; escalation over alteration; no
out-of-scope sorries; docstrings stay; precise imports. Rule 7,
**continuation**: at 30 points, if the budget exhausts, deliver a partial
zip stating the frontier exactly (which obligations proved, which stated
with listed `sorry`s — allowed only in a partial delivery); the maintainer
issues a continuation brief.

## Out-of-scope sorries you will see (leave untouched)

`NP_subset_EXP` / `EXP_subset_NEXP` (2A / epoch 3);
`mem_NP_iff_exists_length_le` + the HALT pair (2C); the
`Nondeterminism.lean` compilations and padding (2B / epoch 3); everything
in E3/E4 (`SAT.lean`, `Tautology.lean`, `CookLevin/*`).

## REPORT.md checklist

- [ ] Four targets + the bridge: filled/stated, with the obligation-to-lemma
      map and the exact bridge constant you proved.
- [ ] Base hash recorded; new declarations listed — the bridge flagged as
      the mandated public addition.
- [ ] Requested shared lemmas / escalations — or "none"; bridge-protocol
      step 3, if taken, documented with the missing internal fact.
- [ ] Final sweep log tail + axiom prints (at most the triple; `sorryAx`
      only per the bridge escalation, root-verified).
- [ ] Diff touches only `TMSAT.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchA.md` §pitfalls, same pin), plus:
- `timed_universal`'s statement shape: destructure its success/timeout
  disjunction before quantitative work; do not let `rcases` discard the
  timeout clause you must preserve in the bridge.
- `canonizerTime` is a function of `|α|`, not of `α` — keep the bridge's
  constant a function of lengths only.
- Unary-run emission: `List.replicate` bookkeeping under binary countdown;
  the epoch-1 `takeTrues_replicate` pattern (private, batch 1D) is the
  shape, not a citable API.
- `pairEncode` nesting order in the quadruple is
  `pairEncode α₀ (pairEncode x (pairEncode 1^Q 1^T'))` — get the
  associativity direction from the statement, not from memory.
- Budget normalizations: epoch 1's `comp_time_bound` is private; re-derive
  the `(s+1)^e`-absorption you need as your own private lemma.

## ===== briefs/ch2-e2cont-batchA.md =====

# Ch2 fill campaign — E2 continuation, Batch A: discharge `enumMachine_contracts`

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-A`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2cont-A.zip`, **flat** (`SHA256SUMS` at the root), with
  `REPORT.md`, the full modified source, the `git format-patch` series, a
  git bundle, the final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchA.md` and the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchA.md`) remain binding context. The
enumerator batch reduced `NP_subset_EXP` to the **single admitted private
`enumMachine_contracts`** (`TCSlib/Complexity/ClassNP/EXP.lean`, the
file's one in-scope `sorry`, ≈ line 764). Since then the campaign built,
audited (three adversarial statement rounds + a proof round, both gates
CLOSED), and fully proved a **machine-construction library**:
`TCSlib/Complexity/TuringMachine/Build/{Convention,Wrappers,Loop,
Primitives}.lean` — 23 public contracts, zero admissions. Your fill is
its flagship customer: **the audited route for `enumMachine_contracts`
is an instantiation of `Turing.FinTM.exists_loopCfgTM`**, certified
exactly at the customer's statement by the infra round-3 audit
(`audits/ch1-infra-r3-findings.md`, item 5: terminal index
`2^w = R + 1`, bounded orbit bridge, budget domination — "no
customer-statement edit or replacement decider theorem is needed") and
recorded in `machine-library-design.md` §9b–§9c. Read those two records
first; they are the route, and they are binding.

## Owned file and target

- `TCSlib/Complexity/ClassNP/EXP.lean` — one target: the private
  `enumMachine_contracts` (7 pts). Its statement is **frozen** (it is the
  audited continuation interface; the outer `NP_subset_EXP` proof already
  consumes it). On completion, `NP_subset_EXP`, `HALT_NPHard`, and
  `HALT_not_mem_NP` all print the clean standard triple — your REPORT
  includes all three prints.

## The binding route (§9b/§9c + round-3 item 5)

Write `w := C * (x.length + 1) ^ c`. Instantiate `exists_loopCfgTM` with:

- `Inv x s := s.length = w` — the exact-width invariant;
- `s0 x := List.replicate w false`; `stepF x s := (incFixed s).getD s`
  (overflow stalls, preserving width — `hInvStep` is immediate);
- `acceptF x s` := the verifier's verdict on `x ++ s`, realized inside
  the body by a **captured run of `MV`** (the hypothesis machine);
- fuel `R n := 2 ^ w - 1`: `Nat.bits (2 ^ w - 1) = List.replicate w true`
  (prove this identity as a private bridge lemma), so `hF` is discharged
  by the library's `computesFunInTime_polyUnary C c` **directly** — the
  fuel machine is a catalog instance;
- the **body machine** is your construction: from the seam (candidate on
  tape 0, scratch blank), assemble `x ++ s` on a buffer, run `MV`
  relocated-and-captured (`Turing.capture_run` with your controller as
  host; the proved `pairMapTM`/`timedCondTM` layers in `Build/` are
  in-tree instantiation templates), read the verdict; on acceptance halt
  `[true]`; on rejection restore scratch (the assembly buffer's extent is
  known, `n + w`), increment the candidate in place (the `incFixed`
  carry discipline; the superseded in-file `enumCarry*` lemmas may be
  consulted as templates but see the no-touch rule below), and return to
  the seam — positive time, anchor-free interior, per the loop contract.

Then translate the loop conclusion onto the frozen statement: the orbit
bridge `∀ i < 2^w, (stepF x)^[i] (s0 x) = enumWord w i` by induction from
the **in-file, proved** `enumWord_zero`, `enumInc_word`, and the
`incFixed = enumInc` equality (round-2 vocabulary note; both definitions
are in scope here); the configuration family and per-round clauses map
index-for-index (`cfg (2^w)` is the exported terminal); the budget
`b * (n + w + 1) ^ e` dominates `c' * (T n + 1)` once your body envelope
`T` is a polynomial in `n + w` — round-3 item 5 carries the full
derivation including width zero. Follow it; do not re-derive a different
translation shape.

## Rules on the superseded in-file privates

`EXP.lean` contains the checkpoint's `enumCarryTM`/`enumCaptureTM`/
`enumLoop_run` families, now superseded by the library. **You may ignore
them or cite them (they are proved and in-file); you must not remove,
rename, or modify them** — deduplication is a recorded E5 closure task.
Your new helpers are `private`, named distinctly, and listed.

## Sanctioned `sorryAx`

**None.** Everything this fill consumes is proved: the full library, the
in-file enumeration semantics, Chapter 1. On completion the file's only
remaining admission is the out-of-scope `EXP_subset_NEXP` (epoch 3).

## Environment, ground rules, verification

As the original E2 brief, with one update: the committed module order is
now **57 modules** (`scripts/ab_ch1_module_order.txt` — the four `Build/`
modules joined it). Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`;
mathlib `029db123ddaa`); `lake exe cache get` once; **never
`lake build`**; bootstrap the 57-module order; iterate
`TCSlib/Complexity/ClassNP/EXP` plus later modules; final full fresh
57-module sweep, zero `error:` lines. Exclusive ownership; statement
freeze absolute; escalation over alteration; docstrings stay
(append-only notes); kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the committed
template). 7 points; continuation per the B2 precedent if exhausted.

## Out-of-scope sorries you will see (leave untouched)

`EXP_subset_NEXP` (epoch 3); `mem_NP_iff_exists_length_le` (2C-cont,
concurrent); the `Nondeterminism.lean` cluster (2B-cont + epoch 3); the
`TMSAT.lean` `D-*` sites (2D-cont, concurrent); everything in E3/E4
files.

## REPORT.md checklist

- [ ] `enumMachine_contracts` proved; the instantiation mapped
      hypothesis-by-hypothesis (`hF` via the catalog fuel instance with
      the bits-identity bridge; `hInv0`/`hInvStep`; `hstart`; `hround`
      with the capture, restore, and increment phases named) and the
      conclusion-translation steps mapped to round-3 item 5's derivation.
- [ ] Axiom prints: `enumMachine_contracts`, `NP_subset_EXP`,
      `HALT_NPHard`, `HALT_not_mem_NP` — all at most the standard
      triple, root-verified empty.
- [ ] Base hash; all new private declarations listed; final file size
      (the file has a recorded 600-line-target overrun; report the new
      figure).
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `EXP.lean`; archive flat.

## Known pitfalls at this pin

The original E2-A list carries over verbatim, plus:
- `exists_loopCfgTM`'s round hypothesis demands `0 < t` and the
  strict-interior anchor clause — your restore phase is part of the
  round, not free.
- `Nat.bits (2^w - 1)`: prove the replicate identity by induction on
  `w`; do not unfold `Nat.bits` numerically.
- The orbit stalls at the all-true word only **beyond** fuel — within
  fuel, `incFixed` always succeeds; keep the `getD` fallback out of the
  bridge's induction (it never fires for `i < 2^w - 1`... and at the
  last point the bridge needs no successor).
- The library seam pins the input head at 1; your assembly scans must
  rewind it before the seam return (`timed_rewind`'s pattern in
  `Build/Wrappers.lean` is the proved template).
- Budget translation: choose your body envelope as a polynomial in
  `n + w + 1` from the start; round-3 item 5 shows `b = K(A+1)`,
  `e = D` — pick coefficients once, after `C, c, a, d` and before `x`.

## ===== briefs/ch2-e2cont-batchB.md =====

# Ch2 fill campaign — E2 continuation, Batch B: the Theorem-2.6 compilations

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-B`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-B.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchB.md` is **binding in full** — in
particular its verbatim phase-2 invariant table and the five-step
certificates↔choice-words reconstruction contract, and the no-untimed-
composition rule. The checkpoint
(`audits/ch2-epoch2-agent-reports/batchB.md`) banked the certificate
equivalence and two proved prepared-configuration phases (`choiceCore`,
the native simulation with exact time `|u| + 1`; `choiceCopy`, the
three-tape copier) and reduced target 1 to the single goal
`choiceVerifier N (2*a) c ∈ P`. Since then the campaign shipped the
fully proved **machine-construction library**
(`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
admissions; statement and proof gates both CLOSED) — the startup, split,
capture, branch, and decision glue your predecessor's frontier list
named are now library calls.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `ntime_poly_subset_NP` (6 pts): close `choiceVerifier ∈ P`.
     Library route: the unique split is
     `computesFunInTime_splitSolve` at the batch's own length equation
     (`i + C'·(i+1)^e = total` with your coefficient/degree — the
     split-search contract's shape; connect to your private
     `certificateSplit` by a semantic bridge lemma, minding that the
     library's `solveSplit` convention differs by the recorded
     coefficient shift, round-2 vocabulary note); guard malformed
     inputs with `pairValid`-style staging or your split's failure
     branch; relocate-and-capture the **proved** `choiceCore` phase
     from its prepared configuration (the startup your predecessor
     listed as missing is exactly what `Turing.capture_run` +
     the `Build/Wrappers.lean` host templates + `timed_rewind`'s
     pattern now provide); finish with the decision glue
     (`mem_P_of_dtime_le`/`mem_P_iff`).
  2. `NP_subset_iUnion_NTIME` (8 pts): the ⊇-direction NDTM
     construction. The **nondeterministic guessing table and the
     branch-correspondence argument remain bespoke by design** (the
     library covers deterministic machines only — D5's recorded scope);
     the deterministic verifier phase inside it reuses the same
     relocation/capture assets as target 1. The five-step contract is
     binding verbatim.
  3. `NP_eq_iUnion_NTIME` (1 pt): antisymmetry of 1 and 2.

  The padding cluster in the same file remains **epoch 3 — not yours**.

## Rules on the superseded in-file privates

Your predecessor's `certificateSplit`/`choiceVerifier`/`choiceCore`/
`choiceCopy` families are proved and in-file: **cite them freely; do not
remove, rename, or modify them** (dedup is a recorded E5 task). New
helpers private, distinctly named, listed.

## Sanctioned `sorryAx`

**None.** Everything cited is proved (the library, the epoch-1 run
calculus, your predecessor's phases). On completion the file's remaining
admissions are exactly the five epoch-3 padding declarations.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt` now includes the four `Build/`
modules). Pinned toolchain; `lake exe cache get` once; **never
`lake build`**; iterate the owned module plus later modules; final full
fresh 57-module sweep, zero `error:` lines; kernel-traversal root
verification (`audits/programs/ch1-libfill-ClosureAxioms.lean` is the
template). Exclusive ownership; statement freeze absolute; escalation
over alteration; docstrings stay. **15 points; continuation per the B2
precedent if exhausted** — fill strictly in the order above.

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3); `enumMachine_contracts`
(2A-cont, concurrent); `mem_NP_iff_exists_length_le` (2C-cont); the
`TMSAT.lean` `D-*` sites (2D-cont); everything in E3/E4 files.

## REPORT.md checklist

- [ ] Three targets filled in order (or the frontier exact); the
      invariant-table rows and the five-step mappings per the original
      brief; the library contracts consumed, named per use.
- [ ] The `solveSplit`↔`certificateSplit`-style bridge lemma's exact
      coefficient translation stated.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints for all three targets: at most the standard triple,
      roots empty.
- [ ] Final sweep log tail; diff touches only `Nondeterminism.lean`;
      archive flat.

## Known pitfalls at this pin

The original E2-B list carries over verbatim, plus:
- The library's `splitSolve` output is the threaded
  `pairEncode (take i) (drop i)` with `[]` on failure — your pipeline
  consumes it through the extractors or a semantic equality to your own
  split, not by re-parsing informally.
- `capture_run`'s host-agreement hypothesis constrains **all** read
  tuples at embedded states — define your controller's table by the
  transformer (`captureAction`) on those states, as the `Build/`
  templates do, rather than proving agreement after the fact.
- The phase boundaries must stay input-length-functions only (five-step
  contract, step 2) — the library's seam discipline helps but does not
  discharge that NDTM-side obligation for you.
- No untimed composition anywhere (phase-2 note 3): the library's
  contracts are all timed; keep your glue at `ComputesInTime`
  granularity.

## ===== briefs/ch2-e2cont-batchC.md =====

# Ch2 fill campaign — E2 continuation, Batch C: the Exercise-2.1 verifier machines

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-C`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-C.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

Three documents are binding, in order: the original
`briefs/ch2-epoch2-batchC.md` (the audited two-verifier construction and
its edge-case obligations), the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchC.md` — the full semantic layer
is proved: `stripCertificate`/`certificateSplit` families, both witness
equivalences, all seven audited edge cases), and the checkpoint's own
continuation document (`audits/ch2-epoch2-agent-reports/
batchC-continuation.md` — the two exact remaining goals with their
contexts). The HALT pair is **done** (proved at the checkpoint; its last
admission root closes with the concurrent 2A continuation), so
`Reductions.lean` is no longer owned. Since the checkpoint, the campaign
shipped the fully proved **machine-construction library**
(`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
admissions) whose threaded/parser family was built with **your two
goals as named customers** — the approved coverage mapping is D5
(`audits/ch1-infra-r3-findings.md` item 7 / `ch1-libfill-resolutions.md`).

## Owned file and targets

- `TCSlib/Complexity/ClassNP/NP.lean` — the two inline goals inside
  `mem_NP_iff_exists_length_le` (6 pts total):
  1. `pairedVerifier C c V ∈ P`. D5 route: `pairValid`-guarded pipeline
     (`computesFunInTime_cond` is the proved branch); extract with
     `pairFst`/`pairSnd`; the **exact-width** test
     `|u| = C(|x|+1)^c` needs both orientations — `pairLenCheck` at
     `(C, c)` gives one; the reverse orientation is assembled per the
     recorded pairing-derivation recipe (`machine-library-design.md`
     §9c, the audit's `H/s/t` construction) — conjoin; then
     `pairConcat` and the captured run of `V`'s decider
     (`capture_run` with your controller as host); decision glue.
     Your proved `pairedVerifier_pair`/`pairedVerifier_malformed`
     connect the machine's indicator to the predicate.
  2. `paddedVerifier C c V ∈ P`. D5 route, **with the mandatory
     coefficient shift**: the split search is
     `computesFunInTime_splitSolve` at **`(C + 1, c)`** — the recorded
     vocabulary equality is `solveSplit (C+1) c = certificateSplit C c`
     (round-2 note 5; same-parameter equality is FALSE — prove the
     shifted bridge lemma, plus `splitAtLastTrue = stripCertificate`);
     then `computesFunInTime_stripLast` for the marker strip;
     `pairLenCheck` at **`(C, c)`** for the original-bound re-check
     (the audited rule: fitting the enlarged region does not authorize
     a witness); guards reject missing-split and no-marker before the
     old verifier is consulted; finish through target 1's paired
     decider on `pairEncode x u`. Your proved `paddedVerifier_*` family
     supplies every semantic identification.

## Rules on the superseded in-file privates

Nothing in `NP.lean` is superseded — your semantic layer is the spec
side the machines must meet, and it stays. (The `Reductions.lean`
`prefixTM`/`fixedPair` privates are subsumed by catalog entries, D4;
that file is not yours and the dedup is an E5 task.)

## Sanctioned `sorryAx`

**None.** The library, Chapter 1, and your semantic layer are all
proved. On completion `mem_NP_iff_exists_length_le` prints at most the
standard triple with an empty root set — and with the concurrent
2A-continuation integrated, the whole `NP.lean`/`Reductions.lean` pair
goes admission-free.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt`). Pinned toolchain;
`lake exe cache get` once; **never `lake build`**; iterate the owned
module plus later modules; final full fresh 57-module sweep, zero
`error:` lines; kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute (including the two
goals' surrounding proof structure — you are filling the two `sorry`s,
not restructuring the audited equivalence proof); escalation over
alteration; docstrings stay. **6 points; continuation per the B2
precedent if exhausted.**

## Out-of-scope sorries you will see (leave untouched)

`enumMachine_contracts` (2A-cont, concurrent — the HALT pair's root
until it lands); the `Nondeterminism.lean` cluster (2B-cont + epoch 3);
the `TMSAT.lean` `D-*` sites (2D-cont); `EXP_subset_NEXP`; everything
in E3/E4 files.

## REPORT.md checklist

- [ ] Both goals filled; each audited edge case's machine-side
      discharge point named (the original brief's seven-row table is
      the rubric); the library contracts consumed, named per use; both
      vocabulary bridge lemmas stated with their exact coefficients.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: `mem_NP_iff_exists_length_le` at most the standard
      triple, root-verified empty.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `NP.lean`; archive flat.

## Known pitfalls at this pin

The original E2-C list carries over verbatim, plus:
- **The coefficient shift is load-bearing**: `solveSplit` at the same
  `(C, c)` as `certificateSplit` is wrong at `C = c = n = 0` — the
  audit's own counterexample. P10 at `(C+1, c)`, P8 at `(C, c)`.
- `splitSolve`'s threaded output carries the *original input* as the
  pair head — that is exactly what lets `pairLenCheck` re-check the
  original bound after stripping; don't discard it and re-measure.
- `stripLast` operates on the *payload* of a valid pair (it guards
  internally); feed it `pairEncode x v`, not bare `v`.
- The exact-width conjunction: build the reverse orientation by the
  §9c recipe verbatim (`pairSnd ∘ pairConcat` over nested encodes) —
  C1 alone cannot make a payload depend on the head component.
- Your `certificateSplit` searches indices with `n + (C+1)(n+1)^c =
  total` — the library equation is `i + C'(i+1)^e = m` over the
  *candidate*; align the variable roles in the bridge lemma carefully
  (the search variable is the input-prefix length in both, but the
  bound coefficient differs by the shift).

## ===== briefs/ch2-e2cont-batchD.md =====

# Ch2 fill campaign — E2 continuation, Batch D: the TMSAT `D-*` sites

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-D`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-D.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchD.md` and the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchD.md`) remain binding — in
particular the exact-value emission discipline (never majorize the
certificate length `Q`; the three-case table), the deadline formula, and
the obligation-to-lemma map. Two things changed:

1. **The bridge is discharged.** `timed_universal_quantitative` is a
   proved theorem (the maintainer exported
   `Turing.timed_universal_concrete` from Chapter 1 and closed your
   predecessor's escalation exactly as its REPORT prescribed, via
   `tmsat_concrete_coefficient`). `TMSAT_mem_NP`'s only remaining root
   is `D-MEM`.
2. **The machine-construction library shipped, fully proved**
   (`TCSlib/Complexity/TuringMachine/Build/`, 23 contracts, zero
   admissions; both gates CLOSED). The three `D-*` obligations were
   named customers of its data-plumbing layer; the approved coverage
   mapping is D5 (`audits/ch1-infra-r3-findings.md` item 7), and the
   **canonical pairing-assembly recipe** — building
   `pairEncode (f x) (g x)` for computed `f, g` via
   `pairDup`/`pairMapSnd`/`pairConcat`/`pairSnd` — is recorded verbatim
   in `machine-library-design.md` §9c. D-MEM's D5 row names its residual
   obligations explicitly; they are yours.

## Owned file and targets

- `TCSlib/Complexity/ClassNP/TMSAT.lean` — the three `D-*` admissions,
  in order (12 pts; `TMSAT_NPComplete` closes automatically):
  1. **`D-MEM`** (inside `TMSAT_mem_NP`, ≈ line 964; 5 pts). The
     verifier: parse the nested quadruple
     `pairEncode (pairEncode (bits t) α) (pairEncode x u)` by iterated
     `pairFst`/`pairSnd` with `pairValid` guards (`cond` is the proved
     branch); the unary-to-binary clock conversion is `pairMapSnd` with
     a length-counting payload transform (the D5 row's named route —
     `lengthBits`' machine on the payload); the D5-named residuals —
     the timed extraction of `w.take n` from the parsed unary clock,
     the all-true unary-shape checks, and the complete-answer test
     `[true, true]` — are your bespoke pieces; assemble the
     well-formed request and invoke the **proved bridge** through your
     predecessor's proved `tmsat_simulator_total`/`tmsatAnswer_accept`/
     `tmsat_simulation_budget` chain.
  2. **`D-WRAP`** (inside `TMSAT_NPHard`, ≈ line 1152; 3 pts). The D5
     route verbatim: `pairValid` guard + **`pairConcat`**
     (`pairEncode x u ↦ x ++ u`) + the captured verifier run + the
     `cond` constant-reject branch realizing `tmsatWrapperOutput`'s
     malformed-`[false]` clause.
  3. **`D-EMIT`** (inside `TMSAT_NPHard`, ≈ line 1190; 4 pts). The §9c
     recipe applied to the two **exact** unary runs: `Q` by your
     predecessor's proved `tmsat_exact_certificate_bits` three-case
     discipline (its case machines are `computesFunInTime_polyUnary`
     instances and `computesFunInTime_const`-style chains — exact
     values, never majorized), `T'` by the proved
     `tmsat_deadline_bound` formula via `polyUnary` at the prescribed
     `(D, 2er - 1)` parameters; pair them per §9c, retain `x` via
     `pairDup`, and apply `computesFunInTime_pairEncodeFixed α₀` for
     the outer layer. `tmsat_quad_injective` and
     `tmsat_reduction_correct` (proved) finish the hardness argument as
     the docstring's audited route prescribes.

## Rules on the superseded in-file privates

`polyUnaryTM`/`poly_unary_computes` were harvested into the library's
catalog; both copies are proved. **Cite either; remove or modify
neither** (dedup is a recorded E5 task). New helpers private,
distinctly named, listed.

## Sanctioned `sorryAx`

**None.** The bridge is proved, the library is proved, the in-file
semantic layer is proved. On completion `TMSAT_mem_NP`, `TMSAT_NPHard`,
and `TMSAT_NPComplete` all print at most the standard triple with empty
root sets — your REPORT includes all three prints.

## Environment, ground rules, verification

As the original E2 brief, with the 57-module order update
(`scripts/ab_ch1_module_order.txt`). Pinned toolchain;
`lake exe cache get` once; **never `lake build`**; iterate the owned
module plus later modules; final full fresh 57-module sweep, zero
`error:` lines; kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute; escalation over
alteration; docstrings stay (append-only notes; the `D-*` CONTINUATION
markers may be converted to historical notes when their sites close).
The file is at 1,206 lines under its recorded exception — report the
final size. **12 points; continuation per the B2 precedent if
exhausted** — fill strictly MEM → WRAP → EMIT.

## Out-of-scope sorries you will see (leave untouched)

`enumMachine_contracts` (2A-cont, concurrent); the `Nondeterminism.lean`
cluster (2B-cont + epoch 3); `mem_NP_iff_exists_length_le` (2C-cont);
`EXP_subset_NEXP`; everything in E3/E4 files.

## REPORT.md checklist

- [ ] Three sites filled in order (or the frontier exact); the original
      brief's obligation-to-lemma map completed for every remaining
      open row; the library contracts and §9c recipe steps named per
      use; the D5 residual obligations' discharge points named.
- [ ] The exact-value discipline attested: `Q` emitted exactly per the
      three-case table; only the deadline majorized.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: all three TMSAT targets (and the bridge) at most
      the standard triple, roots empty.
- [ ] Final sweep log tail; diff touches only `TMSAT.lean`; archive
      flat.

## Known pitfalls at this pin

The original E2-D list carries over verbatim, plus:
- `pairEncode` nesting: get the quadruple's associativity from the
  statement, not memory — the parse order is `pairFst` for
  `pairEncode (bits t) α`, then `pairSnd` twice down the spine.
- C1 (`pairMapSnd`) transforms the **payload only**; any
  cross-component step (the clock count against `x`'s length) goes
  through the §9c retained-whole-request pattern, never a payload
  function peeking at the head.
- The extractors' `getD []` conflates failure with a genuinely empty
  component — guard with `pairValid` **before** extraction at every
  spine level (the audit's recorded design).
- `polyUnary` instances emit `C·(n+1)^e` of **their own input's**
  length — when the emission must be a function of a *component's*
  length, route through `pairMapSnd` so the component is the payload.
- The bridge's budget is consumed through `tmsat_simulation_budget`
  (proved) — do not re-derive the coefficient arithmetic.

## ===== briefs/ch2-e2cont-batchB2.md =====

# Ch2 fill campaign — E2 continuation, Batch B2: the reverse NDTM host

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-B2`),
  record the base commit hash in `REPORT.md`. The required base is
  `e72d95bf35ebf09c21aae7e1959e5d895a345686`.
- **Delivery is by zip, not PR or push**: `fill-ch2-e2cont-B2.zip`,
  **flat** (`SHA256SUMS` at the root), with `REPORT.md`, the full
  modified source, the `git format-patch` series, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

The last open construction of chapter 2's epoch 2. Three documents are
binding, in order: `briefs/ch2-epoch2-batchB.md` (the phase-2 invariant
tables and the **five-step certificates↔choice-words reconstruction
contract, verbatim and binding**; the no-untimed-composition rule),
`briefs/ch2-e2cont-batchB.md`, and — read it first — your predecessor's
REPORT at `audits/ch2-epoch2-agent-reports/batchB-cont.md`: its
"Reverse five-step contract" table says exactly what is proved versus
remaining, its continuation section is a **five-step work plan written
against the banked assets**, and its warnings are binding (repeated
below). The forward compilation is done (`ntime_poly_subset_NP` is
admission-free); nine of the epoch's ten targets are closed; yours are
the last two.

## Owned file and targets

- `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — targets, in order:
  1. `NP_subset_iUnion_NTIME` (8 pts). The exact remaining goal is
     displayed in your predecessor's REPORT: from the certificate
     characterization and a verifier decider, produce
     `N : FinNDTM Bool` deciding `L` within `K·(n + C(n+1)^c + 1)^r`.
     Banked and proved, in-file: the native guessing table
     (`contGuessTM`, built on the library's `captureAction`
     transformer), its physical-position extraction and coverage
     (`contSelect`/`cont_select_surjective`/`cont_guess_coverage` — at
     actual write positions, zero-coefficient case included), the
     polynomial scheduler instance (`cont_poly_guess_phase`), the
     envelope arithmetic (`cont_guess_time_bound`, exact coefficient
     `K(C+1)^r·2^(r·max 1 c)`), and the final packaging
     (`cont_guess_normalize` — it closes the target once handed a
     whole-decider contract). The forward construction's loader,
     relocation, and capture layers are proved precedents in-file.
     Your work is the **integrated host**, per the predecessor's plan:
     (1) the native host preserving the original input and installing
     the length-only scheduler/countdown — the scheduler relocation
     seam is explicitly missing (see warnings); (2) embed the guessing
     table with disjoint source/administrative tapes and translate the
     write mask into complete branch words including the startup
     offset, reusing `cont_guess_coverage` at the actual scheduler
     completion; (3) assemble `x ++ u`, prepare the relocated verifier
     with blank source tapes and virtual head one, prove the two NDTM
     tables coincide outside guessing, capture the completed output
     (halting emission included), one verdict bit; (4) all-branch
     totality, exact certificate length, acceptance ⟺ membership, a
     **common upper bound** (actual halting times may vary per
     branch); (5) the displayed envelope, then `cont_guess_normalize`.
  2. `NP_eq_iUnion_NTIME` (1 pt): antisymmetry of the proved forward
     target and target 1.

## Binding warnings (the predecessor's, restated)

- `contGuessTM` is a **phase**, not the missing decider; its
  scheduler's completed state is a live, stationary return state — it
  never claims all-branch halting. The host supplies that.
- `cont_poly_guess_phase` runs the scheduler on the **unary word of
  length `n`**, not on an arbitrary original input: relocating the
  library's unary generator to a prepared unary input, or proving an
  equivalent normalization of its input reads, is an explicit missing
  seam — the generator's function-level contract alone does not assert
  value-independent running times on arbitrary inputs.
- The host must dispatch on an **actual completed scheduler** (for
  example its first halt) and prove that seam; do not infer a native
  clock from an upper bound.
- Phase boundaries are input-length functions only (five-step contract,
  step 2) — value-dependent timing breaks witness extraction.
- The NDTM guessing side is bespoke by design (the library covers
  deterministic machines); the deterministic sub-phases reuse the
  proved in-file and library assets freely.

## Rules on in-file material

Everything your predecessors proved — the epoch-2 checkpoint's 32
privates, the continuation's 36 — is citable and **untouchable** (no
removal, renaming, or modification; dedup is E5). The padding cluster
(five admissions) is epoch 3; the third target's current admission body
is yours to fill only after target 1.

## Sanctioned `sorryAx`

**None.** Everything cited is proved. On completion the file's only
admissions are the five epoch-3 padding declarations, and the epoch-2
gate condition — all ten targets admission-free — is met.

## Environment, ground rules, verification

As the prior briefs: pinned toolchain (Lean 4.25.0, `cdd38ac5115b`;
mathlib `029db123ddaa`); `lake exe cache get` once; **never
`lake build`**; bootstrap the 57-module order
(`scripts/ab_ch1_module_order.txt`); iterate the owned module plus
later modules; final full fresh 57-module sweep, zero `error:` lines;
kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the template).
Exclusive ownership; statement freeze absolute; escalation over
alteration; docstrings stay (append-only notes; the predecessor's
checkpoint-note tails may be extended per the established pattern).
The file is at 1,670 lines under its recorded exception — report the
final size. **9 points; continuation per the B2 precedent if
exhausted.**

## Out-of-scope sorries you will see (leave untouched)

The padding cluster in your own file (epoch 3); `EXP_subset_NEXP`;
everything in E3/E4 files (`SAT.lean`, `Tautology.lean`,
`CookLevin/*`). Nothing else remains admitted anywhere in scope.

## REPORT.md checklist

- [ ] Both targets filled (or the frontier exact); the five binding
      steps mapped to your discharging lemmas, with the scheduler
      relocation seam, the table-coincidence proof, and the
      common-bound argument called out explicitly.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints: both targets at most the standard triple, roots
      empty — and, since this closes the epoch, prints for all ten
      epoch-2 targets.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `Nondeterminism.lean`;
      archive flat.

## Known pitfalls at this pin

The E2-B and e2cont-B lists carry over verbatim, plus:
- `FinNDTM` branch words: the guessing table ignores its choice bit on
  administrative transitions — coverage is at the **actual** physical
  write positions (`contSelect`), never "the first `Q(n)` choices".
- `cont_guess_normalize` wants all-branch halting through
  `acceptsWithin_iff_of_halts` — prove totality for **every** branch,
  accepted or not, on **every** input, in or out of `L`.
- The two tables must coincide outside the guessing phase as a
  **definitional fact of your construction** (the original brief's
  pitfall), not a lemma fought afterwards.
- Budget padding at the end is `Turing.FinNDTM.AcceptsWithin.mono`
  (proved, epoch 1) — don't re-derive absorption.

## ===== audits/ch2-epoch2-agent-reports/batchA.md =====

# Chapter 2, epoch 2, batch A — partial continuation delivery

**`NP_subset_EXP` is not yet proved.** This archive uses the brief's explicit
partial-delivery provision. Its outer proof is filled, but it depends on one
openly admitted private construction lemma, `enumMachine_contracts`. The
completed-batch axiom gate therefore remains open.

The delivered implementation proves the exact-width enumeration semantics,
a concrete fixed-width increment-and-rewind machine, a buffered verifier-call
simulator with finite-control output capture and live return, an abstract
timed-loop theorem, and the final exponential-budget normalization. The
concrete initialization, buffer assembly, reset, and loop-controller integration
remain unfinished.

The final fresh sweep passed **53/53 modules, zero `error:` diagnostics**.
There are 40 new source-level private declarations: 38 have no `sorryAx` in
their transitive axiom footprint; the construction lemma and its derived
`enumDecider` depend on the single pending admission. No public declaration
was added or removed.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`
- Required base branch: `complexity/arora-barak-ch1`
- Recorded base: `6c09453e6af59ff1575060b66196d28812800d24`
- Work branch, as instructed by the committed brief: `fill/ch2-e2-A`
- Delivered commit: `a8f26ddb38bc52318282f96b4de6543da0ac03db`
- Delivered tree: `551ea91aa587e74eb8d23583dd028467cd4b7087`
- Binding brief: `briefs/ch2-epoch2-batchA.md` at the recorded base.
- Lean: 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent, no delegation.

Only `TCSlib/Complexity/ClassNP/EXP.lean` changed in the Git patch. All work
derives from the required base; `main` was not checked out, edited, or used as
a base. There was no push or PR. Report and verification files are archive
artifacts, outside the repository patch.

Initial restricted network access required recovering the exact base objects
through the GitHub connector and checking their Git hashes. A subsequent
successful `git fetch --unshallow origin complexity/arora-barak-ch1` restored
the normal repository history. The delivered bundle has the genuine recorded
base as its prerequisite, not a synthetic snapshot commit.

## Six-contract mapping

All names in this table are private declarations in `Complexity`, except the
public target. **A proved component is not a claim that its surrounding
controller has been constructed.**

| Required contract | Proved evidence | Remaining obligation |
|---|---|---|
| Width evaluation and initialization | `enumWord_length` and `enumWord_zero` identify the exact-width initial word. | No polynomial-width evaluation/initialization machine is yet constructed. Retaining the instance, allocating the candidate, and reaching the initial configuration within the startup bound remain in `enumMachine_contracts`. |
| Fixed-width increment and overflow | `enumInc_spec`, `enumInc_word`, `enumWord_complete`, `enumWord_no_repeat`, and `enumCandidates_iff` prove exact coverage, distinct ranks, and last-rank overflow. `enumCarry_correct` proves an actual one-tape increment and rewind, preserving width with cost at most twice the width plus two. `enumBump_inc` links its result and success flag to `enumInc`. | Embed this subroutine in the final controller and wire overflow to final rejection. Width zero already has one candidate in the enumeration; its increment returns overflow without extending the tape. |
| Buffering, retention, and verifier-call simulation | `enumCaptureCfg`, `enumCapture_step`, and `enumCapture_run` simulate a verifier on an exact prepared buffer. `bufferTape_inputSymbol` and `virtualMove_correct` from the public API supply native reads and clamping, including both boundaries and empty input. The native input head and arbitrary retained tapes/heads are preserved. | Actually assemble `x ++ u` in that buffer before each call and restore its initial position between calls. The simulator theorem assumes the prepared configuration. |
| Capture and return | `enumCaptureTM` suppresses every source emission and records the first bit. `enumCapture_returns` proves return within the verifier budget plus one step, into a live controller state selected using the updated captured bit. It preserves the entire completed source configuration and has empty physical output, including when the bit is emitted on the halting action. | Supply the final controller and its single final-answer emission. Repeated-call correctness also requires the missing reset. No claim is made that two calls have already been composed into a working enumerator. |
| Restart | The call result identifies the full source work tapes and heads, buffer head, retained data, and captured register, making the reset input precise. | No reset-machine theorem is supplied. Clear the bounded visited region, restore all simulated heads and source control, clear the captured bit, restore the buffer/head bookkeeping, and prove a polynomial bound. |
| Timed loop invariant | `enumLoop_run` composes bounded accept-or-advance segments, tests the final candidate before exhaustion, and proves the singleton-output result and total step bound. `enumAny_certificates` identifies the answer with exact-width existential certificates. `enumExponent_bound` and `enumBudget_bound` prove the pointwise EXP bound, including small lengths. `enumDecider` and `NP_subset_EXP` carry out the outer reduction. | The per-round configuration equalities and startup premises for the concrete finite enumerator remain in `enumMachine_contracts`. Thus `enumDecider` and the public target still inherit `sorryAx`. |

## Exact continuation frontier

The only **new directly admitted** declaration is
`Complexity.enumMachine_contracts`, at source line 750. Its statement requires
one uniform finite machine, a polynomial startup bound, a canonical
configuration for every candidate rank, a halted singleton rejection after
the last rejected candidate, and polynomially bounded accept-or-advance
segments on all exact-width candidates.

The contract quantifies over the actual verifier machine and its explicit
polynomial time guarantee. It does not use an untimed composition theorem or
an abstract, potentially noncomputable width function. The certificate width
is exactly the prescribed formula throughout.

Recommended continuation order:

1. Construct the width evaluator and initial candidate with retained input,
   and prove the startup configuration and polynomial cost.
2. Implement buffer assembly and its rewind to the source's initial position.
3. Implement bounded clearing and reset. The existing public
   `Turing.FinTM.source_bounds` in `TuringMachine/Sweep.lean` bounds source heads
   and nonblank cells by elapsed time, but does not itself perform this reset.
4. Instantiate the finite controller of `enumCaptureTM`, integrate the
   increment subroutine, and establish the per-round equalities required by
   `enumMachine_contracts`. Its controller has access to all tape blocks;
   the existing capture lemmas concern `runFrom` on prepared configurations,
   not initialization from its `q₀`.
5. Fill that one admission and rerun the full sweep and axiom checks. The
   already checked outer proof then gives the target.

The public target's original proof sketch and attribution are preserved.
One **Partial-fill appendix** was appended to its docstring to disclose the
remaining admission. The original proof-body `sorry` was replaced by the
outer derivation; this is not a reduction in the number of unfinished
mathematical obligations.

## New declarations

These are all 40 source-level additions, all private. The full statements and
proofs are in the supplied source; compiler-generated auxiliary declarations
are included in transitive dependency checks.

| Name | Role |
|---|---|
| `enumValue` | Little-endian value including high zero bits. |
| `enumInc` | Fixed-width increment with explicit overflow. |
| `enumWord` | Width-preserving representation of a rank. |
| `enumValue_lt` | Value lies below the width's power of two. |
| `enumWord_length` | Exact representation width. |
| `enumWord_zero` | Initial all-false candidate. |
| `enumWord_value` | In-range rank is recovered. |
| `enumValue_injective` | Equal-width representation uniqueness. |
| `enumWord_complete` | Every word is represented. |
| `enumInc_spec` | Successor or exact overflow specification. |
| `enumInc_word` | Increment follows consecutive candidate ranks. |
| `enumWord_no_repeat` | No duplicate in-range candidates. |
| `enumCandidates_iff` | Exact-width certificates equal ranked candidates. |
| `enumBump` | Physical carry result and success flag. |
| `enumCarryPos` | Leading true-prefix length. |
| `enumCarryPos_le` | Carry distance is width-bounded. |
| `enumBump_length` | Carry preserves width on success and overflow. |
| `enumBump_inc` | Physical carry result agrees with abstract increment. |
| `enumBuffer_read` | Read at the start of a suffix. |
| `enumBuffer_write` | Replace one bit without changing width. |
| `enumCarryTM` | Concrete increment-and-rewind finite machine. |
| `enumCarryCfg` | Its canonical tape configurations. |
| `enumCarry_step` | One carry transition, including nonwriting overflow. |
| `enumCarry_run` | Complete carry-phase correspondence. |
| `enumCarry_rewind` | Exact rewind time and result. |
| `enumCarry_correct` | Complete increment, linear time, and live return. |
| `enumCaptureTM` | Buffered capture wrapper with arbitrary finite controller. |
| `enumCaptureCfg` | Full virtual-source and retained-data invariant. |
| `enumCapture_step` | One-step simulation and boundary-tag preservation. |
| `enumCapture_run` | Simulation through the first source halt. |
| `enumCapture_transfer` | Live dispatch using the updated bit. |
| `enumCapture_returns` | Timed captured-call result and exact retained configuration. |
| `enumAny` | Abstract consecutive-rank search. |
| `enumAny_iff` | Search correctness over the rank interval. |
| `enumAny_certificates` | Search answer matches the existential certificate condition. |
| `enumLoop_run` | Timed loop composition from per-round contracts. |
| `enumExponent_bound` | Polynomial exponent absorbed into an EXP bound. |
| `enumBudget_bound` | Full round budget normalized to EXP. |
| `enumMachine_contracts` | **Admitted:** remaining concrete construction. |
| `enumDecider` | Derived decider, **dependent on that admission**. |

## Requested shared lemmas and escalations

Requested shared lemmas: **none for this delivery**. Every added helper remains
private; no private declaration from another module is cited.

Escalations: **none**. No obstruction to a frozen statement was found. The
unfinished work is machine construction and verification, not a proposed
statement repair.

## Verification

Setup ran the required `lake exe cache get`, narrowed to the campaign's
Mathlib roots. It completed successfully. No `lake build` was run. A bootstrap
sweep checked all 53 modules before the source edits. Edits were checked with
`lean_check_tree.sh` starting at EXP and continuing through every later module.
An early downstream check suffered a process-level bus error while dependency
cache setup was still active; it was not accepted as verification. Successful
downstream sweeps and the final fresh sweep followed after setup completed.

The final sweep used a new, separate olean tree and the recorded commit. Each
check exited zero and produced a fresh olean. The log has 53 pass markers,
zero `error:` lines, and 32 admitted-declaration warnings across the chapter.
EXP's two direct admissions are the new continuation frontier and the
unchanged out-of-scope `EXP_subset_NEXP`.

Final sweep tail:

```text
CHECK TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
MODULES_PASSED 53
END_UTC 2026-10-02T22:06:35Z
```

The axiom audit ran against that final fresh tree. The target prints:

```text
'Complexity.NP_subset_EXP' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound]
```

The audit checks every new source-level declaration, permits only the standard
triple for the 38 independent declarations, and traverses constant types and
values (including opaque values) to locate directly admitted dependencies.
The target's **only directly admitted dependency root** is
`_private.TCSlib.Complexity.ClassNP.EXP.0.Complexity.enumMachine_contracts`.
It does not depend on any out-of-scope admitted theorem.

`logs/statement-freeze.log` records preservation of all six original public
signatures, their ordered sequence and multiset, and byte-identical original
definitions plus both out-of-scope proofs. Imports and option headers are
unchanged. `git diff --check` passes. The owned-file policy lint reports
zero FAIL and zero WARN; it records the 882-line file as above the 600-line
target. Exclusive file ownership keeps this one target's helpers together.

## Delivery and reproduction

The archive root contains this report, the full modified source at its
repository-relative path, one `git format-patch` patch, an incremental Git
bundle, sweep and axiom logs, verification inputs, and `SHA256SUMS`.

The bundle requires the recorded base and advertises `refs/heads/fill/ch2-e2-A`
at the delivered commit. `git bundle verify` passes. A temporary-index replay
of the patch reproduces the delivered Git tree exactly without touching any
working branch. Intended maintainer integration is `git am -3` against the
campaign branch, preserving authorship; this archive is a **continuation
checkpoint**, not a completed fill for closing the epoch gate.

After unpacking, run `sha256sum -c SHA256SUMS`. With the pinned toolchain on
`PATH` and dependencies initialized, the included scripts take the repository
path as their argument:

```bash
bash verification/full-sweep.sh /path/to/tcslib
bash verification/run-axioms.sh /path/to/tcslib
python3 verification/check-freeze.py /path/to/tcslib
python3 verification/replay-patch.py /path/to/tcslib
```

Both shell scripts honor `TCSLIB_OLEANS` when using a separate fresh tree.
The axiom script deliberately identifies the present result as partial; its
passing audit status certifies the **disclosed dependency footprint**, not
the completed-batch no-`sorryAx` gate.

## Checklist

- [ ] Target fully proved and completed-batch axiom gate satisfied.
- [x] Six-contract table identifies completed components and remaining work.
- [x] Every new source-level declaration listed; all private.
- [x] Exactly one new directly admitted private declaration identified.
- [x] Recorded base, patch, bundle, and full source supplied.
- [x] Final 53-module sweep and axiom-print log supplied.
- [x] Statement freeze and exclusive file ownership checked.
- [x] Requested shared lemmas and escalations recorded.

## ===== audits/ch2-epoch2-agent-reports/batchA-cont.md =====

# Chapter 2 E2 continuation, batch A — completed enumerator

`enumMachine_contracts` is proved without an in-scope admission, through the required `Turing.FinTM.exists_loopCfgTM` route. Its frozen statement is unchanged. The existing outer proofs of `NP_subset_EXP`, `HALT_NPHard`, and `HALT_not_mem_NP` are unchanged and now have no admitted dependency.

The four required axiom prints contain exactly `[propext, Classical.choice, Quot.sound]`; checked-kernel dependency traversal finds an empty admission-root set for each. All 95 new named private helpers and their 252 declarations including generated descendants are also admission-free. The only source-level admission remaining in the owned file is the unchanged, out-of-scope `EXP_subset_NEXP`.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required campaign branch: `complexity/arora-barak-ch1`.
- Exact base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- Work branch: `fill/ch2-e2cont-A`.
- Delivered commit: `336f016e28deff86fdcd01dcb5859e150cc0b0a6`.
- Delivered tree: `19890a9d28b1f93c0baeada742a0e97946bcbe48`.
- Parent of the delivered commit: the exact required base above.
- Lean: 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Single Codex agent; no delegation, push, or PR.

The continuation brief was read from the named campaign branch before implementation. The checkout for the delivered source is pinned to its required base, not a newer branch tip. The infra round-3 item 5, machine-library-design sections 9b/9c, original E2-A brief and predecessor report, policy, workflow, and repository agent instructions were read as binding context. `main` was not used as the work base.

Only `TCSlib/Complexity/ClassNP/EXP.lean` changes in Git. The precise import `TCSlib.Complexity.TuringMachine.Build.Primitives` is added. All new implementation declarations are private and distinctly named. Report, instruments, and logs are delivery artifacts outside the Git patch.

## Construction and six-contract mapping

A source block shares work tapes between the unary initializer, the prepared verifier composition, and the prepared increment composition. Each call is wrapped by a finite logging and restoration machine. Logging saves the old symbol and head displacement for each source work tape at each live source step, with a separate unary clock. The public capture simulation suppresses physical emissions and writes the source output to a dedicated capture tape. Reverse replay restores each original work cell and head, erases every history cell, then rewinds the native input and capture heads. Thus the reset is a proved complete-configuration equality, including the buffer, rather than an assumption that clearing is free.

| Required contract | Discharging construction and lemmas |
|---|---|
| Width evaluation and initialization | `computesFunInTime_polyUnary C c` supplies the explicit unary width. `enumCont_lift_init`, `enumCont_body_call`, `enumCont_body_start`, and `enumCont_body_start_guarded` run it, copy each true mark as a false candidate bit, erase the marks, and restore the native head to 1 and every work head to 0. The resulting candidate has exactly the prescribed width; native input is read-only and retained. |
| Fixed-width increment and overflow | `computesFunInTime_incFixed` is invoked on the candidate alone by `enumCont_increment_call`. `enumCont_increment_cases`, `enumCont_body_check`, `enumCont_copy_complete`, and `enumCont_body_increment` copy a successful equal-width result onto candidate tape 0 in place, erase capture, and rewind. Empty overflow output retains the old word. `enumCont_inc_eq`, `enumCont_step_length`, and `enumCont_orbit` bridge this stalled step to the predecessor's proved rank enumeration. The exported fuel controls exhaustion, including the one empty-word round at width zero. |
| Buffering, retention, and verifier-call simulation | `enumCont_concat_native`, `enumCont_concat_candidate`, and `enumCont_concat_run` emit exactly `x ++ s`. `enumCont_prepared_comp`, `enumCont_round_seam`, and `enumCont_verifier_call` use the proved buffered composition, correct virtual input boundaries, and fresh verifier tapes. `enumCont_lift_call` places this prepared call in the shared source block. The clean wrapper restores the retained candidate and source work. |
| Capture and return | `enumCont_clean_capture` instantiates the public `Turing.capture_run` with the clean controller as host for the logged source. That source contains the actual supplied verifier in the buffered composition. `enumCont_clean_complete`, `enumCont_return_run`, and `enumCont_body_call` capture the completed output, including a halting-transition emission, restore work, and redirect the first halt to live administration. `enumCont_body_accept` emits exactly `[true]`; `enumCont_body_reject` erases the false verdict before increment. No source emission reaches the physical output. |
| Restart | `enumCont_log_apply`/`enumCont_log_run` prove the trace, and `enumCont_restore_cell`, `enumCont_undo_back`, `enumCont_undo_write`, `enumCont_undo_run`, and `enumCont_clean_restore` undo it exactly. `enumCont_rewind`, `enumCont_clean_buffer_rewind`, and `enumCont_clean_complete` restore native/capture positions. `enumCont_clean_entry_words`, `enumCont_clean_exit_words`, `enumCont_copy_complete`, and `enumCont_pair_words` identify the complete blank-scratch seam. All restoration costs are included in the body budget. |
| Timed loop invariant | `enumCont_body_round_raw` composes verdict dispatch, clean increment, copy, and rewind. `enumCont_first_anchor` and `enumCont_halt_transfer` transfer runs from a controller variant with an absorbing anchor; `enumCont_body_start_guarded` and `enumCont_body_round_guarded` prove the exact startup and positive, strict-interior-anchor-free round contracts. `enumCont_common_bound` supplies one uniform polynomial. `enumCont_from_body` applies the audited loop export and translates its conclusion to the frozen interface. The predecessor's unchanged `enumDecider`, `enumLoop_run`, and `enumBudget_bound` finish the public result. |

The stopped-controller device is proof machinery only: it differs from the active body solely at the anchor. A rejecting run uses its first anchor visit, whose complete configuration equals the bounded endpoint because that anchor is absorbing. An accepting stopped run could not have visited the live absorbing anchor. Adding the actual body's one-step departure proves strictly positive round time and excludes all strict interior returns.

## Exact loop instantiation

Write `n = x.length`, `w = C * (n + 1)^c`, and `N = n + w + 1`. Let `fU` be the initializer's catalog coefficient and `j` the incrementer's coefficient. `enumCont_common_bound` chooses, before `x`,

- body coefficient `A = 3*a + 3*fU + 3*j + 60`;
- body degree `D = d + c + 2`.

The body startup is bounded by `3*TU + n + 3*w + 10`, with `TU = fU*(n+1)^(c+1)`. A round is bounded by `3*TV + 3*TI + 2*n + 3*w + 22`, where `TV ≤ a*N^d + 2*(n+w) + 4` and `TI ≤ (j+3)*(w+1)`. Both are at most `A*N^D`.

| `exists_loopCfgTM` argument or hypothesis | Exact instance / evidence |
|---|---|
| `body`, `anchor` | `enumCont_bodyTM B qv qi false`, administrative state `.inr 0`. `B = enumCont_sources Q R U`, where `Q` is buffered concatenation followed by `MV`, `R` is candidate-only concatenation followed by the catalog incrementer, and `U` is the catalog unary width generator. |
| `Inv x s` | `s.length = C * (x.length + 1)^c`. |
| `s0 x` | `List.replicate (C * (x.length + 1)^c) false`. |
| `stepF x s` | `(incFixed s).getD s`, preserving width on overflow. |
| `acceptF x s` | `MultiTapeTM.indicator V (x ++ s)`, computed by the captured prepared call to the hypothesis machine `MV`. |
| `R n` | `2^(C*(n+1)^c) - 1`. |
| `hF` | A direct second `computesFunInTime_polyUnary C c` catalog instance with coefficient `fF`; `enumCont_fuel_bits` proves `Nat.bits (2^w-1) = List.replicate w true` by induction, using `Nat.bit1_bits` at successor width. No alternate fuel evaluator is used. |
| common `T n` | `(A + fF) * (n + C*(n+1)^c + 1)^(D+c+1)`, dominating both body and fuel costs. |
| `hInv0` | `List.length_replicate`. |
| `hInvStep` | `enumCont_step_length`, derived through `enumCont_inc_eq` and the proved in-file `enumInc_spec`. |
| `hstart` | `enumCont_body_start_guarded` plus the first component of `enumCont_common_bound`, then domination by `T`. |
| `hround` | `enumCont_body_round_guarded` plus the second component of `enumCont_common_bound`, then domination by `T`. Includes positive time, the strict-interior anchor exclusion, singleton acceptance, and the exact restored next seam. |

The conclusion translation is exactly infra round-3 item 5:

1. `enumCont_orbit` proves the orbit equals `enumWord w i` for `i < 2^w`, using the in-file `enumWord_zero` and `enumInc_word`. It makes no false claim about the terminal orbit value at `2^w`.
2. `1 ≤ 2^w` gives `(2^w - 1) + 1 = 2^w`. The exported terminal state and `[false]` output are rewritten to this exact frozen index.
3. The configuration family is used unchanged, and each exported in-range round is rewritten by the bounded orbit identity.
4. If the export coefficient is `K`, take `b = K*(A+fF+1)` and `e = D+c+1`. Since `1 ≤ N^e`, the frozen budget dominates `K*(T n + 1)`. Coefficients and degrees are fixed before the input. At width zero the fuel is zero but the loop still tests the unique empty candidate before rejecting.

## Statement freeze and size

`freeze.py` verifies all 46 existing declarations remain in their original order, with the same six public declarations and no removals. Only the proof body of `enumMachine_contracts` differs. Its signature is identical. All 46 pre-existing docstrings remain verbatim and in order.

A stronger byte check deletes the newly inserted helper region and completion note, restores only the target's old `sorry` proof, and removes the permitted import. The result is byte-for-byte identical to the base file. This covers every old private family, every unchanged public proof, original header/options, and the out-of-scope admission. In particular no `enumCarry*`, `enumCapture*`, or `enumLoop_run` declaration was edited.

An append-only completion note after the filled target explains that the historical partial-fill descriptions are superseded. Those frozen descriptions themselves were not edited.

The final file is **2887 lines** (base: 882), with six public and 135 private declarations. Its source SHA-256 is `ce21b2543c7acf883d29921e042aeda808c92d564b4483eba3ca9e00ae08e9c6`. This extends the recorded 600-line-target overrun and exceeds the 1000-line split threshold. The positive justification is the binding single-file ownership: all newly required machine/controller proofs must remain private in `EXP.lean`, while the superseded old families must be retained unchanged until E5 deduplication. Splitting or moving these implementations would violate this fill's ownership/freeze constraints. The size is explicitly reported for subsequent closure/refactoring review.

Requested shared lemmas: **none**. Statement escalations: **none**. No frozen statement repair was needed.

## Verification

The required `lake exe cache get` was invoked once, narrowed to the campaign's Mathlib roots, and succeeded. No `lake build` was run. The working olean tree was bootstrapped in dependency order, with the owned module checked during proof iteration and all 14 later modules successfully checked after the final owned-file edit. Failed development iterations were not treated as gate passes.

The final sweep uses the committed 57-module order and a new output tree, `.lake/e2cont-A-final-oleans`, which did not exist at launch. Each module is checked through the committed `lean_check_tree.sh`: zero exit status, no error diagnostics, and a freshly produced olean are required. The completed gate results and exact log tail follow.

The full fresh sweep passed **57/57 modules**, produced 57 fresh oleans, and reported **zero errors**. The 27 admitted-declaration warnings are all out of scope. Final sweep tail:

```text
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

The axiom/root instrument runs against that same fresh tree. It uses the committed closure-audit template's traversal of checked kernel constant types and values, including opaque bodies and inductive constructors. It resolves the private target by its user name, prints all four targets, rejects every axiom outside the standard triple, and requires empty roots. It also checks every new helper and generated descendant, including helpers outside the target's dependency closure.

Final axiom and root output:

```text
'_private.TCSlib.Complexity.ClassNP.EXP.0.Complexity.enumMachine_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ROOTS Complexity.enumMachine_contracts: []
'Complexity.NP_subset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.NP_subset_EXP: []
'Complexity.HALT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.HALT_NPHard: []
'Complexity.HALT_not_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.HALT_not_mem_NP: []
NEW_IMPLEMENTATION_PASS named_helpers=95 declarations_with_descendants=252 roots=[]
ENUMERATOR AUDIT PASS: all four required closures have empty admission roots and at most the standard axiom triple.
```

`git diff --check` passes. The ClassNP policy lint has zero FAIL and two size WARNs: this reported 2887-line `EXP.lean` and the unchanged 1206-line `TMSAT.lean`. The owned-file Lean check emits only the expected out-of-scope admission warning, with no new simplifier/tactic warnings.

The pinned installed toolchain was reused. This executor requires the supplied `proc_self_compat.c` readlink compatibility shim: it redirects only the current process's `/proc/<pid>/exe` lookup to `/proc/self/exe` so Lean finds its standard library. It does not alter Lean, source, kernel behavior, or proof checking. Normal environments do not need the shim. `environment.log` records the actual toolchain version and dependency pin.

## New private declarations

All 95 source-level additions are listed below in declaration order. Names are in namespace `Complexity`; implementation-generated descendants are covered by the kernel check. No new public declaration is introduced.

| Name | Role |
|---|---|
| `enumCont_inc_eq` | The catalog counter and the predecessor's counter have the same recursive equations, including overflow on the empty word. |
| `enumCont_step_length` | Stalling on overflow preserves the exact candidate width. |
| `enumCont_orbit` | Before exhaustion, the stalled catalog orbit is exactly the predecessor's rank enumeration. |
| `enumCont_fuel_bits` | The exact fuel word is a unary all-true word of the certificate width. |
| `enumCont_sparse` | A history tape can contain blank entries; its length is tracked on a separate all-true clock tape. |
| `enumCont_sparse_append` | Appending a possibly blank history symbol writes just the next cell. |
| `enumCont_sparse_erase` | Erasing the last history cell recovers its prefix, even if the erased entry was itself blank. |
| `enumCont_moveCode` | Three tape symbols encode the three source head moves. |
| `enumCont_unmove` | Decode the inverse move for the backward restoration pass. |
| `enumCont_unmove_cast` | A recorded move and its inverse cancel as integer head displacements. |
| `EnumContEntry` | A history entry retains every overwritten symbol and every source move. |
| `enumCont_logAction` | Instrument one source action with a clock cell and two history tracks per source tape. |
| `enumCont_logTM` | The logged source keeps its original finite state set. |
| `enumCont_logCfg` | The correspondence stores exactly the source configuration and the finite history; every history head is one cell past the recorded entries. |
| `enumCont_log_apply` | One logged action preserves source semantics and appends exactly one history entry, including a halting or emitting action. |
| `enumCont_history` | Record precisely the actions actually executed by a source run. |
| `enumCont_log_run` | Logging is lockstep with the source, from arbitrary prepared source configurations. |
| `enumCont_undoTM` | The restoration controller alternates inverse head movement with writing the old symbols. |
| `enumCont_undoCfg` | At a restoration checkpoint the heads inspect the last remaining history entry. |
| `enumCont_undoResult` | The completed restoration retains exactly the source's initial work fields and leaves every history tape blank with its head at zero. |
| `enumCont_restore_cell` | Undoing a tape write at the old head restores its original contents, including no-write actions and writes of blank. |
| `enumCont_clock_erase` | Erasing the last clock mark exposes exactly the preceding clock word. |
| `enumCont_undoMid` | Between inverse movement and inverse writing, the source heads are back at their old positions and the last history entry is already erased. |
| `enumCont_undo_back` | The first restoration transition reverses the last source head moves, retains the old symbols in finite control, and erases their history cells. |
| `enumCont_undo_write` | The second restoration transition writes the retained old symbols and backs the history heads up to the preceding entry. |
| `enumCont_undo_empty` | With no history left, one silent transition restores the history heads to zero and halts. |
| `enumCont_undo_run` | A logged live source prefix can be completely undone in `2t+1` steps. |
| `enumCont_first_halt` | Any known halted endpoint is reached at the first halting time, with a live source at every earlier time. |
| `enumCont_bufferAction` | Administrative actions preserve the source bank and only move the native input and the final capture tape. |
| `enumCont_undoEntry` | Entry into restoration moves all history heads from the right blank to the newest entry, leaving source heads fixed. |
| `enumCont_cleanTM` | A clean subroutine logs and captures a source, undoes all source work, rewinds the native input and captured word, and halts silently. |
| `enumCont_cleanCfg` | Clean administrative configurations expose only the native and capture heads. |
| `enumCont_clean_capture` | The clean subroutine's first phase is the public captured simulation of the logged source. |
| `enumCont_clean_undo_entry` | After source halt, one silent dispatch parks every history head on its last entry and starts the captured restoration, retaining the source output. |
| `enumCont_clean_restore` | The captured restoration returns within `2t+1` steps with the original source work restored and its completed output retained separately. |
| `enumCont_buffer_apply` | Moving the clean subroutine's two exposed heads preserves every tape and the empty physical output. |
| `enumCont_rewind` | A mandatory left step followed by a boundary scan restores the native head in at most its old position plus two steps. |
| `enumCont_clean_buffer_rewind` | The retained output word rewinds without being erased. |
| `enumCont_clean_complete` | A halting source call can be made clean: retain its output on the final tape, restore every source work field, blank all histories, and rewind both exposed heads. |
| `enumCont_concatTM` | The assembly source emits native input followed by the candidate already on its sole work tape. |
| `enumCont_concatCfg` | Assembly configurations keep the candidate word fixed while exposing the input head, candidate head, and emitted prefix. |
| `enumCont_concat_native` | The native-input scan emits exactly the remaining input and switches to the candidate phase, preserving the candidate and its head at zero. |
| `enumCont_concat_candidate` | The candidate scan appends the exact tape word to the emitted native input and halts at its right blank. |
| `enumCont_concat_run` | Assembly from the candidate seam emits exactly `x ++ s` in `\|x\|+\|s\|+2` steps. |
| `enumCont_prepared_comp` | Buffered composition also works from a prepared first-machine work configuration. |
| `enumCont_round_seam` | The prepared assembly source occupies tape zero; the composition buffer and verifier work tapes are exactly blank at the candidate seam. |
| `enumCont_verifier_call` | The prepared verifier call accepts the exact assembled input `x ++ s`. |
| `enumCont_returnAction` | Relabel live states and redirect halt to a live return state, preserving the complete action. |
| `enumCont_returnCfg` | The live-return correspondence preserves all configuration fields except the control state, including work-tape results. |
| `enumCont_return_run` | A host with the redirected transition table simulates a source through its first halt and returns the exact completed configuration. |
| `enumCont_clean_verifier` | Combining the prepared verifier call with the clean wrapper gives a repeatable call: the candidate is retained, all other original source work is restored to blank, and the sole verdict is held on the capture tape. |
| `enumCont_padAction` | Pad an action with inactive high tapes and embed its finite control. |
| `enumCont_padCfg` | Pad a source configuration with blank stationary high tapes. |
| `enumCont_pad_apply` | Padding commutes with one action; the new high tapes remain blank. |
| `enumCont_pad_run` | A machine may run on an initial tape block of a larger controller. |
| `enumCont_sources` | Three finite source routines share a common padded tape block. |
| `enumCont_endsAction` | Move or write the candidate at tape zero and the final capture tape, preserving every intervening tape. |
| `enumCont_bodyTM` | The concrete body uses one clean source block for initialization, verification, and increment. |
| `enumCont_increment_call` | Starting assembly in its candidate phase supplies just that candidate to the catalog incrementer. |
| `enumCont_pad_words` | Padding preserves the candidate-on-zero convention when the source has at least one work tape. |
| `enumCont_pad_init` | The same padding identity for empty initial work is valid even when the source machine has no work tapes. |
| `enumCont_overwrite` | Overwriting the first remaining candidate cell extends the completed prefix and drops the old cell, also when the old word is initially empty. |
| `enumCont_sparse_clear` | The erased capture prefix consists entirely of blanks. |
| `enumCont_pairCfg` | Tape configurations for the administrative copy and rewind scans. |
| `enumCont_ends_apply` | The two-ended administrative action changes exactly those tape cells and their common head, preserving native input and physical silence. |
| `enumCont_sparse_blanks` | A sparse list of blank entries is an everywhere blank tape. |
| `enumCont_sparse_some` | Lifting every word symbol into the sparse representation gives the usual buffer tape. |
| `enumCont_copy_scan` | The copy scan overwrites the candidate from left to right and erases each captured symbol. |
| `enumCont_pair_rewind` | Rewind the two endpoint heads together across the completed candidate. |
| `enumCont_copy_complete` | Copying a captured word at least as long as the old candidate completely replaces it, erases capture, and restores the canonical seam in linear time. |
| `enumCont_log_words` | Empty history adds only blank stationary tapes to a candidate seam. |
| `enumCont_extend_words` | Appending one output tape to a candidate seam has the two-endpoint tape layout used by the administrative controller. |
| `enumCont_clean_entry_words` | The clean wrapper's entry configuration at a prepared source seam. |
| `enumCont_clean_exit_words` | The completed clean call has restored the candidate seam and retained only its captured output on the last tape. |
| `enumCont_body_call` | A clean call inside the body redirects the clean wrapper's first halt to the appropriate live administrative state. |
| `enumCont_pair_words` | With empty capture and zero endpoint heads, the administrative tape layout is exactly the public canonical candidate seam. |
| `enumCont_body_start` | Initialization runs the clean unary generator, copies its marks as false candidate bits, erases the marks, and rewinds to the canonical anchor. |
| `enumCont_body_depart` | A genuine round leaves the anchor in one silent stationary transition. |
| `enumCont_body_accept` | A captured true verdict emits the sole physical accepting bit and halts. |
| `enumCont_body_reject` | A false verdict is erased before entering the clean increment call. |
| `enumCont_increment_cases` | The catalog's empty overflow output preserves the old candidate. |
| `enumCont_body_check` | The increment-result check preserves all fields and chooses the anchor on overflow or the copy phase on a nonempty result. |
| `enumCont_body_increment` | A clean increment call followed by copy and rewind implements the exact stalled fixed-width step. |
| `enumCont_body_round_raw` | Starting just after departure, one verifier call either emits acceptance or clears the verdict and completes one exact candidate update. |
| `enumCont_absorb` | An anchor whose transition is a stationary self-loop preserves its complete configuration for every subsequent step. |
| `enumCont_agree_run` | Two transition tables differing only at the anchor agree on every run prefix that has not yet visited that anchor. |
| `enumCont_first_anchor` | The first visit to a stopped anchor transfers to the active machine with the same full endpoint and no earlier anchor visit. |
| `enumCont_halt_transfer` | A halted stopped run never visited the live absorbing anchor. |
| `enumCont_body_agree` | The active and stopped body have identical transitions away from the anchor. |
| `enumCont_body_start_guarded` | Startup satisfies the loop export's first-anchor guard as well as its full canonical configuration equality. |
| `enumCont_body_round_guarded` | The active round has positive duration and no strict interior visit to the anchor. |
| `enumCont_lift_call` | A prepared source call may use the initial tape block of the shared source machine; padding preserves its halt and exact emitted word. |
| `enumCont_lift_init` | Initial calls pad correctly even for a zero-work-tape source. |
| `enumCont_common_bound` | One input-independent polynomial bounds both body phases. |
| `enumCont_from_body` | A concrete body with polynomial startup and exact seam restoration gives the frozen enumerator configuration contract by the audited loop export. |

## Flat delivery and reproduction

The archive is `fill-ch2-e2cont-A.zip`, with every member at the archive root and `SHA256SUMS` at the root. `EXP.lean` is the complete modified source for repository path `TCSlib/Complexity/ClassNP/EXP.lean`. The numbered patch series and incremental bundle contain the single recorded commit, with the exact required base as the bundle prerequisite. `git bundle verify` succeeds. `replay_patch.py` applies the patches in a temporary index without checking out or changing any branch, and reproduces the delivered Git tree exactly.

After extracting the flat archive, verify `sha256sum -c SHA256SUMS`. With the pinned toolchain and dependencies available, the included instruments can be run from the extracted directory:

```bash
python3 freeze.py --repo /path/to/tcslib
python3 sweep.py --repo /path/to/tcslib --oleans /path/to/new-fresh-olean-tree
python3 run_axioms.py --repo /path/to/tcslib --oleans /path/to/new-fresh-olean-tree
python3 replay_patch.py --repo /path/to/tcslib
```

The sweep output path should be new and empty. The axiom check must use the sweep's output path. Intended maintainer integration is `git am -3` of the supplied patch; this delivery performs no integration, push, or PR.

The ZIP also includes the freeze, policy lint, owned/downstream checks, final sweep, final axiom/root, environment, cache-setup, bundle-verification, and patch-replay logs, plus the verification instruments and optional executor compatibility source.

## Glossary

- **Seam:** the complete configuration expected between subroutines: native input head 1, work heads 0, candidate on tape 0, blank scratch, and empty physical output.
- **Anchor:** the live controller state marking a candidate seam.
- **Stalled increment:** a fixed-width increment that keeps the old word when overflow occurs; fuel, not the stalled state, determines exhaustion.
- **Admission root:** a checked kernel declaration whose type or body directly mentions `sorryAx`, found by traversing the full dependency closure.
- **`fU` / `fF`:** fixed catalog coefficients for the initializer and the separately obtained loop-fuel generator, respectively.

## ===== audits/ch2-epoch2-agent-reports/batchB.md =====

# Chapter 2, epoch 2, batch B — partial continuation delivery

**Status: incomplete. None of the three headline targets is closed.** This archive
uses the brief's partial-delivery exception. It is not a passing completion of the
batch's no-`sorryAx` gate. The first target is reduced to one explicit native
verifier-construction obligation; the second and third targets are untouched to
preserve fill order. All 32 new private declarations are complete, with no new
private admissions.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Base branch: `complexity/arora-barak-ch1`.
Base commit: `6c09453e6af59ff1575060b66196d28812800d24`.
Working branch: `fill/ch2-e2-B`, created from that exact base as the brief requires.
Delivery commit: `43620097f4f6d934ed383e54eb0ff950e4bdfe99`.
One agent; no delegation. No push or PR was made.

## Target disposition and exact frontier

| Order | Target | Disposition |
|---|---|---|
| 1 | `ntime_poly_subset_NP` | Partial. Coefficient `2*a`, verifier language, and the entire certificate equivalence are supplied. The remaining local goal is `choiceVerifier N (2*a) c ∈ P`. |
| 2 | `NP_subset_iUnion_NTIME` | Original admission, unchanged; not advanced past the first target. |
| 3 | `NP_eq_iUnion_NTIME` | Original admission, unchanged. |

The completed work comprises:

- Unique splitting and a finite split-search specification, including explicit
  failure when no split exists.
- Forward padding and backward truncation of accepting choice words, using
  all-branch halting. The certificate equivalence has no admitted dependencies.
- A native deterministic simulation phase for a fixed NDTM, with disjoint input,
  choice and captured-output tapes. Its prepared-configuration contract has exact
  time `|u|+1`, including the final decision transition.
- A native three-tape copying phase. Given a prepared unary split countdown, it
  copies the input prefix and choice suffix in exactly `|x++u|+1` transitions,
  preserving empty physical output throughout.

**Neither prepared-configuration theorem is a theorem about running from the
machine's ordinary blank-tape initial configuration.** The finite search is a
Lean function specification, not a native polynomial-time implementation. No
polynomial-time conclusion is inferred merely from its being a total function.

To close the first target, a continuation must:

1. Implement native input-length measurement, the explicit polynomial arithmetic,
   and `certificateSplit`; budget them on all inputs before assuming validity.
2. On search failure, halt with the singleton false verdict. On success, prepare
   the unary split countdown and reset the physical input head to its proper
   initial position before the copying phase.
3. Embed the proved copier and simulator in one finite machine with disjoint
   source and administrative tapes. Rewind the two copied buffers from their
   right blanks, including the unconditional first left move and empty-word cases.
4. Enter the simulation with the source's initial finite state, blank source work
   tapes, empty capture tape, virtual input head one, and choice head zero. Preserve
   the administrative tapes and physical-output silence across phase boundaries.
5. Prove the timed phase-composition invariant and a single pointwise polynomial
   bound for all inputs, then apply `mem_P_of_dtime_le` or `mem_P_iff` to the
   remaining verifier-membership goal.

Only then should the continuation proceed to the guessing construction and the
final antisymmetry theorem. No `exists_comp_partial` or untimed `Computes`
substitution is used in this delivery.

## Binding forward invariant table

Each discharge below is explicitly limited to the proved phase's preconditions.

| Required component | Lemmas and remaining integration work |
|---|---|
| Source input and boundary clamping | `choiceCore_step` uses the public `bufferTape_inputSymbol` and `virtualMove_correct` lemmas. The source input has its own exact buffer, so it cannot expose the first certificate bit. `choiceCore_run` preserves the guarded read and clamping through all steps. `choiceCore_initial_tag` covers initial position one, including empty input. Installing that prepared buffer from the native initial configuration remains open. |
| Choice tape and choice alignment | `choiceCore_step` reads exactly `u[j]` and advances the choice head once. `choiceCore_run` identifies the source run with `runWith (u.take t)`. Its halted-source case absorbs all subsequent source steps. `choiceCopy_timed` supplies exact copied words once the countdown is prepared. Connecting the administrative phases before source step zero remains open. |
| Source state and disjoint tapes | `choiceCore` has finite control `Option N.State × Bool × Option Bool`. `choiceTapes` partitions source work tapes from three auxiliary tapes. The full configuration equalities in `choiceCore_step` and `choiceCore_run` preserve all source tapes and positions, not just the verdict. The integrated startup embedding remains open. |
| Output capture and exact verdict | `captureEmission_correct`, `capturedSummary_true`, `choiceCore_step`, `choiceCore_finish`, and `choiceCore_timed`. Every emission, including one on a halting transition, updates the complete capture tape and its finite summary. Physical output stays empty until the final transition. The final bit is true exactly for a halted source with output `[true]`; all other completed outputs and a live `[true]` reject. |

The implementation uses a physical head on the copied input and a finite boundary
tag instead of the sketch's binary position counter. This is the existing guarded
input-relocation representation proved by `virtualMove_correct`; its overhead is
one native step per source step. A separate capture tape retains the complete
output; the finite summary is only an exact singleton-test aid. This representation
choice and the partial frontier are recorded in an **append-only implementation
note** on the first target's docstring. Its original sketch and attribution remain.

## Binding reverse-direction five-step mapping

| Step | Status |
|---|---|
| 1. Evaluate the certificate length, initialize countdown, and schedule guesses independently of their values | Open; no reverse-direction machine or lemma is claimed. |
| 2. Cover and extract every exact-length certificate at its actual physical choice positions, including zero coefficient | Open. The forward simulator's choice alignment is not a proof of this reverse contract. |
| 3. Assemble the verifier input and run the relocated, captured verifier with identical tables outside guessing | Open; no reuse of the prepared forward core is asserted as a completed reverse construction. |
| 4. Prove all-branch totality, branch acceptance equivalence and common-budget padding | Open. The public epoch-1 monotonicity lemmas remain available, but this delivery supplies no reverse-machine hypotheses for them. |
| 5. Normalize the complete construction's time bound into a fixed-degree `NTIME` component | Open; no unproved machine-cost estimate is presented as a proved bound. |

## All new declarations

All names below are private within `Complexity`. There are 10 definitions and 22
lemmas; no new public declarations, axioms, unsafe declarations, or private sorries.

| Kind | Private declaration |
|---|---|
| lemma | `certificate_split_strictMono` |
| lemma | `certificate_split_unique` |
| def | `certificateSplit` |
| lemma | `certificateSplit_spec` |
| lemma | `certificateSplit_none_iff` |
| lemma | `certificateSplit_complete` |
| def | `choiceVerifier` |
| lemma | `choiceVerifier_append` |
| lemma | `choiceVerifier_no_split` |
| lemma | `acceptsWithin_iff_of_halts` |
| lemma | `choice_budget_le` |
| lemma | `choice_certificate_iff` |
| def | `capturedSummary` |
| def | `captureEmission` |
| lemma | `captureEmission_correct` |
| lemma | `capturedSummary_true` |
| def | `choiceTapes` |
| def | `choiceCore` |
| def | `choiceCoreCfg` |
| lemma | `choiceCore_step` |
| lemma | `choiceCore_run` |
| lemma | `choiceCore_finish` |
| lemma | `choiceCore_timed` |
| lemma | `choiceCore_initial_tag` |
| def | `copyTapes` |
| def | `choiceCopy` |
| def | `choiceCopyCfg` |
| lemma | `choiceCopy_prefix_step` |
| lemma | `choiceCopy_suffix_step` |
| lemma | `choiceCopy_prefix_run` |
| lemma | `choiceCopy_suffix_run` |
| lemma | `choiceCopy_timed` |

## Admissions and frozen surface

The owned file still contains exactly eight explicit `sorry` occurrences, the same
count as the base. Their current declarations and line numbers are:

| Declaration | Explicit `sorry` line |
|---|---|
| `ntime_poly_subset_NP` | 682 |
| `NP_subset_iUnion_NTIME` | 713 |
| `NP_eq_iUnion_NTIME` | 723 |
| `ntime_expPow_subset_NEXP` | 743 |
| `NEXP_subset_iUnion_NTIME` | 764 |
| `NEXP_eq_iUnion_NTIME` | 775 |
| `EXP_eq_NEXP_of_P_eq_NP` | 811 |
| `P_ne_NP_of_EXP_ne_NEXP` | 817 |

The first three rows are unfinished in-scope targets, permitted here only under
the brief's partial-delivery exception. They are not sanctioned admitted
dependencies for a completed batch. The final five rows are the untouched epoch-3
padding cluster. All other campaign admissions are unchanged.

`verification/surface-check.json` and its reproducible script confirm:

- Exactly one changed tracked path:
  `TCSlib/Complexity/ClassNP/Nondeterminism.lean`.
- All eight existing public declaration headers are identical after stripping
  comments and normalizing whitespace, with identical order and no additions or
  removals.
- From the second target's docstring through the end of the file, source bytes are
  identical to the base. This includes both later in-scope targets and all padding.
- Every original block comment is preserved, except for the documented append-only
  note on the first target. No attribution was changed.
- `git diff --check` passes. The file exceeds the 600-line target because ownership
  restricts this phase's private helpers to this file; it remains below 1000 lines.

Requested shared lemmas: **none**. Statement escalations: **none**; the frontier is
missing construction work, not a demonstrated defect in a frozen statement.

## Verification

- Final full sweep: **PASS**, all 53 modules, exit 0, zero `error:` lines, fresh oleans.
- Admission warnings: **32**, unchanged from the base campaign count.
- Axiom command: exit 0; all 35 requested declarations were printed.
- New private declarations: **32/32 within** `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Headline targets: **0/3 closed**; all three contain `sorryAx`. The complete-batch axiom gate fails.
- Style lint: **0 FAIL, 0 WARN** over the ten ClassNP files.
- Surface comparison, patch replay and git bundle verification: **PASS**.

The environment uses Lean 4.25.0 and the committed dependency manifest. The required
`lake exe cache get` was invoked once. It ended with server failures and a missing
shared temporary cache file. Completed downloads were copied to an isolated task
cache and unpacked; disk exhaustion during unpacking required pruning this
checkout's generated cache to the campaign dependency closure. These setup
failures are recorded in the included setup logs. The final sweep below was run
after recovery. No `lake build` was run.

The bootstrap was resumed after its first missing dependency. Iteration checked
the owned module; the final owned-and-downstream check and the final full sweep
both use the committed `scripts/lean_check_tree.sh`, which removes each old olean
and requires a fresh nonempty replacement, Lean exit zero, and no `error:` line.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

The full axiom output is `verification/axiom-print.log`. Its three target lines
are reproduced here to make the incomplete status unmistakable:

```text
'Complexity.ntime_poly_subset_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Archive and replay

The archive contains this report, the full modified source at its repository path,
one `git format-patch`, an incremental git bundle, the raw final sweep and axiom
logs, the module order, surface and style checks, and `SHA256SUMS`. The checksum
file covers every other archive member.

The bundle verifies against the recorded base. The patch was applied to a separate
copy of the base source and reproduced the delivered source byte-for-byte.
`verification/patch-replay.log` and `verification/bundle-verify.log` record these
checks. The patch preserves the local commit's Codex authorship. No remote branch
was modified.

To recheck the surface in a repository containing the base and applied patch, run
`python3 verification/verify_surface.py /path/to/tcslib`. For elaboration, use the
brief's full module loop and the included `AxiomChecks.lean` on the resulting fresh
olean tree. A zero-error sweep here certifies elaboration of a partial source; it
does not close the three headline proofs.

## ===== audits/ch2-epoch2-agent-reports/batchB-cont.md =====

# Chapter 2, E2 continuation, batch B — partial delivery

**INCOMPLETE: one of three public targets is closed.** This delivery uses the
continuation/partial-delivery allowance in `briefs/ch2-e2cont-batchB.md` and
`briefs/ch2-epoch2-batchB.md`. It is not a passing completion of the entire
batch's no-`sorryAx` gate. The forward compilation is complete; the reverse
compilation has proved native components but still lacks its integrated
controller. The equality remains untouched to preserve target order.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Requested base branch: `complexity/arora-barak-ch1`.
Required and actual source base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
Working branch: `fill/ch2-e2cont-B`.
Delivery commit: `2239b0f3b128c5acf4f35d5e83918b8aa0e6b492`.
The continuation brief was read from `cc103db9d9f00e28924a685919629be9b3ec1b63`,
the next commit on the requested branch; the source branch was then created
from the brief's required base. No other branch was changed. No push or PR.
Single-agent execution; no delegation.

## Public targets and exact remaining frontier

| Order | Target | Result |
|---|---|---|
| 1 | `ntime_poly_subset_NP` | **Proved.** Native split search, failed-split rejection, paired-input loading, both rewinds, source simulation, and the uniform polynomial bound close `choiceVerifier ∈ P`. Kernel admission roots are empty. |
| 2 | `NP_subset_iUnion_NTIME` | **Incomplete.** Proved a native guessing phase, its exact physical-position extraction/coverage, its unary-generator instance, and final time normalization. The whole NDTM controller remains the only admission in this target. |
| 3 | `NP_eq_iUnion_NTIME` | Original admission, byte-identical together with its docstring. Not filled ahead of target 2. |

The first target retains the predecessor's complete certificate equivalence.
The second target now extracts the verifier's timed witness and applies the
proved `cont_guess_normalize`. Its exact remaining local goal is:

```lean
-- L : Language Bool; C c : ℕ; V : Language Bool
-- hcert : ∀ x, x ∈ L ↔ ∃ u, u.length = C * (x.length + 1)^c ∧ x ++ u ∈ V
-- M : FinTM Bool; A d : ℕ
-- hM : M.DecidesInTime V (fun n => A * (n + 1)^d)
⊢ ∃ (K r : ℕ) (N : FinNDTM Bool),
    N.DecidesInTime L (fun n => K * (n + C * (n + 1)^c + 1)^r)
```

The native `contGuessTM` is a **phase**, not that missing decider. Its source
scheduler's completed state is a live, stationary return state; the phase
never claims all-branch halting. `cont_poly_guess_phase` runs its scheduler
on the unary word of length `n`, not on an arbitrary original input word.
The polynomial scheduler budget may include absorbed source steps; a host
must dispatch on an actual completed scheduler (for example its first halt)
and prove that seam, rather than infer a native clock from an upper bound.

A continuation should do the following, in this order:

1. Build the native host preserving the original input and installing its
   length-only scheduler/countdown. The library unary generator is available;
   its function-level contract alone does not assert value-independent
   running times on arbitrary original input strings. Relocating it to the
   unary input, or proving an equivalent normalization of input reads, is an
   explicit missing seam.
2. Embed the proved guessing table with source and administrative tapes
   disjoint. Translate its physical write mask into the complete branch
   word, including the startup offset; all non-guess choices are ignored.
   Reuse `cont_guess_coverage` at the actual scheduler completion time.
3. Assemble the preserved original input followed by the captured guesses.
   Prepare the verifier with blank source tapes, empty capture output and
   virtual head one; prove the two tables coincide outside guessing. Capture
   its completed output, including any halting emission, and issue one bit.
4. Prove every branch completes, that its certificate has the exact required
   length, and that branch acceptance is precisely verifier membership. Use
   a common upper bound; actual verifier halting times may depend on guesses.
5. Bound the entire construction by the displayed envelope. The proved
   `cont_guess_normalize` then closes target 2, including forward padding and
   backward truncation. Only then fill target 3 by antisymmetry.

## Forward invariant table: complete discharge

| Required component | Discharge |
|---|---|
| Source input and boundary clamping | `cont_parse_run`, `cont_copy_run`, `cont_rewind_input`, `cont_start_core` install the exact undoubled input buffer and initial virtual head. `cont_core_run` embeds the unchanged `choiceCore_step`/`choiceCore_run`, whose `bufferTape_inputSymbol` and `virtualMove_correct` enforce both blanks and repeated outward-move clamping. `choiceCore_initial_tag` includes the empty input. The choice suffix is on a separate tape. |
| Choice tape and source-choice alignment | `cont_copy_run` copies exactly the suffix; `cont_rewind_choices` returns its head to zero. Administrative steps do not invoke the source simulation. The unchanged `choiceCore_run` consumes one copied bit per source step, absorbing halted source configurations. |
| Source state and disjoint tapes | `contLoadCfg` keeps all original source tapes and the source-output capture tape blank during setup. `cont_start_core` installs the complete prepared initial configuration. `cont_core_run` is an exact configuration equality using the public state-renaming definitions; it preserves the predecessor's tape partition and full source-state invariant. |
| Output capture and exact verdict | All successful loader steps are silent. `cont_pair_empty` emits exactly `[false]` for split failure. The unchanged `captureEmission_correct`, `capturedSummary_true`, and `choiceCore_timed` capture all source emissions and accept exactly a halted source with output `[true]`. A live `[true]`, empty output, false output, and multi-bit output reject. `cont_pair_computes` and `cont_split_answer` connect this to the completed verifier output. |

The predecessor's `choiceCopy` family and all other 32 private declarations
are retained byte-for-byte. The new loader uses the library's encoded split
output directly, so it does not need a separate unary split countdown. This
is documented in an append-only note on the first public target.

## Split convention and time ledger

The exact bridge in this owned file is

```lean
cont_split_bridge (C c m : ℕ) : solveSplit C c m = certificateSplit C c m
```

It is proved by reflexivity. **There is no coefficient shift for batch B.**
The recorded `solveSplit (C+1) c = certificateSplit C c` vocabulary note
concerns the marker-padding parser in `ClassNP/NP.lean`, whose formula has
coefficient `C+1`. This file's predecessor already defines its own
`certificateSplit C c` using coefficient `C`. Therefore the public forward
target instantiates split search at coefficient `2*a`, degree `c`, exactly.
Applying the unrelated shift here would be incorrect.

| Phase | Proved bound or equality |
|---|---|
| Library split search | `A * (m+1)^(c+2)` on every original verifier input, successful or failed |
| Emitted split length | At most `2*m+2`, by `cont_split_length` |
| Paired parser | Exactly `2*|x|+2`, by `cont_parse_run` |
| Suffix copy | Exactly `|u|`, by `cont_copy_run` |
| Buffer rewinds and dispatch | Exactly `|x|+|u|+3`, by `cont_start_core` |
| Unchanged source core | Exactly `|u|+1`, by `choiceCore_timed` |
| Full paired machine | `3*|x|+3*|u|+6 ≤ 3*(|pairEncode x u|+1)` |
| Timed composition startup | At most split-search budget plus emitted length plus 2, by `bufferedComp_start` |
| Complete verifier | At most `(A+13)*(m+1)^(c+2)`, by `cont_choiceVerifier_mem_P` |

All bounds are pointwise, including coefficient zero, degree zero and empty
strings. No untimed composition is used. The second stage is proved on every
possible first-stage output (valid pairs or the empty failure word); the
proof does not substitute an arbitrary time function at an inflated length.

## Reverse five-step contract: proved pieces and limitations

| Binding step | Proved here | Remaining |
|---|---|---|
| 1. Compute the explicit length, initialize control, and schedule guesses independently of their values | `contEmissionMask`, `cont_mask_length`, `cont_mask_count`; `contGuessTM` uses the deterministic scheduler's source bank and never reads guessed data. `cont_poly_guess_phase` supplies a polynomial unary-generator instance with a schedule depending only on `n`. | The whole host's original-input preservation, native unary-input preparation/relocation, countdown installation and phase entry. No completed implementation of this entire step is claimed. |
| 2. Certificate coverage and extraction at the actual physical write positions, including `C=0` | `contSelect`, `cont_select_length`, `cont_select_surjective`, `cont_guess_step`, `cont_guess_run`, `cont_guess_coverage`, `cont_poly_guess_phase`. They select emission positions, not the first `Q(n)` physical choices. Zero writes extract and cover only `[]`. | Lift the standalone phase's correspondence to the complete branch word and its startup offset. |
| 3. Assemble `x++u`, initialize and capture the relocated verifier, identical tables outside guessing | The forward construction provides relevant loader and timed relocation precedents, but is not a reverse-host proof. | Entire integrated reverse assembly/verifier phase and its all-branch termination proof. |
| 4. Branch acceptance equivalence and padding to a common bound | `cont_guess_normalize` proves budget transfer using all-branch halting and `acceptsWithin_iff_of_halts`, once a whole-decider contract is provided. | Acceptance equivalence and all-branch totality for the actual host. |
| 5. Normalize the complete envelope into one `NTIME` component | `cont_guess_time_bound` proves the exact coefficient `K*(C+1)^r*2^(r*max 1 c)` and exponent `r*max 1 c`; `cont_guess_normalize` packages the result. | Establish the displayed complete-envelope hypothesis for the missing host. |

## Library and existing contracts consumed

| Contract | Use |
|---|---|
| `Turing.FinTM.computesFunInTime_splitSolve` | The actual first-stage machine in `cont_choiceVerifier_mem_P` |
| `Turing.FinTM.computesFunInTime_polyUnary` | Concrete scheduler in `cont_poly_guess_phase` |
| `Turing.captureAction` | The transition transformer in `contGuessTM`; its one-step correspondence is proved locally in `cont_guess_step` |
| `Turing.Action.mapState`, `Turing.Cfg.mapState` | Embed the unchanged deterministic core without duplicating these public definitions |
| `Turing.MultiTapeTM.runFrom_comm_of_step` | Exact core embedding invariant |
| `Turing.FinTM.bufferedComp_start`, `bufferedSecondCfg_run` | Timed, captured first stage and relocated paired machine in the completed forward compiler |
| `Complexity.mem_P_iff` | Conclude polynomial-time verification and obtain the reverse verifier witness |
| `Complexity.succ_pow_le`, `Turing.NDTM.HaltsWithin.mono`, predecessor `acceptsWithin_iff_of_halts` | Reverse-envelope normalization and correct acceptance transfer |

`capture_run` and the private `timed_rewind` are not falsely claimed as
invoked contracts. The forward source core already captures output; this
host directly loads its prepared tapes, proves its own two timed rewinds,
and then uses the public timed buffered-composition interface.

## All 36 new private declarations

Seven definitions and 29 lemmas; no new public declarations or private admissions.

| Kind | Name |
|---|---|
| lemma | `cont_split_bridge` |
| def | `contPairTM` |
| def | `contLoadCfg` |
| lemma | `cont_core_run` |
| lemma | `cont_rewind_choices` |
| lemma | `cont_rewind_input` |
| lemma | `cont_write_apply` |
| lemma | `cont_load_read` |
| lemma | `cont_load_right` |
| lemma | `cont_copy_run` |
| lemma | `cont_start_core` |
| lemma | `cont_suffix_run` |
| lemma | `cont_parse_double` |
| lemma | `cont_parse_separator` |
| lemma | `cont_parse_run` |
| lemma | `cont_pair_computes` |
| lemma | `cont_pair_empty` |
| def | `contSplitWord` |
| lemma | `cont_split_length` |
| lemma | `cont_split_answer` |
| lemma | `cont_choiceVerifier_mem_P` |
| def | `contSelect` |
| lemma | `cont_select_length` |
| lemma | `cont_select_surjective` |
| def | `contEmissionMask` |
| lemma | `cont_mask_length` |
| lemma | `cont_mask_count` |
| def | `contGuessTM` |
| def | `contGuessCfg` |
| lemma | `cont_guess_step` |
| lemma | `cont_guess_run` |
| lemma | `cont_guess_initial` |
| lemma | `cont_guess_coverage` |
| lemma | `cont_guess_time_bound` |
| lemma | `cont_guess_normalize` |
| lemma | `cont_poly_guess_phase` |

## Frozen surface, admissions and policy

Only the tracked path `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changed.
All eight public headers are identical after comment stripping and whitespace
normalization; public order and inventory are unchanged. The original 32-private
block is byte-identical. All original docstrings remain, with append-only
implementation/checkpoint notes on the first two targets. From the third
public target's docstring through the end, source bytes are unchanged.
`git diff --check` passes. `surface-check.json` and `verify_surface.py` provide
reproducible evidence.

The final file has **1,670 lines, 88,871 UTF-8 bytes**. SHA-256:
`7268c31897087c78aa95f3849e855692e3ff5edcfb3a02306c8e8bfc1af9819e`.

| Remaining explicit admission | Line | Disposition |
|---|---:|---|
| `NP_subset_iUnion_NTIME` | 1564 | In-scope partial frontier described above |
| `NP_eq_iUnion_NTIME` | 1574 | In-scope, untouched pending target 2 |
| `ntime_expPow_subset_NEXP` | 1594 | Epoch 3, untouched |
| `NEXP_subset_iUnion_NTIME` | 1615 | Epoch 3, untouched |
| `NEXP_eq_iUnion_NTIME` | 1626 | Epoch 3, untouched |
| `EXP_eq_NEXP_of_P_eq_NP` | 1662 | Epoch 3, untouched |
| `P_ne_NP_of_EXP_ne_NEXP` | 1668 | Epoch 3, untouched |

The owned file's explicit admission count falls from 8 to 7. The five padding
admissions remain exactly as inherited. No other file's admissions changed.

Statement escalations: **none**; the unfinished compiler is missing proof/
construction work, not evidence of a false frozen statement. Requested shared
lemmas: **none**. File-size exception: the brief's exclusive ownership and its
prohibition on moving the predecessor's families require these helpers to stay
in the owned file. A serial split/dedup is deferred to the recorded E5 work;
no other source file is changed to evade this ownership rule. The style lint
has 0 FAIL and 2 WARN over the ten ClassNP files: this size warning and the
pre-existing `TMSAT.lean` size warning. No new compiler lint warnings occur
in the owned module beyond its seven documented admissions.

## Verification

- Lean **4.25.0**; mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**.
  Installed dependency revisions match the manifest (`environment.log`).
- Required `lake exe cache get`: invoked **once**, completed successfully
  (`cache-get.log`). No `lake build` invocation. The pinned existing toolchain
  was reused; generated dependency artifacts outside this task's import
  closure were pruned locally after cache extraction to recover disk space.
- Final **57/57** fresh-module sweep: exit **0**, **zero `error:` lines**,
  `FULL_SWEEP_COMPLETE`. The committed check script removes each old olean
  before checking and requires a fresh nonempty replacement.
- Final admission warnings: **27**, down from the pinned campaign baseline 28.
- Owned-and-downstream recheck: pass (`downstream-final.log`).
- Kernel closure traversal and prints on the final fresh tree: exit **0**.
  First target has empty admission roots and only the standard triple.
  **All 36 new helpers and all their generated descendants (114 declarations
  total) have empty admission roots and axiom sets within the standard triple.**
- The other two public targets still depend on `sorryAx`, each rooted in its
  own admission. Therefore **the complete-batch axiom gate does not pass**.
  The instrument's `PARTIAL_CLOSURE_AUDIT_PASS` means exactly the stated partial
  expectations passed, not that those targets were completed.
- Statement/private/docstring/padding checks, two-patch replay and incremental
  git-bundle verification: pass. Patch replay reproduces the source byte-for-byte.

Axiom prints and target admission roots:

```text
'Complexity.ntime_poly_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
TARGET ROOTS Complexity.ntime_poly_subset_NP: []
TARGET ROOTS Complexity.NP_subset_iUnion_NTIME: [Complexity.NP_subset_iUnion_NTIME]
TARGET ROOTS Complexity.NP_eq_iUnion_NTIME: [Complexity.NP_eq_iUnion_NTIME]
```

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## Flat archive and replay

`fill-ch2-e2cont-B.zip` is flat: every member, including `SHA256SUMS`, is at
the archive root. `Nondeterminism.lean` is the complete modified source and
maps to `TCSlib/Complexity/ClassNP/Nondeterminism.lean` in the repository.
The archive also contains this report, two format-patches, the incremental
git bundle, the full final sweep and axiom logs, the axiom program, module
order, environment/cache record, surface verifier, declaration inventory,
style result, and replay/bundle validation logs. `SHA256SUMS` covers every
other archive member; no toolchain, dependency cache, or olean is included.

From an extracted archive, `sha256sum -c SHA256SUMS` verifies the payload.
Apply the two numbered patches in order with `git am` to a checkout of the
required base; this preserves Codex authorship. The bundle is an alternative
containing the same two commits and requires that base to be available.
For elaboration, use the committed 57-module order/check script under the
pinned toolchain, then run `AxiomChecks.lean` with the fresh olean tree and
pinned package build directories on `LEAN_PATH`. The source-header verifier
can be run as `python3 verify_surface.py /path/to/tcslib` on the delivery branch.

## Notation

`n` is original input length; `m` is a verifier input length. `x,u` are input
and certificate words; `|w|` is word length. `C,c` are the exact certificate
coefficient and degree. `a` is the original NTIME coefficient. `A` denotes
the relevant deterministic time coefficient; `d` is the verifier's degree.
`K,r` are the missing reverse compiler's whole-time envelope parameters.
`Q(n)=C(n+1)^c`; `T` is a physical scheduler budget. Machine and lemma names
refer to the declarations in the delivered source and pinned library.

## ===== audits/ch2-epoch2-agent-reports/batchB2.md =====

# Chapter 2, E2 continuation, batch B2 — complete

**COMPLETE: both owned targets are proved; the full axiom gate passes.**

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested source branch: `complexity/arora-barak-ch1`.
- Required and actual source base: `e72d95bf35ebf09c21aae7e1959e5d895a345686`.
- Working branch: `fill/ch2-e2cont-B2`.
- Delivery commit: `022cd0f3cf63689b866cc0e7407db62f7e14cc77`.
- The B2 brief was read from branch tip `312a9a5b21ae84953295431a291102b3f0557ff5`,
  then the working branch was created at the brief's required base. The original
  source-branch ref was not moved. No push or PR. Single-agent execution.
- Only tracked source changed: `TCSlib/Complexity/ClassNP/Nondeterminism.lean`.

## Targets

| Order | Target | Result |
|---|---|---|
| 1 | `NP_subset_iUnion_NTIME` | Proved by the integrated native reverse host, `b2_compile`, and the inherited `cont_guess_normalize`. |
| 2 | `NP_eq_iUnion_NTIME` | Proved afterwards by antisymmetry and `ntime_poly_subset_NP`. |

The forward compiler and all 68 inherited private declarations are byte-identical.
No new public declarations, imports, assumptions, or admissions were introduced.

## Binding five-step contract

| Step | Discharging declarations and exact behavior |
|---|---|
| 1. Preserve the input and install a length-only scheduler | `b2Host`, `b2Slots`, `b2_initial`, `b2_copy_step`, `b2_copy_run`, `b2_copy_done`, `b2_rewind_step`, `b2_rewind_done`, `b2_rewind_run`, `b2_start`. The host copies the original word into its assembly buffer and returns the physical input head to one in exactly `2*|x|+2` steps. Both machine banks are blank. `b2UnaryTM`, `b2_unary_read`, `b2_unary_apply`, `b2_unary_step`, `b2_unary_run`, `b2_unary_initial`, `b2_unary_computes`, `b2_unary_mask`, and `b2_unary_first` close the missing scheduler-input seam by exact read normalization. |
| 2. Physical-position extraction and coverage | `b2_guess_step`, `b2_guess_run`, `b2_guess_word_injective`, `b2_guess_coverage`, `b2_host_contract`. Coverage explicitly invokes the inherited `cont_guess_coverage` at the actual first scheduler halt. Full branch words consist of a startup prefix, the scheduler interval, and a completion suffix. Only marked emission positions inside the scheduler interval supply guesses; the startup offset is `2*|x|+2`. |
| 3. Assemble, initialize, simulate, and capture | Guesses append directly after the copied original word, giving exactly `x++u` without a second copy. `b2_guess_return`, `b2_ready_step`, `b2_ready_done`, `b2_ready_run`, `b2_assembly` rewind this word and install `M.tm.initCfg (x++u)` with virtual input head one, blank verifier tapes, and empty captured output. `b2_verify_step` and `b2_verify_run` preserve guarded reads and clamping, all verifier work tapes, and every emission. `b2_verify_finish` emits precisely one verdict. `b2_tables_coincide` proves that both tables are definitionally the same outside live guessing states, for all symbol tuples. |
| 4. All-branch totality and acceptance equivalence | `b2_verify_timed`, `b2_finish`, `b2_host_contract`, `b2_compile`. Every sufficiently long branch yields a certificate of exactly the prescribed length and halts with the verifier's singleton decision bit. Conversely every such certificate is realized. The final verifier may halt at different actual times on different certificates; all branches satisfy the same upper bound, and extra choices are absorbed. |
| 5. Envelope and final normalization | `b2_host_bound` proves the entire native ledger is bounded by `(B+A+5)*(n+Q(n)+1)^(c+d+1)`. `b2_compile` packages the all-branch decider. The unchanged `cont_guess_normalize` applies its exact coefficient/exponent normalization and acceptance padding/truncation. |

### Scheduler-input seam and actual dispatch

`b2UnaryTM` changes only the scheduler's input reads: `some false` and
`some true` both become `some true`, while `none` remains `none`. It does
not change the physical input, work symbols, or input-head motion.
`b2UnaryCfg` identifies every configuration with one on the unary input of
the same length. `b2_unary_run` proves exact lockstep at **every elapsed
time**, and `b2_unary_mask` identifies the emission schedules.

The library's timed unary generator provides the scheduler. `b2_unary_first`
chooses its first halt on the unary word, with a bound from that generator,
and proves that the normalized scheduler on every original word of that
length has the same first halt. The host uses the scheduler's actual
completed state, followed by `b2_guess_return`, to dispatch. A polynomial
upper bound is never treated as an executable clock. The inherited
standalone phase's live return state is not mistaken for a halted decider.

The generator's emissions implement the prescribed number of guesses. Its
source/control bank cannot read the guessed buffer. This is the length-only
scheduler route in the B2 brief, rather than a claim that the library's
function-level contract alone makes arbitrary-input timing independent of
input values.

### Physical choices and edge cases

At input length `n`, the first `2n+2` physical choices are administrative.
The next `τ(n)` choices are interpreted by the emission mask of the unary
scheduler's first-halt run. The inherited selection and coverage proofs,
transferred by `b2_guess_coverage`, realize every word of length `Q(n)`.
All later physical choices are ignored by the deterministic completion.

When `C=0`, the scheduler emits no bits, so its mask has no marked positions
and the only extracted certificate is `[]`. All proofs also cover degree
zero and empty input. The assembly buffer may be empty; its mandatory left
move followed by the left-blank dispatch still installs virtual head one.
The verifier captures its halting-transition emission before testing the
complete output; only the singleton `[true]` accepts.

## Exact time ledger

| Phase | Physical-step bound |
|---|---|
| Original input copy and physical-head rewind | `2n+2` exactly |
| Guessing | `τ(n)` exactly, the scheduler's actual first halt; `τ(n) ≤ B(n+1)^(c+1)` |
| Assembly-buffer rewind and verifier dispatch | `n+Q(n)+2` exactly |
| Verifier simulation, verdict, and absorption | At most `A(n+Q(n)+1)^d+1` |

Thus the common ledger is

\[
H(n)=3n+Q(n)+\tau(n)+A(n+Q(n)+1)^d+5.
\]

Put `m=n+Q(n)+1` and `r=c+d+1`. The proof uses

\[
\begin{aligned}
\tau(n)&\le B(n+1)^{c+1}\le Bm^r,\\
Am^d&\le Am^r,\\
3n+Q(n)+5&\le5m\le5m^r,\\
H(n)&\le(B+A+5)m^r.
\end{aligned}
\]

`cont_guess_normalize` then uses `e=r*max(1,c)` and the coefficient
`(B+A+5)*(C+1)^r*2^e`, exactly as proved by the predecessor. Both enlargements
use all-branch halting for backward truncation, as well as accepting-branch
padding. No arbitrary time function is evaluated at an inflated input size;
the verifier always receives its actual input `x++u`.

## Library and predecessor contracts used

- `Turing.FinTM.computesFunInTime_polyUnary`: supplies the concrete scheduler
  and the explicit degree-`c+1` budget in `b2_compile`.
- `contGuessTM`, `contGuessCfg`, `cont_guess_step`, `cont_guess_run`,
  `cont_guess_initial`, `cont_guess_coverage`: retained native guessing phase,
  capture representation, and exact physical-mask correspondence.
- `Turing.captureAction`: used by the retained guessing table invoked by the host.
- `Turing.FinTM.leftAction`, `leftCfg`, `leftCfg_apply`: embed that table in
  the disjoint scheduler/assembly bank while the verifier bank stays blank.
- `bufferTape_inputSymbol`, `virtualMove_correct`, `VirtualTag`,
  `bufferTape_append`: exact virtual-input clamping and tape capture.
- `capturedSummary`, `captureEmission`, `captureEmission_correct`,
  `capturedSummary_true`: complete-output capture and exact singleton verdict.
- Native `NDTM.runWith_append` and `runWith_of_halt`: timed phase composition
  and absorption; `FinTM.computesInTime_iff` and `ComputesInTime.output_unique`:
  completed-source contracts at their actual first halt.
- `NDTM.HaltsWithin.mono`, inherited `acceptsWithin_iff_of_halts` (which uses
  `FinNDTM.AcceptsWithin.mono`), `cont_guess_time_bound`, and
  `cont_guess_normalize`: common-bound transfer and final NTIME packaging.

There is no use of `exists_comp_partial` or untimed computability substitution.
The deterministic copier, rewinds, and verifier phases have explicit timed
configuration contracts throughout.

## Frozen surface and hygiene

`surface-check.json` and `verify_surface.py` verify against the required base:

- all eight public declaration headers and their order are unchanged;
- the entire inherited prefix, including all 68 predecessor private
  declarations and the forward compiler, is byte-identical;
- the five epoch-3 padding declarations, their docstrings, and the full
  remainder of the file are byte-identical;
- the original reverse-target docstring is retained with an append-only B2
  completion note; the equality docstring is unchanged;
- only the owned source path differs, and `git diff --check` passes.

Final size: **2,627 lines, 138,282 UTF-8 bytes**. SHA-256:
`d2f7358daaf0c0dd43779728bf1e1b536970b82cdd58b2c7645a5b8ccfcc8317`.
The file-size exception continues under exclusive ownership and the prohibition
on moving/removing predecessor helpers. Splitting/deduplication remains the
recorded E5 task. Style lint: **0 FAIL, 3 WARN** over the ten ClassNP files;
the warnings are the sizes of EXP, Nondeterminism, and TMSAT. The final owned
module has no compiler warnings other than its five untouched padding admissions.

Requested shared lemmas: **none**. Statement escalations: **none**.
Remaining frontier for this batch: **none**. No sanctioned `sorryAx` is consumed.

## Verification

- Lean **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`;
  mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**. Installed dependency
  revisions match the manifest; see `environment.log`.
- The required `lake exe cache get` ran once after the pinned toolchain was
  functioning. A prior startup attempt could not locate Lake's installation.
  Cache setup then encountered archive-owner metadata unsupported by this
  environment; it was resumed through the already-built cache executable with
  `TAR_OPTIONS=--no-same-owner`, and completed successfully. No `lake build`.
- The environment's PID namespace exposes `/proc/self/exe` but not the
  namespace-relative numeric `/proc/<pid>/exe` expected by this Lean release.
  The included `proc-self.c` compatibility shim redirects only that current-
  process executable lookup. The pinned release binaries and proof checker
  were not modified. The shim was used consistently for checking and caching.
- Owned-module and downstream checks: exit **0** (`downstream-final.log`).
- Final **57/57 fresh-module sweep**: exit **0**, **zero `error:` lines**,
  `FULL_SWEEP_COMPLETE`. The committed check script deletes each old olean and
  requires a fresh nonempty replacement. Final admission warnings: **21**, down
  from **23** at the required base. Exactly **five** remain in the owned file,
  all in the frozen epoch-3 padding cluster.
- Kernel type/value traversal, including opaque values: exit **0**.
  Both targets have empty admission roots and only the standard axiom triple.
  Every new private helper and its generated descendants — **92 checked
  declarations** in all — likewise has empty admission roots and at most that
  triple. See `AxiomChecks.lean`, `run-axioms.sh`, and `axiom-print.log`.
- Epoch-wide prints cover all **11 names enumerated in the campaign's E2
  batch table**, plus `timed_universal_quantitative`: all **12** closures are
  clean. This is a superset of the brief's request for “all ten” targets.
- Flat archive, SHA-256 manifest, format-patch replay, and git-bundle
  verification pass. Detached patch replay reproduces the full source exactly
  and passes the same surface verifier.

Headline prints:

```text
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
TARGET ROOTS Complexity.NP_subset_iUnion_NTIME: []
TARGET ROOTS Complexity.NP_eq_iUnion_NTIME: []
B2_COMPLETE_CLOSURE_AUDIT_PASS: all 12 target/bridge closures and 92 new-helper/generated-declaration closures have empty admission roots and at most the standard axiom triple.
```

Final sweep tail:

```text
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## New private declarations

All 42 are listed below: eight definitions and 34 lemmas. There are no new
private admissions. `surface-check.json` also records this inventory.

| Kind | Name |
|---|---|
| def | `b2UnaryTM` |
| def | `b2UnaryCfg` |
| lemma | `b2_unary_read` |
| lemma | `b2_unary_apply` |
| lemma | `b2_unary_step` |
| lemma | `b2_unary_run` |
| lemma | `b2_unary_initial` |
| lemma | `b2_unary_mask` |
| lemma | `b2_unary_computes` |
| lemma | `b2_unary_first` |
| def | `b2Slots` |
| def | `b2Host` |
| def | `b2GuessCfg` |
| lemma | `b2_tables_coincide` |
| lemma | `b2_guess_step` |
| lemma | `b2_guess_run` |
| def | `b2LoadCfg` |
| lemma | `b2_copy_step` |
| lemma | `b2_copy_run` |
| lemma | `b2_rewind_done` |
| lemma | `b2_rewind_step` |
| lemma | `b2_rewind_run` |
| lemma | `b2_initial` |
| lemma | `b2_copy_done` |
| lemma | `b2_start` |
| lemma | `b2_guess_word_injective` |
| lemma | `b2_guess_coverage` |
| def | `b2VerifyCfg` |
| def | `b2ReadyCfg` |
| lemma | `b2_verify_step` |
| lemma | `b2_verify_run` |
| lemma | `b2_verify_finish` |
| lemma | `b2_guess_return` |
| lemma | `b2_ready_step` |
| lemma | `b2_ready_done` |
| lemma | `b2_ready_run` |
| lemma | `b2_assembly` |
| lemma | `b2_verify_timed` |
| lemma | `b2_finish` |
| lemma | `b2_host_contract` |
| lemma | `b2_host_bound` |
| lemma | `b2_compile` |

## Archive and replay

`fill-ch2-e2cont-B2.zip` is flat: every entry is at its root, including
`SHA256SUMS`. `Nondeterminism.lean` is the full source and maps to
`TCSlib/Complexity/ClassNP/Nondeterminism.lean` in the repository. The archive
contains this report, one numbered format-patch, an incremental git bundle,
final sweep and axiom logs, the closure instrument, source-freeze verifier,
module order/check script, environment/cache records, and replay evidence.
`SHA256SUMS` covers every other archive member. No toolchain, dependency cache,
or olean is shipped.

Verify with `sha256sum -c SHA256SUMS`. Apply the numbered patch with `git am`
to the required base; this preserves Codex authorship. The bundle provides
the same commit and requires the base to be present. To reproduce checking,
use the committed 57-module order with `scripts/lean_check_tree.sh`, then
run `bash run-axioms.sh /absolute/path/to/tcslib` from this extracted archive.
The pinned `lean` must be on `PATH`. The compatibility shim is needed only
in environments with the documented PID-namespace mismatch.

Run `python3 verify_surface.py /absolute/path/to/tcslib` on the delivery
checkout to reproduce the surface checks. No changes to another repository
branch are needed.

## Notation

`x` is the original input, `u` its certificate, and `n=|x|` its length.
`C,c` are the prescribed certificate coefficient and degree;
`Q(n)=C(n+1)^c`. `S` is the unary scheduler; `B` is its time coefficient and
`τ(n)` its actual first halt. `V` is the verifier language, `M` its decider,
and `A,d` its time coefficient and degree. `H(n)` is the whole-host common
budget; `m=n+Q(n)+1`, `r=c+d+1`, `K=B+A+5`, and `e=r*max(1,c)` are the
normalization parameters. The argument name `V` in low-level helper lemmas
instead denotes the verifier machine, as its explicit `FinTM Bool` type shows.

## ===== audits/ch2-epoch2-agent-reports/batchC.md =====

# Chapter 2, epoch 2, batch C — continuation checkpoint

**Status: incomplete, 2 of 3 targets filled. Do not close batch C on this archive.**

`HALT_NPHard` and `HALT_not_mem_NP` are filled and kernel-checked. Their only
admitted dependency is exactly the brief-sanctioned `Complexity.NP_subset_EXP`.
The full 53-module sweep passes with zero errors. All 34 new private helpers
are admission-free.

`mem_NP_iff_exists_length_le` remains admitted at two explicit machine
obligations: polynomial-time membership of the forward paired verifier and
the reverse padded verifier. The witness equivalences, search uniqueness,
padding/stripping specifications, and required rejection behavior are proved.
These semantic results do **not** discharge the machine obligations. Its
`sorryAx` is an outstanding defect under the completion criterion, not a
sanctioned dependency. This archive uses the brief's continuation provision;
`CONTINUATION.md` identifies the exact remaining work.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Base branch: `complexity/arora-barak-ch1`
- Base commit: `6c09453e6af59ff1575060b66196d28812800d24`
- Working branch, created off that exact base as the brief requires: `fill/ch2-e2-C`
- Delivered commit: `3a7201b13789c5c2f051e69203257f03d3d494c1`
- Delivered tree: `3382c0564df63e9b94e20b88f0534967b1bee538`
- Binding brief: `briefs/ch2-epoch2-batchC.md` at the base commit.
- Lean: `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent, no delegation.

Only the two owned tracked files changed:

- `TCSlib/Complexity/ClassNP/NP.lean`
- `TCSlib/Complexity/ClassNP/Reductions.lean`

No other branch was checked out or changed. There was no push or PR. All
existing public declarations, statement signatures, hypotheses, docstrings,
AB09 attributions, imports, and option headers are preserved. There are no
removed declarations or new public declarations. All existing non-target
declarations and their proofs are untouched.

## Target disposition, in the assigned order

| Target | Status | Work and remaining obligation |
|---|---|---|
| `mem_NP_iff_exists_length_le` | **Open** | Follows the audited two-verifier construction. Both witness equivalences are proved. Two inline `sorry` terms remain, each proving a verifier language is in `P`; neither is hidden in a helper. |
| `HALT_NPHard` | Filled | Uses `NP_subset_EXP`, normalizes the total singleton-indicator decider with `one_work_tape_binary`, transforms its control, applies `exists_codeTM`, and uses fixed-code prefixing. Only `decode_encode` is used of the representation scheme. |
| `HALT_not_mem_NP` | Filled | Converts the assumed NP membership through `NP_subset_EXP` to a total decider, proves its singleton indicator equals `[HALT c s]` on every string, and contradicts `HALT_not_computable`. The `EffectiveMachineCode` hypothesis is unchanged. |

The first target was developed before moving to the HALT pair. It is not
being reported as false or as unprovable: the missing work is construction
and timed verification of its two machines. No mathematical obstruction to
the frozen statement was found.

### Exercise 2.1: audited edge cases

These are semantic discharges; the pending timed machines must implement
the same checks.

| Edge case | Where discharged |
|---|---|
| `C = 0` | `certificate_room` is quantified over all natural coefficients. The old witness bound forces the empty witness, and `paddedVerifier_witness` pads it with a marker using coefficient `C+1`. No positivity hypothesis on `C` is used. |
| `c = 0` | `certificateTotal_strictMono` derives strictness from the additive input length, not strict growth of the power. `certificate_room` uses only `(n+1)^c ≥ 1`. Both proofs include degree zero. |
| `x = []` | `paddedVerifier_append` proves the recovered split for every input, including length zero; `take`/`drop` at that boundary recover the entire certificate region. |
| `u = []` | `stripCertificate_pad` includes an empty old witness. The marker itself is retained in the padded region, and `paddedVerifier_witness` proves its exact length. |
| All-false region | `stripCertificate_false` and `paddedVerifier_no_marker` prove rejection, including when the input contains true bits. Stripping operates only on the suffix after the recovered boundary. |
| Malformed strings | `pairedVerifier_malformed` rejects failed grammar parsing; `paddedVerifier_no_split` rejects missing length solutions. `certificateSplit_zero` covers empty total input. `stripCertificate_spec` characterizes every successful strip as a last-true decomposition. |
| Marker after too many witness bits | `paddedVerifier_too_long` proves rejection even for a correctly marked word of the enlarged exact width. The original bound is explicitly present in `paddedVerifier`. |

### HALT control modification

The named control-modification lemma is **`acceptTM_halts_iff`**; its run
invariant is `acceptTM_run`, derived from `acceptCfg_step`.

The state space is `Option (M.State × Bool)`. A simulated source state carries
the remembered bit; the inner `none` is a live loop state, distinct from a
configuration's outer `none` halting state. `acceptAction` first updates the
register with the action's optional output, then redirects the successor
state. Consequently an emission on the halting transition is included.
`acceptTM_loop` proves the stationary live configuration stays fixed at every
time. The real output is suppressed, and the tape count is unchanged.

The separate emit-then-copy machine is `prefixTM`. Its proved budget is
`|w| + |x| + 1`; `fixedPair_computes` explicitly specializes this to
`2|α| + |x| + 3`. It does not substitute the diagonal-pairing machine.

## New declarations

All names below are private, in namespace `Complexity`; there are **34**.
The axiom log checks every one, including definitions and theorems.

### NP.lean: 18 private declarations

| Name | Statement or role |
|---|---|
| `stripCertificate` | Removes the last true marker and its false suffix, returning failure if no marker exists. |
| `stripCertificate_false` | All-false input strips to failure. |
| `stripCertificate_pad` | A word followed by a marker and false run strips back to that word. |
| `stripCertificate_spec` | Failure is equivalent to being all false; success is equivalent to a last-true decomposition. |
| `certificateTotal_strictMono` | Input length plus repaired exact width is strictly increasing. |
| `certificate_room` | The repaired exact width exceeds the original bound by at least one. |
| `certificateSplit` | Executable bounded search for a legal length split. |
| `certificateSplit_spec` | The search returns a given index exactly when that index solves the length equation. |
| `certificateSplit_zero` | Total length zero has no legal split. |
| `pairedVerifier` | Forward verifier language, using `pairDecode`, the exact length test, and the old verifier. |
| `pairedVerifier_pair` | Membership on genuine pairs has exactly the intended meaning. |
| `pairedVerifier_malformed` | Failed pair parsing implies rejection. |
| `paddedVerifier` | Reverse verifier language, with split search, marker stripping, original-bound check, and old paired verification. |
| `paddedVerifier_no_split` | Failed split search implies rejection. |
| `paddedVerifier_append` | A correctly sized certificate region is split at exactly the original input boundary. |
| `paddedVerifier_no_marker` | An all-false certificate region is rejected. |
| `paddedVerifier_too_long` | An overlong stripped witness is rejected, even inside a valid exact-width region. |
| `paddedVerifier_witness` | Exact padded witnesses and old bounded paired witnesses are equivalent. |

### Reductions.lean: 16 private declarations

| Name | Statement or role |
|---|---|
| `acceptState` | Maps a source state and captured bit to a simulated, halting, or live-loop state. |
| `acceptAction` | Copies the source tape actions, updates the bit before halt redirection, and suppresses output. |
| `acceptTM` | Finite control-transformed machine with unchanged tape count. |
| `acceptCfg` | Configuration correspondence using the source output's last bit. |
| `acceptTM_loop` | Every run from the live loop configuration remains at that configuration. |
| `acceptCfg_apply` | Action application commutes with the configuration correspondence. |
| `acceptCfg_step` | The correspondence commutes with every source step. |
| `acceptTM_run` | Initialized runs correspond at every time. |
| `acceptTM_halts_iff` | For a total singleton-bit source decider, transformed halting is equivalent to a true bit. |
| `prefixTM` | Zero-work-tape fixed-prefix emission followed by input copying. |
| `prefixCfg` | Configuration notation for the prefix machine. |
| `prefixTM_emit` | Fixed-prefix phase run invariant. |
| `prefixTM_copy` | Input-copy phase run invariant. |
| `prefixTM_computes` | Exact linear bound for fixed prefixing, including the final halting step. |
| `fixedPair_computes` | Audited `2|α| + |x| + 3` bound for fixed-code pairing. |
| `fixedPair_polyTime` | Polynomial-time computability of fixed-code pairing. |

## Requested shared lemmas

For serial promotion at a maintainer's discretion:

1. An existential public fixed-prefixing theorem from `prefixTM_computes`,
   in the composition layer, with the same `|w| + |x| + 1` bound.
2. Its fixed-code pairing specialization from `fixedPair_computes`, in the
   encoding layer. This is distinct from diagonal pairing.

The implementations remain private in the owned file. No shared file was
modified. The two verifier constructions remain this batch's continuation
obligations, not assumed shared results.

## Escalations and continuation

**Completion escalation:** Exercise 2.1 is unfinished. Its direct `sorryAx`
root violates the brief's clean-target requirement, so the gate remains open.
There is no proposed statement alteration. Continue from the delivered
commit using `CONTINUATION.md`, replacing both verifier-membership admissions
with actual timed machine proofs. Preserve all frozen statements and the
audited route.

## Verification evidence

The dependency setup invoked `lake exe cache get`. The whole-Mathlib fetch
encountered repeated HTTP 502 responses and was stopped after the required
dependencies were available. Same-pin local caches supplied missing campaign
modules. The initial bootstrap's missing Mathlib module was repaired, then
the complete 53-module bootstrap retry passed. No dependency revision,
toolchain, or tracked build configuration was changed. No `lake build` was run.

Early scratch development used the same-pin previous-epoch olean tree;
subsequent owned-module checks and the final complete sweep used this
checkout's freshly emitted olean tree. The final gate invokes the committed
`scripts/lean_check_tree.sh` and requires each Lean process to exit zero,
emit no `error:` lines, and produce a fresh olean. It stops at any failure.

- Final sweep: **53/53 pass; zero `error:` lines**.
- Final admitted-declaration warnings: **30**: the one unfinished owned NP
  target, plus 29 out-of-scope declarations.
- `Reductions.lean`: no directly admitted declarations.
- New private helpers: **34/34 admission-free**.
- Owned-file style lint: **0 FAIL, 0 WARN**.
- Statement freeze: **13 existing public declarations unchanged**, both
  ordered signatures and multisets checked; no removals or public additions.
- `git diff --check`: passes.
- Patch replay on a separate index: reproduces the delivered tree exactly.
- Incremental bundle: verifies against the recorded base.

Final sweep tail:

```text
CHECK 51/53 TCSlib/Complexity/Formulas
RESULT 51/53 exit=0 seconds=1.318
CHECK 52/53 TCSlib/Complexity/CookLevin
RESULT 52/53 exit=0 seconds=1.567
CHECK 53/53 TCSlib/Complexity/ClassNP
RESULT 53/53 exit=0 seconds=1.478
PASS: 53/53 modules; seconds=184.992
UTC end: 2026-10-02T22:01:39.191581+00:00
```

### Axiom prints and verified roots

All three headlines currently print
`[propext, sorryAx, Classical.choice, Quot.sound]`. The set alone does not
distinguish a permitted dependency from an unfinished proof; kernel-environment
traversal does:

| Target | Declarations directly using `sorryAx` in its transitive dependency closure | Disposition |
|---|---|---|
| `mem_NP_iff_exists_length_le` | Only `Complexity.mem_NP_iff_exists_length_le` itself | **Unfinished, unsanctioned; continuation required.** |
| `HALT_NPHard` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |
| `HALT_not_mem_NP` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |

The traversal inspects checked kernel declarations, both types and values,
including opaque values. It checks every new helper has no direct admission
root and only a subset of `[propext, Classical.choice, Quot.sound]`. The
script deliberately reports the unfinished NP target as such; successful
execution of the diagnostic is **not** a claim that all targets meet the gate.

After recreating the fresh tree, run `verification/run_axioms.sh` with the
checkout path. The full raw results are in `logs/axioms.log`; the verifier
program is included. `verification/sweep.py` and `verification/check_freeze.py`
take the checkout path as their argument. Put the pinned Lean on `PATH`.

## Archive contents and integration

The archive includes this report, continuation instructions, the two full
modified sources, one `git format-patch` patch, an incremental git bundle,
the final sweep and axiom logs, supporting verification scripts/logs, the
committed module order, and `SHA256SUMS`. Every payload file except
`SHA256SUMS` itself is covered.

Verify with `sha256sum -c SHA256SUMS` in the unpacked root. The bundle requires
base `6c09453e6af59ff1575060b66196d28812800d24` and advertises only
`refs/heads/fill/ch2-e2-C`. The patch is suitable for the workflow's `git am -3`
integration, but **must not be mistaken for a completed batch**.

## Brief checklist

- [ ] Three targets filled — **only two are filled**.
- [x] Exercise 2.1 edge-case semantic discharges itemized.
- [x] HALT control-modification lemma named and proved.
- [x] Base hash and all new declarations listed.
- [x] Shared-lemma requests and completion escalation recorded.
- [x] Final full sweep and axiom logs supplied; sanctioned roots checked.
- [ ] Exercise 2.1 has no `sorryAx` — **still open**.
- [x] Diff restricted to owned files and named targets plus private helpers.
- [x] Full sources, patch, bundle, verification material, and checksums supplied.

## ===== audits/ch2-epoch2-agent-reports/batchC-cont.md =====

# Chapter 2 E2 continuation C — completed

Both inline machine obligations in `mem_NP_iff_exists_length_le` are filled.
The existing witness-equivalence proof and all semantic helpers are preserved.
Only `TCSlib/Complexity/ClassNP/NP.lean` changes. No remote push or PR was made.

## Provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch1`.
- Required and actual code base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- Working branch: `fill/ch2-e2cont-C`.
- Delivered commit: 7d343bfd9124cf44991e893a1e4108a2f22c15d4.
- Delivered tree: 5f284c073402c1f82b0304bf5410154c683066d9.
- Binding continuation brief read at branch tip
  `cc103db9d9f00e28924a685919629be9b3ec1b63`. That commit adds the briefs and
  planning updates; the code baseline is its parent, as the brief requires.
  The new local working branch was moved to that required base before edits.
  No other branch was changed.
- Lean `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Single agent; no delegation.
- Final owned file: 679 lines, 32,936 bytes.

The original E2-C brief, predecessor report and continuation, policy/workflow,
infrastructure audit D5 and design §9c were read. The continuation brief controls
the narrower ownership, exact base, 57-module order, and absence of sanctioned
admissions for this target.

## Completed constructions

### Forward paired verifier

`pairedVerifier_mem_P` implements the aligned grammar guard, both length
inequalities, concatenation, and the old verifier. The upper bound is P8 at
`(C,c)`. For the reverse inequality, `verifier_poly_reverseBound` uses P5 to
generate `C(|x|+1)^c` trues, P3 to prepend one bit, and the audited general
pairing recipe to pair `u` with that word. P8 at `(1,1)` tests

```
C(|x|+1)^c + 1 ≤ |u| + 1  iff  C(|x|+1)^c ≤ |u|.
```

Conjoining the orientations yields exact width even when the coefficient or
degree is zero. The outer P6 grammar guard rejects malformed strings before
the old verifier runs.

`verifier_poly_pair` is the canonical §9c recipe:

```
H x = pairEncode (f x) []
s x = pairEncode x (H x)
t x = pairEncode (s x) (g x)
pairSnd (pairConcat (t x)) = pairEncode (f x) (g x).
```

The second threaded map uses `g ∘ pairFst` on the duplicated whole `s x`.
No payload-only map is treated as a cross-component operation.

### Reverse padded verifier

`paddedVerifier_mem_P` uses P10 at **`(C+1,c)`**, guards its empty failure
output, applies P9 to the valid threaded pair, guards marker failure, and
checks P8 at **`(C,c)`**. Only then does it run the supplied old paired
verifier on `pairEncode (y.take n) u`. The original prefix remains the head
throughout; the equation supplies `n ≤ |y|`, so that prefix has length `n`.
The last stage is the supplied language `V`'s decider on the pair, exactly as
the frozen `paddedVerifier` specifies; it does not apply the forward
exact-width predicate to this bounded witness.

The two new vocabulary bridges have these exact statements:

```lean
private lemma verifier_split_bridge (C c : ℕ) :
    solveSplit (C + 1) c = certificateSplit C c

private lemma verifier_strip_bridge :
    splitAtLastTrue = stripCertificate
```

The split bridge is definitional at the shifted coefficient. The strip bridge
uses the predecessor's complete last-true/all-false semantic specification.

### Runtime and capture discipline

All machines are obtained from the proved timed contracts, never from an
untimed computability theorem. `verifier_poly_cond` instantiates W3 and
dominates its three polynomials by their maximum degree. `verifier_poly_map`
uses C1 with an explicitly monotone polynomial and degree `c+1` to absorb the
input scan. Compositions use the proved `PolyTimeComputable.comp`.

`verifier_poly_indicator` deliberately runs the supplied old decider as W3's
test, with constant true/false branches. W3's finite controller is the capture
host; its proof consumes `capture_run`, including halting-transition output.
Thus the verifier run is captured and its singleton verdict is emitted by the
host. No new raw controller or duplicated capture invariant is needed.

## Library contracts consumed, by use

All `computesFunInTime_*` names below are in `Turing.FinTM`.

| Contract | Use |
|---|---|
| `computesFunInTime_const` | Empty payload in the pairing recipe, false rejection, and terminal Boolean outputs. |
| `computesFunInTime_cond` | Grammar, both width, marker, and original-bound gates; capture of the supplied old verifier. |
| `computesFunInTime_pairMapSnd` | Payload transformations in the exact `H/s/t` pairing assembly. |
| `computesFunInTime_pairDup` | Retain the whole request through that assembly. |
| `computesFunInTime_pairFst` | Extract the original input for polynomial generation; recover it inside the retained-request map. |
| `computesFunInTime_pairSnd` | Extract the old witness; final general-pairing extraction. |
| `computesFunInTime_pairConcat` | Complete general pairing and feed `x ++ u` to the forward verifier. |
| `computesFunInTime_pairValid` | Reject malformed original pairs, missing splits, and failed marker strips. |
| `computesFunInTime_polyUnary` | Exact unary original bound. |
| `computesFunInTime_prepend` | Add the one bit required by the reverse-comparison translation. |
| `computesFunInTime_pairLenCheck` | `(C,c)` original bound; `(1,1)` reverse exact-width orientation. |
| `computesFunInTime_splitSolve` | `(C+1,c)` split search. |
| `computesFunInTime_stripLast` | Strip the last marker only in a valid pair's payload. |
| `computesFunInTime_comp` | Consumed through `PolyTimeComputable.comp` for all sequential stages. |
| `Turing.capture_run` | Consumed by the proved W3 host instantiated in `verifier_poly_indicator` and the other guards. |

`mem_P_iff` supplies and repackages actual finite singleton-indicator deciders.
The existing pairing parser API is reused; no alternate encoding is introduced.

## Seven audited edge cases: machine-side discharge

| Edge case | Discharge point |
|---|---|
| `C = 0` | All catalog instantiations and both membership lemmas quantify over arbitrary natural coefficients. The reverse orientation is still exact, and the padded split uses `C+1`. The original-bound check accepts only the empty stripped witness. |
| `c = 0` | Unary generation and both P8 checks include zero degree; `verifier_poly_map` absorbs the scan with degree `c+1`. The shifted split bridge retains the predecessor's strict-monotonicity semantics at degree zero. |
| `x = []` | Extractors and P10 handle an empty pair head. The successful split branch proves `n ≤ |y|` and uses the exact `take` length, also at `n=0`. |
| `u = []` | General pairing and P9 retain a valid encoding even with an empty payload. Grammar guards distinguish this from the empty failure word. The reverse comparison's added bit also includes zero witness length. |
| All-false certificate region | P9 receives `pairEncode x v`, never bare `v`; `verifier_strip_bridge` turns the existing failure fact into `[]`, which the post-strip grammar guard rejects before consulting `V`. |
| Malformed strings / no split | The forward outer grammar guard rejects malformed encodings. In the reverse direction P10 failure produces `[]`; the pre-strip grammar guard rejects it. The `none` case of `paddedVerifier_mem_P` proves this for every failed search, including the empty input. |
| Marker after too many witness bits | After successful stripping, P8 at the original `(C,c)` checks the retained original prefix. The `¬hu` branch of `paddedVerifier_mem_P` proves rejection without consulting `V`, even when the witness fits the enlarged certificate region. |

These machine correctness proofs hold on every input, and the existing seven
semantic discharge families remain byte-identical.

## New private declarations

There are **20**, all in `Complexity`; no public declaration is added.

| Name | Role |
|---|---|
| `verifier_poly_linear` | Lift a linear timed contract into the polynomial normal form. |
| `verifier_poly_const` | Fixed output words. |
| `verifier_poly_cond` | Timed conditional closure and polynomial bound. |
| `verifier_fst` | Total first projection. |
| `verifier_snd` | Total second projection. |
| `verifier_concat` | Guarded pair concatenation. |
| `verifier_map` | Guarded payload map. |
| `verifier_poly_map` | Timed payload-map closure. |
| `verifier_poly_pair` | Audited general pairing assembly. |
| `verifier_split_bridge` | Shifted search vocabulary equality. |
| `verifier_strip_bridge` | Last-marker vocabulary equality. |
| `verifier_bound` | Original-bound Boolean test. |
| `verifier_poly_bound` | Its P8 timed realization. |
| `verifier_poly_indicator` | Captured old-verifier execution. |
| `verifier_mem_P` | Repackage the timed singleton indicator into `P`. |
| `verifier_poly_reverseBound` | Reverse exact-width comparison. |
| `pairedVerifier_mem_P` | First completed machine obligation. |
| `verifier_split` | Shifted threaded split function. |
| `verifier_strip` | Threaded marker-strip function. |
| `paddedVerifier_mem_P` | Second completed machine obligation. |

Requested shared lemmas / escalations: **none**. The existing owned file stays
below the policy's 1,000-line split threshold. Its 679 lines reflect preserving
the frozen semantic layer and keeping all new helpers private in the sole owned
file; a separate shared-API change is not needed for this batch.

## Verification

- Final fresh sweep: **57/57 modules pass; zero `error:` lines**. Each module
  passes the committed script's exit-status, error-diagnostic, and freshly
  produced-olean gates. The run uses a new isolated `.lake/e2cont-C-final`
  tree, not the development tree.
- The owned module plus all 16 later modules also passed sequentially before
  the final sweep. No owned-module diagnostics remain.
- Final sweep admission warnings: **27**, all in untouched out-of-scope
  declarations, versus 28 at the base. `NP.lean` has none.
- `mem_NP_iff_exists_length_le` prints exactly
  `[propext, Classical.choice, Quot.sound]`.
- Checked-kernel traversal of that target finds **no direct admission roots**.
  The traversal reads declaration types and values, including opaque values.
- A separate whole-module traversal covers **84 kernel declarations** originating
  in `NP.lean`, including generated declarations. Its transitive closure has no
  admission roots; every axiom set is contained in the standard triple. The
  program also checks all **20 new helpers** exist exactly once and are private,
  printing each helper's axioms.
- Statement freeze: **21 existing declarations** retain their ordered signatures
  and signature multiset; **3 public declarations** are unchanged with no public
  additions/removals. The stronger byte comparison reconstructs the exact base
  source by removing the new import and helper block and reverting only the two
  authorized proof-hole replacements. This also verifies all old docstrings,
  semantic proofs, and the surrounding equivalence proof are preserved.
- Style lint over ClassNP: **0 FAIL, 1 WARN**. The only warning is the unchanged
  1,206-line `TMSAT.lean`; the owned file has no warning (679 lines is an INFO
  against the 600-line target). No out-of-scope file was edited.
- `git diff --check` passes; exactly one tracked file changes; the working tree
  is clean after the local commit. The incremental bundle verifies against the
  required base. Patch replay on a separate index reproduces the delivered tree
  exactly, without checking out or modifying another branch.

Environment setup reused a same-pin local dependency cache and completed
`lake exe cache get` successfully (`cache-get.log`). An initial launch needed
this environment's existing Lean runtime-path compatibility shim; it failed
before the cache operation. The successful cache operation ran once, with no
files needing download. No `lake build` was run and no pinned configuration
was changed. An early bootstrap overlapped owned-module development and stopped
at a temporarily missing owned-module olean; the subsequent sequential downstream
pass and the final isolated fresh sweep above supersede that attempt.

The diagnostic is an acceptance check: any target or whole-module admission
root, or any axiom outside the standard triple, fails it. It does not whitelist
`sorryAx`. The remaining `enumMachine_contracts` root in untouched Chapter 2
files is outside this batch and is not consumed by this target.

### Final sweep tail

```
CHECK 55/57 TCSlib/Complexity/Formulas
RESULT 55/57 exit=0 seconds=1.096
CHECK 56/57 TCSlib/Complexity/CookLevin
RESULT 56/57 exit=0 seconds=1.221
CHECK 57/57 TCSlib/Complexity/ClassNP
RESULT 57/57 exit=0 seconds=1.351
SWEEP_PASS modules=57 seconds=175.791
UTC_END 2026-10-04T15:30:36.893986+00:00
```

## Flat archive and integration

The ZIP is flat: `SHA256SUMS`, this report, `NP.lean`, the format-patch series,
the incremental git bundle, final sweep and axiom logs, and supporting evidence
and reproduction programs are all root entries. Every payload other than
`SHA256SUMS` itself is hashed. `NP.lean` maps to
`TCSlib/Complexity/ClassNP/NP.lean` in the repository.

Verify with `sha256sum -c SHA256SUMS`. Apply the patch with `git am -3` on the
integration branch, or import the bundle, which requires the recorded base and
advertises only `refs/heads/fill/ch2-e2cont-C`. The source delta is exactly one
precise import, the new private helper block, and replacements of the two
authorized `sorry` terms; no existing statement, docstring, helper body, or
surrounding public proof structure changes.

For reproduction, put the pinned Lean on `PATH`, populate its pinned dependencies,
then run `TCSLIB_OLEANS="$PWD/.lake/e2cont-C-final" python3 /path/to/sweep.py "$PWD"`
and `bash /path/to/run-axioms.sh "$PWD"`. `check-freeze.py` takes the repository
path and compares against the exact recorded base.

## ===== audits/ch2-epoch2-agent-reports/batchC-continuation.md =====

# Continue epoch 2 batch C: timed verifiers for Exercise 2.1

Read `briefs/ch2-epoch2-batchC.md` on the exact campaign branch first. Its
repository rules, frozen statements, proof routes, and verification protocol
remain binding. This continuation does not authorize a different route.

Base of the original batch: `6c09453e6af59ff1575060b66196d28812800d24`.
This checkpoint: `3a7201b13789c5c2f051e69203257f03d3d494c1`.
Import its patch or bundle without replacing newer unrelated work. No remote
branch was pushed. Both HALT targets are already proved; preserve them.

## Exact remaining proof goals

In `TCSlib/Complexity/ClassNP/NP.lean`, the two inline admissions inside
`mem_NP_iff_exists_length_le` have these contexts and goals:

```lean
C c : ℕ
V : Language Bool
hV : V ∈ P
⊢ pairedVerifier C c V ∈ P
```

```lean
C c : ℕ
V : Language Bool
hV : V ∈ P
⊢ paddedVerifier C c V ∈ P
```

The semantic parts of the public proof are finished and compile. No new
helper contains an admission. Do not replace either missing machine proof
with a computability claim, an informal polynomial-time assertion, or an
out-of-scope admitted theorem. This target must have no `sorryAx` at completion.

## Forward machine

Implement the exact `pairedVerifier` predicate:

1. Scan the aligned `pairDecode` grammar; reject malformed words.
2. Recover both components, count their lengths, and test equality to the
   explicit formula `C * (n+1)^c`, with the original `C,c`.
3. Assemble the concatenation and run the old polynomial-time decider.
4. Prove the actual finite machine's completed output is the singleton
   indicator and its runtime is polynomial in the entire input length.

`pairedVerifier_pair` supplies correctness on genuine pairs;
`pairedVerifier_malformed` covers failed grammar parsing. The pinned API
includes `pairDecode_pairEncode` and `pairEncode_injective`; reuse them.

## Reverse machine

Implement the exact `paddedVerifier` predicate:

1. Given total input length, search indices up to that length for
   `n + (C+1)*(n+1)^c = totalLength`. Reject if there is no solution.
2. Split at the recovered index. Restrict marker search to this suffix.
3. Strip at its last true bit; reject if the suffix is all false.
4. Recheck the **original** bound on the stripped witness length.
5. Assemble `pairEncode x u` and run the old polynomial-time decider.
6. Prove the singleton-indicator output and a polynomial time bound for
   the finite machine on **all** strings, including failed searches.

Useful completed lemmas:

- `certificateTotal_strictMono`: uniqueness, including degree zero.
- `certificate_room`: the repaired exact width has space for the marker.
- `certificateSplit_spec`, `certificateSplit_zero`: exact search semantics.
- `stripCertificate_spec`, `stripCertificate_pad`, `stripCertificate_false`.
- `paddedVerifier_append`: the search recovers the original input boundary.
- `paddedVerifier_witness`: the required existential witness equivalence.
- `paddedVerifier_no_split`, `paddedVerifier_no_marker`,
  `paddedVerifier_too_long`: all audited rejection obligations.

The missing infrastructure is **timed machine construction** for fixed-degree
length arithmetic, bounded search, scans/copies, and verifier execution.
The present list-level functions do not constitute that construction.
`PolyTimeComputable.comp` and `FinTM.computesFunInTime_comp` are proved and
usable for timed composition. Do not substitute `exists_comp_partial` or
untimed `exists_cond` where a polynomial runtime is required. The private
counter in `ClassP/TimeConstructible.lean` is a reference implementation,
not a public polynomial-evaluation theorem.

## Verification and acceptance

Use the pinned Lean and cache. Never run `lake build`. Run the owned module
check and all later modules after edits; finish with the full committed
53-module order and the final axiom audit. The checkpoint has 30 admitted
declarations; closing this target alone reduces that to 29, assuming no
concurrent changes.

Update the diagnostic in `verification/Axioms.lean`: require an empty direct
admission-root list for `mem_NP_iff_exists_length_le`. Currently it explicitly
expects and reports that target's own admission, solely to document this
checkpoint. Keep the two HALT roots restricted to `NP_subset_EXP` until the
concurrent batch-A proof is integrated; after integration those must also
become empty.

Rerun statement-freeze checks against the original base, enumerate all new
private declarations, refresh the report and checksums, and deliver the
required ZIP. Do not close the batch until all three headline proofs meet
the brief's axiom requirements.

## ===== audits/ch2-epoch2-agent-reports/batchD.md =====

# Chapter 2, epoch 2, batch D — PARTIAL continuation delivery

**This is the partial-delivery case of ground rule 7, not a completed batch and not a closed audit gate.** `timeConstructible_poly` is fully proved. The other target bodies have checked assemblies, but membership and hardness retain three explicitly marked concrete-machine obligations. The mandated quantitative bridge is separately admitted under bridge-protocol step 3. There are **four explicit `sorry` sites in three declarations**. No private helper is admitted.

## Repository, base, and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `6c09453e6af59ff1575060b66196d28812800d24`.
- Working branch: `fill/ch2-e2-D`, created directly from that base as the committed brief instructs.
- Delivered commit: `7c91b03a3519d73159b6316f43e78d3812d77460`.
- Only changed repository path: `TCSlib/Complexity/ClassNP/TMSAT.lean`.
- No PR, push, checkout of `main`, or modification of another existing branch. Single agent; no delegation.
- The archive contains the complete modified source, one format-patch, and an incremental git bundle advertising `refs/heads/fill/ch2-e2-D`. The bundle requires the recorded base commit, which is its sole prerequisite.
- Existing declaration order and all five existing signatures are unchanged. The `TMSAT` definition is unchanged, even after comment stripping. No declaration was removed. The only deliberate new public declaration is `Complexity.timed_universal_quantitative`.

## Target status

| Target | Status | Exact frontier |
|---|---|---|
| `timeConstructible_poly` | **Proved, no `sorryAx`** | Concrete finite machine, exact output, and runtime bound checked. |
| `timed_universal_quantitative` | **Stated; bridge escalation** | One simulator before all codes and inputs; both success and timeout clauses; missing public concrete-simulator API described below. |
| `TMSAT_mem_NP` | **Partial** | Certificate equivalence, total timed answers, uniform polynomial budget, and buffered composition proved; `D-MEM` remains. |
| `TMSAT_NPHard` | **Partial** | Exact certificate-value cases, normalization, prescribed deadline, pairing pinning, and reduction correctness proved; `D-WRAP` and `D-EMIT` remain. |
| `TMSAT_NPComplete` | **Assembly filled, dependent on admissions** | The conjunction uses the two preceding targets. It is not an admission-free NP-completeness proof. |

Fill order was polynomial construction, bridge, membership, hardness, completeness. Out-of-scope admissions and source files were left untouched.

## Exact outstanding admissions

| Site | Current line | Remaining proof obligation |
|---|---:|---|
| `timed_universal_quantitative` | 636 | Bridge protocol step 3: expose the concrete bounded-answer theorem from Chapter 1, then use the proved coefficient estimate. |
| `TMSAT_mem_NP`, local `hV` / `D-MEM` | 943 | Build the odd-split/quadruple parser, unary-to-binary clock conversion, and well-formed timed-request preprocessor; assemble the verifier and its runtime. |
| `TMSAT_NPHard`, local `hwrap` / `D-WRAP` | 1131 | Build a total pair-to-concatenation wrapper, reject malformed pairs, and run the supplied verifier with a polynomial bound. |
| `TMSAT_NPHard`, local `hemit` / `D-EMIT` | 1169 | Retain the input while emitting the fixed code, doubled input, and the two exact unary runs; prove the nested pairing layout and polynomial runtime. |

The last three admissions are permitted **only because this is a partial delivery**. They are not covered by the bridge exception and must be removed before claiming a completed batch. The source marks them with `CONTINUATION D-MEM`, `D-WRAP`, and `D-EMIT` comments.

## Closed construction and proof-route deviation

The original polynomial time-constructibility sketch proposed binary schoolbook multiplication. This delivery instead constructs the exact unary value and composes it with the already-proved public binary length counter. The original sketch remains; an appended implementation note explicitly records this deviation. No statement or hypothesis changed.

The machine uses `c+1` unary loop tapes, each of side length `n+1`, and emits exactly `C` true bits per box point. Its full output is `List.replicate (C*(n+1)^(c+1)) true`. A recursive invariant preserves all outer heads and resets completed inner heads. A loop of depth `r` costs at most `(C+1+5*r)*(n+1)^r`; startup and the final halt give total budget `(C+5*(c+1)+4)*(n+1)^(c+1)`. Timed composition with `timeConstructible_id` emits the exact `Nat.bits` value within the required constant multiple of that value plus one. The theorem's domination condition uses `C>0`. The generator itself also handles `C=0`; the theorem does not assert time constructibility for that case.

This construction includes empty input and side length one. It does not cite private counter declarations from `TimeConstructible.lean`, use an assumed arithmetic machine, or introduce an axiom. The exact certificate-bit lemma separately follows the mandated three-way case split: zero coefficient, positive coefficient with degree zero, and positive coefficient with positive degree.

The file is 1185 lines. Its size warning is accepted for this delivery because the brief permits modification of only this file, and the first target needs the concrete machine and run invariants. Any shared-file extraction should occur serially at merge, not by changing frozen Chapter-1 sources in this batch.

## Bridge escalation: precise missing API

The **stated simulator bound** is

```text
(3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1)^2.
```

`U` is quantified before `α`, the simulated input, and the deadline. The bound is a fixed closed expression in the code length and canonizer time, not a newly chosen coefficient per input. Both original `timed_universal` implications are present, including timeout rejection at deadline zero.

The public-API portion of the coefficient calculation **is proved**: `tmsat_serialization_length`, `tmsat_serialization_parameters`, and `tmsat_concrete_coefficient` show that the explicit startup-plus-block coefficient used in Chapter 1 is at most `3*|α| + 14*H + 50`, where `H = c.canonizerTime |α|`. This is not a proof that an arbitrary existential witness of `timed_universal` has that bound.

The missing fact is the concrete, uniformly selected simulator's bounded-answer theorem:

- `Universal.lean`'s `timedUniversalTM` is private.
- Its `timedStartupBound` is private.
- Its `timed_computes` theorem is private. It states that this concrete machine produces the exact `timedAnswer` within `(timedStartupBound c α + universalBlockBound c α + 14)*(t+1)^2`.
- `timedAnswer` is also private and can be exposed in an export statement by spelling out the source configuration at time `t`: `true :: output` if halted, `[false]` otherwise.

**Requested shared addition:** a public Chapter-1 theorem exposing this concrete bounded-answer guarantee with one simulator chosen before code and input, with the private startup expression expanded (or an equally strong explicit success-and-timeout theorem). The maintainer can then discharge this file's bridge by monotonicity and `tmsat_concrete_coefficient`. No Chapter-2 predicate, including `PolyBound`, belongs in that Chapter-1 addition. No private declaration from another source file is used as a proof dependency in this contribution.

This is the required bridge-protocol step-3 escalation. The bridge remains a genuine admission; neither the arithmetic lemma nor its two-clause statement is presented as a completed simulator construction.

## Obligation-to-lemma map

| Audited obligation | Discharging lemma or exact open frontier |
|---|---|
| Concrete polynomial-value computation | `polyUnaryTM`, `poly_loop`, `poly_start`, `poly_unary_computes`, and `timeConstructible_poly`; closed, with the documented route deviation. |
| Uniform concrete coefficient arithmetic | `tmsat_serialization_length`, `tmsat_serialization_parameters`, `tmsat_concrete_coefficient`; closed. Concrete simulator API remains at the bridge. |
| Both success and timeout clauses | `tmsat_simulator_total`; closed as a theorem with the bridge-shaped hypothesis. |
| Reject timeout or any non-`[true]` completed output | `tmsatAnswer_accept`; exact whole-answer semantics closed; machine integration remains in `D-MEM`. |
| Explicit `hc : PolyBound c.canonizerTime` budget chain | `tmsat_simulation_budget`, giving coefficient `3+14*C+50`, degree `max 1 e+2`; no monotonicity assumption on canonizer time. |
| Certificate length bounded by input length | `tmsat_quad_bounds`; closed. |
| Odd split and unique split position | `tmsat_split_length` and the `List.append_inj` step of `tmsat_certificate_equiv`; semantics closed; parser machine remains in `D-MEM`. |
| Quadruple parser and all-true unary checks | `D-MEM`, open. The existential verifier specification alone does not prove computability. |
| Exact certificate padding and prefix extraction | `tmsat_certificate_equiv`; closed. |
| Unary-to-binary clock conversion | `D-MEM`, open assembly obligation; public `timeConstructible_id` is available. |
| Relocation and capture | `tmsat_comp_on_image`; closed with budget `2*T₁(n)+T₂(n)+2`, assuming the second machine terminates only on the first machine's image. Concrete preprocessor integrations remain open. |
| Total wrapper including malformed pairs | `tmsatWrapperOutput` specifies the total function; `D-WRAP` must construct its machine. |
| One-work-tape normalization and fixed lawful code | The `one_work_tape_binary`, `exists_codeTM`, and `decode_encode` steps in `TMSAT_NPHard`, conditional on `D-WRAP`. |
| Exact certificate value, all three cases | `tmsat_exact_certificate_bits`, using `tmsat_constant_poly` and `timeConstructible_poly C₀ (c₀-1)`; closed. |
| Prescribed deadline majorization | `tmsat_deadline_bound`; closed with exactly `r=max 1 c₀`, `D=(K+1)(B+1)^2(C₀+3)^(2e)`, `T'(n)=D(n+1)^(2er)`. |
| Exact binary deadline | Local `hdeadline` in `TMSAT_NPHard`, via `timeConstructible_poly D (2er-1)` and proved positivity. |
| Fixed-code emission, doubled input, binary countdowns, nested tuple assembly | `D-EMIT`, open. Available exact bit-computation theorems do not substitute for these machines. |
| Pairing injectivity pins all components | `tmsat_quad_injective`; three explicit uses of `pairEncode_injective`, then unary lengths. |
| Reduction correctness and completed-output uniqueness | `tmsat_reduction_correct`; closed under the wrapper semantics hypothesis, instantiated in `TMSAT_NPHard`. |
| Completeness conjunction | `TMSAT_NPComplete`; body filled, dependent on the remaining admissions. |

## Every new explicit declaration

Public addition: `Complexity.timed_universal_quantitative`, the mandated bridge, at line 625.

All 41 declarations below are **private**. Each helper theorem is closed; the type, instances, and definitions contain no admissions. The full delivered module's compiler-generated declaration inventory is included in `logs/kernel-declarations.log`; source-level inventory and signature checks are in `logs/statement-freeze.json`.

| Private declaration (inside `Complexity`) | Line | Meaning |
|---|---:|---|
| `PolyControl` | 117 | Six families of finite controller states for copy/setup, nested loops, rewinds, advances, and fixed emission. |
| `polyControlFintype` | 125 | Private finite enumeration of the control type via its sum representation. |
| `polyControlDecidableEq` | 129 | Private decidable equality for the control type. |
| `polyTape` | 133 | A unary interval of true bits, blank outside the interval. |
| `polyMove` | 137 | A no-output action moving exactly one selected work head. |
| `polyUnaryTM` | 144 | Concrete finite binary machine enumerating a fixed-dimensional box and emitting the exact unary polynomial. |
| `polyCfg` | 174 | Canonical loop configurations with arbitrary outer heads and accumulated output. |
| `polyMove_apply` | 180 | A head-only action has exactly the stated single-head update. |
| `poly_emit` | 194 | The finite chain emits exactly its remaining number of true bits. |
| `poly_rewind` | 216 | Rewind restores the selected loop head to zero without changing other heads or output. |
| `poly_advance` | 249 | Returning to an outer loop increments exactly that loop head. |
| `polyCost` | 259 | Exact recursive cost of a full loop nest. |
| `poly_loop` | 271 | Full recursive loop invariant: exact output, exact cost, restored inner heads. |
| `polyTape_write` | 376 | Writing the first blank extends the unary tape by one cell. |
| `polyCost_le` | 389 | The loop cost is at most (C+1+5r) times the number of box points. |
| `polyCopyCfg` | 408 | Canonical configurations during the parallel unary-length copy. |
| `poly_copy` | 413 | An input scan copies the exact length to every loop tape. |
| `poly_setup` | 448 | Parallel startup rewind reaches the outermost loop at head zero. |
| `poly_start` | 472 | Startup installs side length |x|+1 in 2(|x|+1) steps. |
| `poly_unary_computes` | 506 | The exact unary polynomial is computed within (C+5(c+1)+4)(n+1)^(c+1). |
| `tmsat_serialization_length` | 639 | Canonizer output length is at most its time budget. |
| `tmsat_flatMap_length` | 645 | Flattening nonempty words does not shorten a list. |
| `tmsat_action_nonempty` | 655 | Every serialized transition record is nonempty. |
| `tmsat_serialization_parameters` | 670 | The serialization bounds the header bit length, initial index, and state count. |
| `tmsat_concrete_coefficient` | 703 | The concrete Chapter-1 coefficient expression is at most 3|α|+14H+50. |
| `tmsatAnswer` | 713 | The source deadline configuration determines a tagged full output or timeout. |
| `tmsat_simulator_total` | 723 | Both bridge clauses give total completed answers on well-formed requests. |
| `tmsatAnswer_accept` | 746 | Equality with the entire answer [true,true] is equivalent to source acceptance. |
| `tmsat_simulation_budget` | 760 | PolyBound on canonizer time gives a uniform polynomial simulation budget. |
| `tmsatQuad` | 788 | The exact right-nested quadruple encoding. |
| `tmsat_quad_bounds` | 792 | Each code/input/unary length fits in the quadruple length. |
| `tmsatVerifier` | 800 | Existential verifier specification with exact odd split and prefix extraction. |
| `tmsat_split_length` | 806 | The exact certificate convention forces odd total length and the unique split index. |
| `tmsat_certificate_equiv` | 818 | Padding and prefix extraction give exactly the original TMSAT witnesses. |
| `tmsat_comp_on_image` | 852 | Timed buffered composition assuming second-machine totality only on the first machine’s image. |
| `tmsat_deadline_bound` | 955 | The prescribed deadline formula majorizes normalized wrapper time. |
| `tmsat_constant_poly` | 990 | Finite-control constant emission gives a polynomial-time function. |
| `tmsat_exact_certificate_bits` | 1001 | Exact binary certificate generation in the prescribed three cases. |
| `tmsatWrapperOutput` | 1019 | Total mathematical wrapper specification; malformed pairs receive [false]. |
| `tmsat_quad_injective` | 1026 | Three pairing-injectivity steps pin all four components. |
| `tmsat_reduction_correct` | 1052 | A fixed wrapper with the prescribed accepting semantics gives exactly the source NP language. |

An initial visibility check caught that `deriving DecidableEq, Fintype` on a private inductive generated public instances. The final source uses explicitly private instances instead. The final kernel-level visibility check rejects any public declaration outside the five frozen declaration families and the mandated bridge family; it passed. Compiler-generated proof auxiliaries attached to the existing target theorems are listed in the kernel inventory.

## Verification evidence

- Lean: `leanprover/lean4:v4.25.0`, runtime commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, checked against the dependency checkout.
- Cache setup: successful `lake exe cache get` for the actual imported Mathlib modules; log included.
- Never invoked `lake build`. Iteration used the brief's direct-Lean script and direct scratch proof checks.
- Final authoritative sweep: **53/53 modules, exit 0, zero `error:` lines**, using a separate fresh olean tree after the visibility repair. Each module's script removes its old olean and requires a fresh result.
- Sweep admission warnings: **31 declarations** total, including three declarations in this owned file. The remaining warnings are unchanged out-of-scope declarations. Four source `sorry` sites here yield three declaration warnings because hardness contains two local admissions.
- All 41 explicit private declarations: axiom subsets of `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
- `timeConstructible_poly`: `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
- Bridge and all three TMSAT targets: standard axioms plus `sorryAx`, as expected for this partial delivery.
- A transitive constant-dependency traversal checks the precise admission roots; it does not infer them merely from source warning counts.
- Frozen signature/order/definition comparison: PASS. New public source declaration: bridge only. No removals. `git diff --check`: PASS.
- Style lint: zero FAIL; the file-size warning is justified above. The existing lint regex misses the `private noncomputable def` modifier order and therefore reports one fewer private declaration; the source inventory and kernel audit check all 41 explicitly.

Final sweep tail:

```text
CHECK 49 TCSlib/Complexity/ClassP
CHECK 50 TCSlib/Complexity/Uncomputability
CHECK 51 TCSlib/Complexity/Formulas
CHECK 52 TCSlib/Complexity/CookLevin
CHECK 53 TCSlib/Complexity/ClassNP
FULL_SWEEP_PASS modules=53
```

Axiom admission roots:

| Declaration | Direct/transitive `sorry` roots |
|---|---|
| `timeConstructible_poly` | none |
| `timed_universal_quantitative` | itself |
| `TMSAT_mem_NP` | itself (`D-MEM`), bridge |
| `TMSAT_NPHard` | itself (`D-WRAP`, `D-EMIT`) |
| `TMSAT_NPComplete` | membership, hardness, bridge |

Thus the bridge-only admission condition for a **completed** batch is not yet met. This report explicitly invokes the brief's partial-delivery continuation provision. No nonstandard axiom other than these listed admissions appears.

## Continuation and archive checks

Continue by discharging `D-MEM`, then `D-WRAP`, then `D-EMIT`, while the maintainer handles the Chapter-1 bridge addition serially. The marked goals already specify the total functions and exact formulas required. Do not replace exact certificate lengths with majorants or assume the simulator terminates on malformed requests.

`SHA256SUMS` covers every archive payload except the checksum file itself. `logs/package-validation.log` records bundle verification, application of the patch to a temporary index initialized at the base, and equality of the reconstructed tree with the delivered commit. The source in the archive is byte-identical to that commit. `verification/verify-lean.sh` reruns the full sweep and axiom audit from a repository with the patch applied; `verification/verify-freeze.py` reruns the source freeze and scope checks against the pinned base.

## ===== audits/ch2-epoch2-agent-reports/batchD-cont.md =====

# Chapter 2 E2 continuation, batch D — completed fill

All three owned admission sites were discharged in the required order: **D-MEM → D-WRAP → D-EMIT**. `TMSAT_mem_NP`, `TMSAT_NPHard`, and the unchanged `TMSAT_NPComplete` assembly are admission-free. The quantitative bridge and polynomial time-constructibility theorem are also admission-free and unchanged. No continuation or statement escalation remains.

## Repository, base, and delivery

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`, on `complexity/arora-barak-ch1`.
- Working branch: `fill/ch2-e2cont-D`.
- Delivered commit: `45ea0842138ff6027465400ef6a8d3fc37839276`.
- Delivered tree: `79df844f3c5a6d18862ca594ce34e841fbdc2dbd`.
- Only changed repository path: `TCSlib/Complexity/ClassNP/TMSAT.lean`.
- Final source size: **1908 lines**; **46 new explicit private declarations**, zero new public declarations.
- Source SHA-256: `e3a0647bb89d5e7e074516bf08191463e925f438f2e2a2339995a2ac446fe5e0`.
- Delivery: `fill-ch2-e2cont-D.zip`, with every file at the archive root, including `SHA256SUMS`. The root-level `TMSAT.lean` belongs at the owned repository path above.
- Single-agent execution. No remote write, PR, push, or modification of another branch.

The fetched branch tip was `cc103db9d9f00e28924a685919629be9b3ec1b63`. Before source work, ancestry was checked and only the newly created working branch was pinned back to the brief’s required base. The original branch reference was preserved.

Binding records read: `briefs/ch2-e2cont-batchD.md`, the original E2-D brief, `audits/ch2-epoch2-agent-reports/batchD.md`, `workflow.md`, `policy.md`, the inherited E1-A pitfalls, the phase-3 resolutions, D5 in `audits/ch1-infra-r3-findings.md`, and the canonical recipe in `machine-library-design.md` §9c. The required 57-module order was used.

## Target and route accounting

| Site | Discharge |
|---|---|
| D-MEM | `tmsat_request_poly`, `tmsat_good_bounds`, and `tmsat_result_accept`, composed with the existing `tmsat_simulator_total`, `tmsat_simulation_budget`, and `tmsat_comp_on_image` in the filled local `hV`. |
| D-WRAP | Filled local `hwrap`: P6 `computesFunInTime_pairValid`; P13 `computesFunInTime_pairConcat`; timed captured composition with the supplied verifier; W3 `computesFunInTime_cond` with a fixed `[false]` branch. Coefficient and degree are enlarged to positive values only at the runtime level. |
| D-EMIT | `tmsat_certificate_unary`; the unchanged `poly_unary_computes` instantiated at loop parameter `2*e*r-1` and coefficient `D`; nested `tmsat_pt_pair`; P6 `computesFunInTime_pairEncodeFixed α₀`. |
| Completeness | Existing conjunction body unchanged; its two dependencies are now closed. |

### D5 residuals and canonical assembly

| Named obligation | Concrete discharge and library use |
|---|---|
| Exact odd split, rejecting even lengths | P10 `computesFunInTime_splitSolve 1 1`; `tmsatSplit`, `tmsat_split_some`, `tmsat_split_exists`, `tmsat_split_append`, and `tmsat_split_components`. A successful index solves `i + (i+1) = input.length`, so the split is unique. |
| Three nested quadruple parses | P6 `pairFst`/`pairSnd` contracts, `tmsat_pair_inverse`, `tmsat_pair_valid`, and `tmsat_good_spec`. `tmsatGood` short-circuits through the split validity and all three spine validities. `tmsat_pt_and` realizes the ordering with W3. Failure is never inferred from an empty extracted component. |
| All-true checks on both unary fields | P11 `computesFunInTime_incFixed` plus `computesFunInTime_ifEq []`; `tmsat_inc_nonempty`, `tmsat_inc_none`, and `tmsat_pt_unary`. This includes both empty unary fields. |
| Timed variable-prefix extraction | The actual finite machine `tmsatTakeTM`, with `tmsat_take_double`, `tmsat_take_separator`, `tmsat_take_parse`, `tmsat_take_payload`, and `tmsat_take_computes`. It emits exactly `b.take a.length` on `pairEncode a b`, within `(pairEncode a b).length + 1`. Its application in `tmsat_pt_take` is restricted to constructed pairs using `tmsat_comp_on_image`; no unproved totality claim on malformed inputs is needed. |
| Unary-to-binary clock conversion | P4 `computesFunInTime_lengthBits` is placed under C1 `computesFunInTime_pairMapSnd`. `tmsat_request_poly` first retains the entire request as the head and the clock as payload, maps the payload length counter, and extracts the resulting binary clock. C1 never reads the head. |
| General computed pairing | `tmsat_pt_pair` follows §9c literally: P14 duplication and C1 constant-empty map form `H`; P14/C1 form the retained-input `s`; a second P14/C1 stage applies `g ∘ pairFst` to form `t`; P13 concatenation and P6 second extraction give the required pair. The lemma is reused for prefix-machine inputs, clock retention, timed requests, and reduction emission. |
| Well-formed simulator request on every input | `tmsatRequest` and `tmsat_request_poly`; failed guards choose the fixed request with code `[]`, input `[]`, and deadline zero. |
| Relocated and captured simulation | Existing `tmsat_comp_on_image` uses the proved `bufferedComp_start` and `bufferedSecondCfg_run`. D-MEM supplies simulator totality only on the preprocessor’s image. D-WRAP uses the proved polynomial timed-composition calculus. |
| Success and timeout budget | Existing `tmsat_simulator_total` consumes both quantitative-bridge clauses. `tmsat_good_bounds` feeds the original input-length bounds to `tmsat_simulation_budget`; no monotonicity assumption about canonizer time is introduced. |
| Complete-answer recognition | `tmsat_pt_eq [true,true]` and `tmsat_result_accept`, using existing `tmsatAnswer_accept`. The whole captured answer is checked; timeout and every other completed output reject. |
| Invalid requests reject | `tmsat_result_accept` uses `FinTM.not_computesInTime_zero` for the fallback. The simulator is never assumed total on arbitrary malformed strings. |

### Completed predecessor obligation map

| Original obligation | Discharging lemmas / assembly |
|---|---|
| Concrete polynomial-value computation | Existing `polyUnaryTM`, `poly_loop`, `poly_start`, `poly_unary_computes`, `timeConstructible_poly`; unchanged. |
| Uniform concrete coefficient arithmetic | Existing `tmsat_serialization_length`, `tmsat_serialization_parameters`, `tmsat_concrete_coefficient`; unchanged. |
| Public quantitative bridge | Existing proved `timed_universal_quantitative`, from `Turing.timed_universal_concrete`; unchanged. |
| Both source outcomes | `tmsat_simulator_total`, integrated in the filled D-MEM body. |
| Full-output acceptance | `tmsatAnswer_accept` → `tmsat_result_accept` → `tmsat_pt_eq [true,true]`. |
| Explicit polynomial-canonizer chain | `tmsat_simulation_budget` → `tmsat_good_bounds` → the filled local simulator/composition budget. |
| Certificate bound and exact padding | Existing `tmsat_quad_bounds` and `tmsat_certificate_equiv`, unchanged; implemented prefix recovery is `tmsat_pt_take`. |
| Odd split and unique split position | Existing `tmsat_split_length` and certificate equivalence, plus the new checked P10 route above. |
| Quadruple parser and unary checks | `tmsat_fields_poly`, `tmsat_good_spec`, `tmsat_good_quad`, and the named D5 discharges above. |
| Binary clock conversion | The P4-under-C1 stage of `tmsat_request_poly`. |
| Relocation-and-capture | Existing `tmsat_comp_on_image` plus the proved library composition/branch contracts. |
| Total wrapper, including malformed input | Filled local `hwrap`, exactly realizing unchanged `tmsatWrapperOutput`. |
| Normalization and lawful fixed code | Existing `one_work_tape_binary`, `exists_codeTM`, and `decode_encode` chain in hardness; unchanged and now fed a proved wrapper. |
| Exact certificate value, all three cases | Existing `tmsat_exact_certificate_bits` retained; direct exact unary counterpart `tmsat_certificate_unary` uses the same case table. |
| Prescribed deadline majorization | Existing `tmsat_deadline_bound`, unchanged, with the exact `r`, `D`, and `T'` formulas below. |
| Exact binary deadline | Existing local `hdeadline` from `timeConstructible_poly D (2*e*r-1)` retained unchanged. |
| Fixed code, retained input, exact unary runs, and nested layout | Filled `hemit`, using `tmsat_pt_pair`, the unary generators, and P6 fixed-code pairing. |
| Component pinning and reduction correctness | Existing `tmsat_quad_injective` and `tmsat_reduction_correct`; unchanged. |
| Completeness | Existing `TMSAT_NPComplete` body; unchanged. |

## Exact-value discipline

The certificate output is always exactly `List.replicate (C₀*(input.length+1)^c₀) true`.

| Case | Emission |
|---|---|
| `C₀ = 0` | Finite-control constant `[]`. |
| `C₀ > 0`, `c₀ = 0` | Finite-control constant `List.replicate C₀ true`. |
| `C₀ > 0`, `c₀ > 0` | P5 `computesFunInTime_polyUnary C₀ (c₀-1+1)`, with the proved equality `c₀-1+1=c₀`. The harvested loop index is `c₀-1`. |

The deadline alone majorizes the normalized verifier runtime. Its formulas remain exactly:

```text
r  = max 1 c₀
D  = (K+1)*(B+1)^2*(C₀+3)^(2*e)
T' n = D*(n+1)^(2*e*r)
```

The original `hdeadline` and `hcertificate` binary witnesses remain unchanged. The authorized direct-unary route avoids converting those binary values back by countdown: the deadline uses `poly_unary_computes (2*e*r-1) D`, with `2*e*r-1+1=2*e*r`, and the certificate uses the case table above. Append-only implementation notes document this in the original target docstrings. **Neither copy of `polyUnaryTM` / `poly_unary_computes` was removed or modified.** No certificate length is majorized.

## Statement freeze, scope, and helper hygiene

`verify-freeze.py` compared nonempty, comment-stripped declaration bodies and signatures against the required base. Results:

- All **47 existing explicit declarations** remain in their original relative order, with identical signatures and visibility.
- Only the two intended theorem bodies, `TMSAT_mem_NP` and `TMSAT_NPHard`, changed.
- All other existing bodies, including every definition, the bridge, both in-file polynomial generator declarations, and the completeness theorem, are identical after comment stripping.
- Every original docstring’s contents remain verbatim; two append-only continuation notes explain the implementations.
- Exactly one precise import was added: `Build.Primitives`.
- No source admissions, new axioms, `unsafe` declarations, or public additions.
- `git diff --check` passed. Only the owned source path differs from the base.

The kernel-level inventory independently checks every declaration owned by the compiled TMSAT module, including generated descendants. It contains **325 declarations**; the union of their complete dependency traversals has no admission roots and only the standard axiom triple. Every non-private name belongs to an existing public declaration family. This is stronger than checking only the headline theorem closures.

The final size is **1908 lines**, under the brief’s inherited exclusive-file exception. The increase is the concrete prefix machine, runtime calculus, guarded parser semantics, and their proofs. Moving them to shared files would violate this batch’s ownership; any later extraction belongs to serial maintainer work. Style lint reports **0 FAIL, 1 WARN**, the owned file’s size. The linter’s declaration regex misses the unchanged `private noncomputable def` modifier order; the source inventory and kernel audit cover it.

### Every new explicit declaration

All names below are private in `Complexity`. Their source line numbers refer to the delivered full source. Generated declarations are exhaustively listed in `axiom-print.log`.

| Private declaration | Line | Role |
|---|---:|---|
| `tmsat_pt_linear` | 895 | Embed linear-time contracts in the polynomial-time calculus. |
| `tmsat_pt_const` | 902 | Obtain fixed-word emission from finite control. |
| `tmsatFst` | 906 | Total first projection with an explicit separate validity guard. |
| `tmsatSnd` | 909 | Total second projection with an explicit separate validity guard. |
| `tmsatConcat` | 912 | Name P13’s total pair-to-concatenation function. |
| `tmsatMap` | 916 | Name C1’s payload-only map. |
| `tmsat_pt_map` | 921 | Bound C1 by a monotone polynomial envelope. |
| `tmsat_pt_pair` | 944 | Prove the canonical §9c general pairing assembly. |
| `tmsat_pt_cond` | 966 | Embed W3’s captured branch in the polynomial calculus. |
| `tmsat_pt_eq` | 990 | Test equality with an entire fixed word. |
| `tmsat_inc_nonempty` | 998 | A successful fixed-width increment never returns an empty word. |
| `tmsat_inc_none` | 1004 | Overflow is equivalent to exact all-true shape. |
| `tmsat_pt_unary` | 1011 | Decide unary shape by P11 overflow and whole-word equality. |
| `tmsatTakeTM` | 1028 | Concrete one-work-tape, four-state counted native-prefix machine. |
| `tmsatTakeCfg` | 1052 | Indexed parser/payload configurations with the unary counter. |
| `tmsat_take_read` | 1058 | Identify the exact native input symbol. |
| `tmsat_take_double` | 1064 | Two equal prefix bits install exactly one unary counter cell. |
| `tmsat_take_separator` | 1096 | The separator enters payload mode at the counter’s final cell. |
| `tmsat_take_parse` | 1128 | Exact parser run and counter installation. |
| `tmsat_take_payload` | 1163 | Exact bounded native-payload emission invariant. |
| `tmsat_take_computes` | 1197 | Compute the requested prefix within encoded-input length plus one. |
| `tmsat_pt_take` | 1245 | Compose only on constructed pairs, using the actual output-length bound. |
| `tmsat_pt_and` | 1267 | Short-circuit conjunction of polynomial-time bit tests. |
| `tmsat_pair_inverse` | 1279 | Reconstruct a successful aligned parse. |
| `tmsat_pair_valid` | 1299 | Reconstruct the original word from guarded projections. |
| `tmsatSplit` | 1309 | P10 exact split at coefficient and degree one. |
| `tmsat_split_some` | 1315 | Every successful split satisfies the exact length equation. |
| `tmsat_split_exists` | 1322 | The unique solution is returned by the bounded search. |
| `tmsat_split_append` | 1334 | Recover an instance and its exact padded certificate. |
| `tmsat_split_components` | 1341 | Recover concatenation and the one-bit length difference. |
| `tmsatY` | 1356 | The recovered instance field. |
| `tmsatW` | 1359 | The recovered padded certificate. |
| `tmsatCode` | 1362 | The recovered machine code. |
| `tmsatInput` | 1365 | The recovered source input. |
| `tmsatWidth` | 1368 | The parsed unary certificate-length field. |
| `tmsatClock` | 1371 | The parsed unary deadline field. |
| `tmsatGood` | 1375 | Ordered grammar and exact unary-shape guards. |
| `tmsat_good_spec` | 1384 | Successful guards reconstruct the exact quadruple and split. |
| `tmsat_good_quad` | 1403 | Well-formed quadruples pass guards and recover every field literally. |
| `tmsat_fields_poly` | 1416 | Assemble the polynomial-time field and guard contracts. |
| `tmsatRequest` | 1437 | Valid simulator request, with a zero-deadline fallback. |
| `tmsatResult` | 1444 | Exact tagged simulator answer corresponding to preprocessing. |
| `tmsat_request_poly` | 1458 | Polynomial-time guarded request assembly and payload clock conversion. |
| `tmsat_good_bounds` | 1473 | Code length and deadline fit the original verifier-input length. |
| `tmsat_result_accept` | 1491 | Whole-answer equality is exactly the existential verifier language. |
| `tmsat_certificate_unary` | 1760 | Exact unary certificate emission by the binding three-case table. |

## Verification evidence

- Lean `leanprover/lean4:v4.25.0`; runtime commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, checked against its checkout.
- `lake exe cache get` invoked once and completed successfully; `cache-setup.log` included. Pinned toolchain and dependency artifacts already present in the workspace were reused. Native launch uses an existing readlink compatibility shim for this execution environment; the compiler and its pin are unchanged.
- No manual `lake build` invocation. All source verification used `scripts/lean_check_tree.sh` and direct Lean for the axiom instrument.
- D-MEM was compiled closed before D-WRAP was filled; D-WRAP was compiled closed before D-EMIT was filled. Final owned-module compilation has no errors or warnings.
- Final authoritative sweep used a **separate fresh olean tree**: **57/57 ordered modules, exit 0, zero `error:` lines**. The check script removes the target olean and requires a freshly produced nonempty one for each module.
- **26 out-of-scope declaration admission warnings** remain in the campaign; **zero** in the owned module. Out-of-scope source files are byte-identical to the base.
- The final axiom instrument ran against that final fresh tree, not bootstrap artifacts. It checks headline prints, exact admission roots, all owned kernel declarations, all dependency axioms, and public visibility.
- Frozen-source and archive checks are independently rerunnable using the included scripts.

Exact headline prints and root reports:

```text
'Complexity.timeConstructible_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.timed_universal_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.timed_universal_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.timeConstructible_poly: []
ROOTS Turing.timed_universal_concrete: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Complexity.TMSAT_mem_NP: []
ROOTS Complexity.TMSAT_NPHard: []
ROOTS Complexity.TMSAT_NPComplete: []
```

Final sweep tail:

```text
CHECK 52 TCSlib/Complexity/TuringMachine
CHECK 53 TCSlib/Complexity/ClassP
CHECK 54 TCSlib/Complexity/Uncomputability
CHECK 55 TCSlib/Complexity/Formulas
CHECK 56 TCSlib/Complexity/CookLevin
CHECK 57 TCSlib/Complexity/ClassNP
FULL_SWEEP_PASS modules=57
```

## Archive and integration checks

The one format-patch is against the exact required base. The incremental bundle advertises only `refs/heads/fill/ch2-e2cont-D`, with the required base as its sole prerequisite. Bundle verification passed. Applying the patch to a temporary index initialized at that base reproduces the delivered commit’s entire tree. The root-level full source is byte-identical to the committed source. `package-validation.log` records these checks.

Apply `0001-ch2-e2cont-D.patch` using the maintainer’s normal integration process. With the pinned dependencies available and the branch name retained, `bash verify-lean.sh /path/to/patched/repo /path/to/output` reruns the fresh sweep, axiom audit, freeze check, and lint. The source checker deliberately enforces this batch’s working branch name; for integration on another branch, review that one branch guard separately rather than changing any source statement.

`SHA256SUMS` covers every archive payload except itself. All ZIP members are regular root-level files; no enclosing directory or nested source tree is needed. The archive includes the report, full source, patch, bundle, final sweep and axiom logs, source-freeze inventory, lint and environment records, package-validation evidence, cache log, summary, and reproduction scripts.

## Escalations and requested shared lemmas

None. All named D5 residuals and the three owned admissions are discharged. The fill is ready for maintainer integration and audit.

## ===== audits/programs/ch2-e2-ClosureAxioms.lean =====

import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer attestation: B2 integration — epoch-2 closure.
-- Expected: ALL TEN epoch-2 targets (12 printed names: the campaign table's 11
-- plus timed_universal_quantitative) admission-free; Chapter-1 headline and
-- library regressions unchanged; the E3 statement layer untouched at its own
-- roots.

open Lean Elab Command

namespace B2ClosureAudit

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

partial def visit (name : Name) : WalkM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      modify fun s => { s with roots := s.roots.push name }
    deps.forM visit
    match ci with
    | .inductInfo i => i.ctors.forM visit
    | _ => pure ()

def roots (env : Environment) (name : Name) : Array Name :=
  (((visit name).run env).run {}).2.roots

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def userRoots (env : Environment) (name : Name) : List Name :=
  ((roots env name).map privateToUserName).toList.eraseDups.mergeSort
    (fun a b => a.toString ≤ b.toString)

run_cmd do
  let env ← getEnv
  let expectations : Array (Name × List Name) := #[
    -- Epoch-2 targets, all ten closed (12 printed names).
    (``Complexity.NP_subset_EXP, []),
    (``Complexity.HALT_NPHard, []),
    (``Complexity.HALT_not_mem_NP, []),
    (``Complexity.ntime_poly_subset_NP, []),
    (``Complexity.NP_subset_iUnion_NTIME, []),
    (``Complexity.NP_eq_iUnion_NTIME, []),
    (``Complexity.mem_NP_iff_exists_length_le, []),
    (``Complexity.timeConstructible_poly, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Complexity.TMSAT_mem_NP, []),
    (``Complexity.TMSAT_NPHard, []),
    (``Complexity.TMSAT_NPComplete, []),
    -- Chapter-1 headline and library regressions.
    (``Turing.timed_universal, []),
    (``Turing.timed_universal_concrete, []),
    (``Turing.FinTM.exists_loopCfgTM, []),
    (``Turing.FinTM.computesFunInTime_splitSolve, []),
    (``Turing.capture_run, []),
    -- E3 statement layer, untouched.
    (``Complexity.EXP_subset_NEXP, [``Complexity.EXP_subset_NEXP])]
  for (name, expectedRaw) in expectations do
    let expected := expectedRaw.eraseDups.mergeSort (fun a b => a.toString ≤ b.toString)
    let found := userRoots env name
    logInfo m!"ROOTS {name}: {found}"
    unless found == expected do
      throwError "Unexpected admission roots for {name}: {found}; expected {expected}"
    let ax ← collectAxioms name
    unless ax.all (fun a => allowed.contains a || a == ``sorryAx) do
      throwError "Unexpected axiom for {name}: {ax}"
    if expected.isEmpty && ax.contains ``sorryAx then
      throwError "Unexpected sorryAx for {name}"
    unless expected.isEmpty || ax.contains ``sorryAx do
      throwError "Expected sorryAx for {name} but it is absent"
  logInfo "B2 CLOSURE AUDIT PASS: all ten epoch-2 targets admission-free; Chapter-1 and library regressions unchanged; E3 statement layer at its own roots."

end B2ClosureAudit

## ===== audits/logs/ch2-e2cont-B2-integration-sweep.log =====

CHECK TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/Deterministic
CHECK TCSlib/Complexity/TuringMachine/StateRenaming
CHECK TCSlib/Complexity/TuringMachine/Finite
CHECK TCSlib/Complexity/TuringMachine/Oracle
CHECK TCSlib/Complexity/TuringMachine/Simulation
CHECK TCSlib/Complexity/TuringMachine/Sweep
CHECK TCSlib/Complexity/TuringMachine/Composition
CHECK TCSlib/Complexity/TuringMachine/Build/Convention
CHECK TCSlib/Complexity/TuringMachine/Build/Wrappers
CHECK TCSlib/Complexity/TuringMachine/Build/Loop
CHECK TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
CHECK TCSlib/Complexity/TuringMachine/Robustness/SingleTape
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/ClassP/DTIME
CHECK TCSlib/Complexity/ClassP/TimeConstructible
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
CHECK TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/ClassP/P
CHECK TCSlib/Complexity/ClassP/ModelInvariance
CHECK TCSlib/Complexity/ClassP/Examples
CHECK TCSlib/Complexity/TuringMachine/Encoding
CHECK TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2491:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2497:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2491:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2497:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2489:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2519:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2519:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2507:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2511:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2569:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2532:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2537:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2540:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2579:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2603:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2926:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2926:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3025:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3173:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3203:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3203:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3266:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3311:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3351:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3399:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:448:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:454:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:459:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:484:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:490:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:495:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:719:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:821:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:314:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:337:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:362:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:427:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:434:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:470:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:477:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:487:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:621:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:644:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:659:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:638:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:684:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:761:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:820:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:847:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:889:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:897:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1006:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1106:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1578:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1606:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2278:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK TCSlib/Complexity/Uncomputability/Computable
CHECK TCSlib/Complexity/Uncomputability/Diagonalization
CHECK TCSlib/Complexity/Uncomputability/Halting
CHECK TCSlib/Complexity/TuringMachine/Nondeterministic
CHECK TCSlib/Complexity/Formulas/CNF
CHECK TCSlib/Complexity/Formulas/CNFEncoding
CHECK TCSlib/Complexity/Formulas/DNF
CHECK TCSlib/Complexity/ClassNP/PolyTime
CHECK TCSlib/Complexity/ClassNP/NP
CHECK TCSlib/Complexity/ClassNP/CoNP
CHECK TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:2884:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Reductions
CHECK TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
CHECK TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2550:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2571:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2582:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2618:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:2624:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:120:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:155:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/TMSAT
CHECK TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Snapshot.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:192:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:204:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:244:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE

## ===== audits/logs/ch2-e2cont-B2-axioms.log =====

B2 integration: epoch-2 closure axiom attestation
HEAD: 1514fd6b19b9ead81bbc556e9f6b5a816009cec4
UTC: 2026-10-05T04:17:53Z
ROOTS Complexity.NP_subset_EXP: []
ROOTS Complexity.HALT_NPHard: []
ROOTS Complexity.HALT_not_mem_NP: []
ROOTS Complexity.ntime_poly_subset_NP: []
ROOTS Complexity.NP_subset_iUnion_NTIME: []
ROOTS Complexity.NP_eq_iUnion_NTIME: []
ROOTS Complexity.mem_NP_iff_exists_length_le: []
ROOTS Complexity.timeConstructible_poly: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Complexity.TMSAT_mem_NP: []
ROOTS Complexity.TMSAT_NPHard: []
ROOTS Complexity.TMSAT_NPComplete: []
ROOTS Turing.timed_universal: []
ROOTS Turing.timed_universal_concrete: []
ROOTS Turing.FinTM.exists_loopCfgTM: []
ROOTS Turing.FinTM.computesFunInTime_splitSolve: []
ROOTS Turing.capture_run: []
ROOTS Complexity.EXP_subset_NEXP: [Complexity.EXP_subset_NEXP]
B2 CLOSURE AUDIT PASS: all ten epoch-2 targets admission-free; Chapter-1 and library regressions unchanged; E3 statement layer at its own roots.
lean exit: 0

## ===== audits/logs/ch2-e2cont-B2-lint.log =====

FAIL  TCSlib/Complexity/NPReductions/NAESATToColoring.lean                line 119: public def `nae_sat_eg` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/NAESATToColoring.lean                line 121: public def `assign_eg` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/SATTo3SAT.lean                       module docstring lacks a `## References` section
FAIL  TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean            module docstring lacks a `## References` section
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToClique.lean                module docstring lacks a `## References` section
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 75: public inductive `Literal` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 79: public structure `Clause` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 84: public def `SatisfiesLiteral` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 88: public def `SatisfiesClause` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 91: public abbrev `Sat3` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 93: public def `SatisfiesSat3` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 96: public def `IsSatisfiable` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 102: public def `sat3_inst` has no preceding docstring (policy section 2, statement prose)
FAIL  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              line 108: public def `ex_assign_1` has no preceding docstring (policy section 2, statement prose)
WARN  TCSlib/Complexity/ClassNP/EXP.lean                                  2887 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Nondeterminism.lean                       2627 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean                                1908 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2698 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               4418 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/CircuitComplexity/Basic.lean                      691 lines > target 600
INFO  TCSlib/Complexity/CircuitComplexity/Basic.lean                      691 lines; 61 public / 5 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/CircuitSat.lean                 413 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/Encoding.lean                   442 lines; 25 public / 3 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/FeedForward.lean                356 lines; 21 public / 1 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/Formulas.lean                   92 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/HardFunctions.lean              281 lines; 5 public / 5 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/Hierarchy.lean                  327 lines; 24 public / 1 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/NCAC.lean                       532 lines; 25 public / 22 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/PPoly.lean                      153 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/Parity.lean                     405 lines; 10 public / 29 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/SizeClasses.lean                162 lines; 17 public / 2 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/UHalt.lean                      104 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean             226 lines; 22 public / 1 private declarations
INFO  TCSlib/Complexity/CircuitComplexity/Universal.lean                  177 lines; 11 public / 2 private declarations
INFO  TCSlib/Complexity/CircuitComplexity.lean                            82 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/CoNP.lean                                 165 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/EXP.lean                                  2887 lines; 6 public / 135 private declarations
INFO  TCSlib/Complexity/ClassNP/NP.lean                                   679 lines > target 600
INFO  TCSlib/Complexity/ClassNP/NP.lean                                   679 lines; 3 public / 38 private declarations
INFO  TCSlib/Complexity/ClassNP/NTIME.lean                                222 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean                       2627 lines; 8 public / 110 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTime.lean                             162 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/Reductions.lean                           477 lines; 10 public / 16 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean                                  158 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean                                1908 lines; 6 public / 86 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean                            133 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP.lean                                      48 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/ClassP/DTIME.lean                                 117 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassP/Examples.lean                              362 lines; 3 public / 15 private declarations
INFO  TCSlib/Complexity/ClassP/ModelInvariance.lean                       133 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassP/P.lean                                     129 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/ClassP/TimeConstructible.lean                     457 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/ClassP.lean                                       28 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/CookLevin/Hardness.lean                           237 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/CookLevin/Snapshot.lean                           252 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/CookLevin.lean                                    23 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas/CNF.lean                                 259 lines; 5 public / 8 private declarations
INFO  TCSlib/Complexity/Formulas/CNFEncoding.lean                         475 lines; 13 public / 9 private declarations
INFO  TCSlib/Complexity/Formulas/DNF.lean                                 118 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas.lean                                     26 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/NPReductions/NAESATToColoring.lean                388 lines; 14 public / 2 private declarations
INFO  TCSlib/Complexity/NPReductions/SATTo3SAT.lean                       884 lines > target 600
INFO  TCSlib/Complexity/NPReductions/SATTo3SAT.lean                       884 lines; 37 public / 4 private declarations
INFO  TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean            192 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/NPReductions/ThreeSATToClique.lean                342 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean              405 lines; 16 public / 3 private declarations
INFO  TCSlib/Complexity/NPReductions.lean                                 26 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               122 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2698 lines; 5 public / 95 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               4418 lines; 15 public / 167 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 687 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 687 lines; 7 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines; 13 public / 49 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines; 6 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  403 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       481 lines; 19 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         257 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines; 1 public / 73 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               248 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         517 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   600 lines; 1 public / 50 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines; 2 public / 53 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines; 4 public / 130 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations
INFO  TCSlib/Complexity/TuringMachine.lean                                88 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/Uncomputability/Computable.lean                   88 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/Uncomputability/Diagonalization.lean              119 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/Uncomputability/Halting.lean                      198 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Uncomputability.lean                              26 lines; 0 public / 0 private declarations

style_lint: 14 FAIL, 11 WARN over 78 files
WARN  TCSlib/Complexity/ClassNP/EXP.lean             2887 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Nondeterminism.lean  2627 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean           1908 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassNP/CoNP.lean            165 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/EXP.lean             2887 lines; 6 public / 135 private declarations
INFO  TCSlib/Complexity/ClassNP/NP.lean              679 lines > target 600
INFO  TCSlib/Complexity/ClassNP/NP.lean              679 lines; 3 public / 38 private declarations
INFO  TCSlib/Complexity/ClassNP/NTIME.lean           222 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean  2627 lines; 8 public / 110 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTime.lean        162 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/Reductions.lean      477 lines; 10 public / 16 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean             158 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean           1908 lines; 6 public / 86 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean       133 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 3 WARN over 10 files

## ===== audits/evidence/ch2-epoch2/span-attestation.md =====

# Maintainer whole-epoch attestation — Chapter 2, epoch 2

Evidence for the epoch-2 audit pack (`audits/ch2-epoch2-pack.md`). Every
claim below was produced by the maintainer from the repository alone,
independent of the delivery agents' own attestations. Span:
`f317f0c7` (close of the epoch-1 gate) → `2e176f60` (B2 integration
attestation); the pack commit follows.

## 1. Commit enumeration

**Ten Codex-authored fill commits, nine zip deliveries** (replayed
byte-identically from `git format-patch` series before each `git am -3`;
per-delivery verification recorded in the `AroraBarakChapter2Plan.md`
decision log at each integration):

| Zip | Commit(s) | File(s) | REPORT |
|---|---|---|---|
| fill-ch2-e2-A | `da8bd091` | EXP.lean | batchA.md |
| fill-ch2-e2-B | `3e076219` | Nondeterminism.lean | batchB.md |
| fill-ch2-e2-C | `53a884cd` | NP.lean, Reductions.lean | batchC.md (+ batchC-continuation.md, its filed continuation plan) |
| fill-ch2-e2-D | `4b4cd418` | TMSAT.lean | batchD.md |
| fill-ch2-e2cont-A | `7fa3c08d` | EXP.lean | batchA-cont.md |
| fill-ch2-e2cont-B | `42e2f65f`, `4df03129` | Nondeterminism.lean | batchB-cont.md |
| fill-ch2-e2cont-C | `db617dea` | NP.lean | batchC-cont.md |
| fill-ch2-e2cont-D | `9f748601` | TMSAT.lean | batchD-cont.md |
| fill-ch2-e2cont-B2 | `1514fd6b` | Nondeterminism.lean | batchB2.md |

**Three maintainer integration commits** (`a6c1804a`, `e72d95bf`,
`2e176f60`): verified by `git show --stat` to touch **no `.lean` source**
— records, logs, programs, and reports only.

**Interleaved, separately audited material.** The entire
machine-construction-library campaign sits inside this git span
(`71d90d39` design freeze → `64d82f84` fill-gate close) and was audited
under its own two gates (`audits/ch1-infra-resolutions.md`,
`audits/ch1-libfill-resolutions.md`). One of its commits, `e8dd3e57`
(bridge export), is the only non-Codex commit in the span that touches an
epoch-2 file: its `TMSAT.lean` slice (the discharge of the sanctioned
bridge `timed_universal_quantitative`, 1,185 → 1,206 lines) was
byte-decomposed and proof-audited at the infra gate (that pack's scope
item and freeze item 4). It is therefore **out of scope** for the epoch-2
gate.

No other commit in the span touches the five owned files. Per-file
`git log f317f0c7..HEAD -- <file>` outputs are exactly the rows above
(plus `e8dd3e57` for TMSAT.lean).

## 2. Per-file ledger (baseline `f317f0c7` → HEAD)

| File | Lines | Public decls | Private decls | New imports (whole span) |
|---|---|---|---|---|
| EXP.lean | 143 → 2,887 | 6 → 6 | 0 → 135 | `Build.Primitives` |
| Nondeterminism.lean | 239 → 2,627 | 8 → 8 | 0 → 110 | `Simulation`, `Build.Primitives`, `Mathlib.Tactic.FinCases` |
| NP.lean | 137 → 679 | 3 → 3 | 0 → 38 | `Build.Primitives` |
| Reductions.lean | 210 → 477 | 10 → 10 | 0 → 16 | none |
| TMSAT.lean | 244 → 1,908 | 5 → 6 | 0 → 87 | `Build.Primitives`, `Universal` (bridge, audited), `Mathlib.Tactic.Ring`, `Mathlib.Tactic.DeriveFintype` |

All imports are order-legal in the committed 57-module list (the owned
files sit after `Build/` and `Universal`); no cycles.

**Public-surface freeze.** Name-level extraction
(`^(theorem|lemma|def|abbrev|instance|structure|inductive|noncomputable
def) <ident>`) at baseline vs HEAD is **identical for every file except
TMSAT.lean, which adds exactly `timed_universal_quantitative`** — the
bridge statement sanctioned in advance by batch 2D's bridge protocol,
added by the 2D checkpoint, and statement-and-proof audited at the infra
gate. Three flush-left docstring prose lines beginning with a declaration
keyword (`EXP.lean:457` "lemma proves …", `TMSAT.lean:698` "lemma from
Chapter 1 …", `TMSAT.lean:703` "theorem with the private startup …")
are grep artifacts, inside `/- … -/` blocks, not declarations.

**Net deletion audit (whole span).** The net diff of the five files
deletes exactly:

- **11 `sorry` lines** — the eleven closed theorem names (EXP 1,
  Nondeterminism 3, NP 1, Reductions 2, TMSAT 4);
- **6 docstring tail lines** (EXP 1, Nondeterminism 2, TMSAT 3) — each
  the closing line of a sketch docstring re-emitted with an append-only
  completion note (per-delivery deleted-line audits confirmed
  append-only at each integration);
- **1 statement line** (`NP.lean`, `mem_NP_iff_exists_length_le`'s
  `∃ u : List Bool, …` line) — the 2C checkpoint's recorded cosmetic:
  re-emitted token-identical with a doubled space before `:= by`
  (disclosed and verified at checkpoint integration).

Nothing else is deleted in-span. Intermediate placeholders (the
checkpoints' `CONTINUATION` markers, the checkpoint-admitted private
`enumMachine_contracts`, the 2B frontier comment) were added and removed
inside the span, so they cancel in the net record.

## 3. Private-helper arithmetic

Per-REPORT new-private counts, cross-checked against the per-file
`^private ` counts at HEAD:

| Stratum | A | B | C | D | Σ |
|---|---|---|---|---|---|
| Checkpoints | 40 | 32 | 34 | 41 | 147 |
| Continuations | 95 | 36 | 20 | 46 | 197 |
| B2 | — | 42 | — | — | 42 |
| **Σ** | **135** | **110** | **54** | **87** | **386** |

HEAD per-file counts: EXP 135, Nondeterminism 110, NP 38 + Reductions 16
= 54 (batch C owned both), TMSAT 87. **Total 386 = 147 + 197 + 42
exactly**; the bridge-export commit added zero privates to TMSAT.lean.

## 4. Admission ledger

Fresh-olean sweeps over the committed module order at each integration
(all logs under `audits/logs/`):

| State | Commit | Modules | Admissions |
|---|---|---|---|
| Baseline (epoch-1 gate closed) | `f317f0c7` | 53 | 32 |
| Checkpoints integrated | `a6c1804a` | 53 | 29 (= 32 − 5 target bodies written + 2 new sites: `enumMachine_contracts`, the bridge) |
| Continuations integrated | `e72d95bf` | 57 | 23 (= 2 B frontiers + 5 padding + `EXP_subset_NEXP` + 15 E3/E4) |
| B2 integrated | `1514fd6b` | 57 | **21** (= 5 padding + `EXP_subset_NEXP` + 15 E3/E4) |

Final distribution (from `ch2-e2cont-B2-integration-sweep.log`):
Nondeterminism 5 (epoch-3 padding), EXP 1 (`EXP_subset_NEXP`), SAT 3,
Tautology 2, CookLevin 10. Net over the span: −11 = the eleven closed
names. 32 − 11 = 21.

## 5. Closure attestation

Maintainer kernel type/value traversal (opaque values and constructors
included), program committed at `audits/programs/ch2-e2-ClosureAxioms.lean`,
run against the fresh sweep oleans at `1514fd6b`
(`audits/logs/ch2-e2cont-B2-axioms.log`, exit 0): all twelve closure
names (the eleven targets plus the bridge) have **empty admission-root
sets and at most the standard triple**; the Chapter-1 headline and
library regressions (`timed_universal`, `timed_universal_concrete`,
`exists_loopCfgTM`, `computesFunInTime_splitSolve`, `capture_run`)
unchanged; `EXP_subset_NEXP` at exactly its own root.

Earlier integration traversals (`ch2-e2-checkpoint-axioms.log`,
`ch2-e2cont-axioms.log`) confirmed every intermediate `sorryAx` root
exactly as disclosed at each stage, including the A/C-cluster funnel
through the single admitted private `enumMachine_contracts`.

## 6. Policy

Lint at `2e176f60` (`audits/logs/ch2-e2cont-B2-lint.log`), ClassNP
scope: **0 FAIL, 3 WARN** — the recorded size exceptions EXP 2,887,
Nondeterminism 2,627, TMSAT 1,908 (each justified at its integration
under exclusive single-file fill ownership; extraction/dedup is the
recorded E5/D7 follow-up). Repo-wide, the only FAILs are 14 pre-existing
items in `NPReductions/*`, untouched by the span (no span commit touches
that directory).

## ===== scripts/ab_ch1_module_order.txt =====

TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Deterministic
TCSlib/Complexity/TuringMachine/StateRenaming
TCSlib/Complexity/TuringMachine/Finite
TCSlib/Complexity/TuringMachine/Oracle
TCSlib/Complexity/TuringMachine/Simulation
TCSlib/Complexity/TuringMachine/Sweep
TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Build/Convention
TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/ClassP/DTIME
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/ClassP/P
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Computable
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/TuringMachine/Nondeterministic
TCSlib/Complexity/Formulas/CNF
TCSlib/Complexity/Formulas/CNFEncoding
TCSlib/Complexity/Formulas/DNF
TCSlib/Complexity/ClassNP/PolyTime
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/Reductions
TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/ClassP
TCSlib/Complexity/Uncomputability
TCSlib/Complexity/Formulas
TCSlib/Complexity/CookLevin
TCSlib/Complexity/ClassNP
