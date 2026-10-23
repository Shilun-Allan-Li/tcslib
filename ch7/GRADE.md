# Chapter 7 completeness grade, round 3 (printed AB09, pp. 123–143)

Independent grader pass, 2026-10-14, worktree `tcstcslib-ch7`, branch
`complexity/arora-barak-ch7`, HEAD `a90db5bb`. Paths below are relative to
`TCSlib/Complexity/`.

## History

- **Round 1: INCOMPLETE.** Ten problems, P1–P10: Lemma 7.9 and Thm 7.10 were proved only
  abstractly, Ex 7.11(d) was weakened, §7.4.2 was missing for RTIME, the p.129 `∏(1+xᵢ)` example
  was missing, BP·P = BPP and the two "BPP = P ⇒ …" consequences were missing, NOT_FORMALIZED
  was not exhaustive, draft numbering was still in use, Ex 7.11(b)(a) was ℚ-only, and SURVEY
  had stale rows.
- **Round 2: INCOMPLETE.** P1–P10 were all resolved. Two new problems: R1, p.125 says the
  constant can be changed for BPTIME(T(n)) as well as for BPP, and that half was neither
  formalized nor listed (round 2 also asked that the §7.4.2 polynomial-class scope be noted);
  R2, SURVEY row G2 cited the wrong namespace.
- **Round 3 (this file):** R1 and R2 are resolved. A further pass over the printed chapter found
  one unlisted literature claim in the chapter notes (R3, below). The coordinator fixed R3 and I
  re-checked it in an addendum (§6), so this round's final verdict is COMPLETE.

## 1. Round-2 problems: status

| # | Problem | Fix found | Check | Status |
|---|---|---|---|---|
| R1 | p.125: the BPTIME(T(n)) half of "any constant > 1/2" | `Randomized.BPTIMEWith` and `Randomized.BPTIMEWith_eq_BPTIME` in `Randomized/BPTIMEThreshold.lean`, plus a NOT_FORMALIZED row for §7.4.2 with general T | See §2 | RESOLVED |
| R2 | SURVEY G2 namespace | SURVEY.md:197 now cites `Randomized.P_ssubset_DTIME_pow_log` | Declaration resolves | RESOLVED |

## 2. R1 in detail

**Statement.** The elaborated type (probe `#check`) is
`∀ {ρ : ℚ}, 1/2 < ρ → ρ < 1 → ∀ T : ℕ → ℕ, BPTIMEWith ρ T = BPTIME T`.

- `BPTIMEWith ρ T` is defined as `{L | ∃ c N, N.BPDecidesInTimeWith L (c·T) (fun _ => ρ)}`.
  `BPDecidesInTimeWith` (PTMEquiv.lean:183) requires that every branch halt within `T(|x|)` and
  that `ρ ≤ Pr[M(x) = L(x)]`. This is exactly Def 7.2 with `2/3` replaced by `ρ`, and with
  `O(T)` written as `c·T`.
- `BPTIMEWith (2/3) T = BPTIME T` holds by `rfl` against `BPTIME` (PTM.lean:268), so the
  statement compares the right classes.
- There is no hypothesis on `T`. That is at least as general as the printed claim, which
  §7.4.1 makes precise only for BPP.
- The range `ρ ∈ (1/2, 1)` is the intended reading of "any other constant greater than half".
  For `ρ > 1` the class is empty, and `ρ = 1` changes the class. Restricting `ρ` to `ℚ` loses
  nothing, because the class is antitone in `ρ`. Both points are recorded in the file header.
- The proof is genuine: majority of `2n+1` runs of the `Amplify.amp` repetition machine, with
  run time `t + 2n(2t+3) + 1 ≤ (10n+2)·c·T`, using `one_le`.

**Sorry and axioms.** `BPTIMEThreshold.lean` contains no `sorry`. Probe
`Randomized/Scratch_Grader3.lean` was built only through `lb.sh`; log
`scratchpad/ch7/logs/build-180015-67287.log`. The probe has been deleted. Its build exit was
non-zero only because the probe's own last line named a constant that the imported module does
not provide (`haltProb_le_truncate` lives in `ExpectedTime.lean`, and its name was confirmed by
grep). All requested results printed before that line:

- `Randomized.BPTIMEWith_eq_BPTIME`: `[propext, Classical.choice, Quot.sound]`
- `Randomized.Amplify.majority_randProb_ge`: `[propext, Classical.choice, Quot.sound]`
- `Randomized.Amplify.amp_haltsWithin_pos`: `[propext, Classical.choice, Quot.sound]`
- `Turing.FinNDTM.BPDecidesInTimeWith.amp`: `[propext, Classical.choice, Quot.sound]`

**NOT_FORMALIZED row for §7.4.2 with general T.**

- *Accurate.* The printed §7.4.2 (p.133) builds `M′` "by simply adding a counter and halting …
  after 100T(n) steps". That needs `100·T(n)` to be computable within the time budget, which is
  time-constructibility, and the book leaves it implicit. The row cites the machine-level Markov
  truncation (`Turing.FinNDTM.haltProb_le_truncate`, `ZDecidesInTime.truncate`) and the three
  polynomial-class equalities (`BPP_ExpPTM_eq_BPP_PTM`, `RP_ExpPTM_eq_RP_PTM`,
  `coRP_ExpPTM_eq_coRP_PTM`). All of them exist.
- *Legitimate.* The exclusion is an implicit-hypothesis aside, nothing in the chapter uses the
  general-T form, and it is the row that round 2 asked for.

## 3. Independent pass over the printed chapter (round 3)

I re-read the whole chapter: the introduction, §§7.1–7.7, footnotes 1–7, Note 7.11, "What have
we learned", the chapter notes and Exercises 7.1–7.11 with all sub-parts. I checked them against
SURVEY.md and NOT_FORMALIZED.md. The round-2 item-by-item verdict table still holds, with these
updates:

- p.125 / §7.4.1, "any constant > 1/2" for BPTIME(T(n)) and BPP: **OK** (SURVEY G5:
  `BPTIMEWith_eq_BPTIME`, `BPP_PTMWith_const_eq_BPP_PTM`).
- §7.4.2: **OK**. The polynomial classes are proved, and general T is listed with a legitimate
  reason.
- Everything else (Defs 7.1–7.3, 7.6, 7.7, 7.16–7.18; Claim 7.4; Lemmas 7.5, 7.9, 7.12, 7.13;
  Thms 7.8, 7.10, 7.14, 7.15, 7.19; Note 7.11; the p.129 example; the fingerprinting and Lovász
  arguments; the §7.5 consequences; §7.5.3; Exercises 7.1–7.11(e)) is unchanged and **OK**.
- **New: chapter notes p.140.** "Subsequent probabilistic NC algorithms can find a perfect
  matching as well; see [KUW85, MVV87]." This is a result the book cites from the literature.
  It is neither formalized nor listed. Its sibling notes items are listed (Lovász NC [Lov79];
  [Can96, RS95]; BPP/1; promise-BPP; PP), and by the round-1 P7 and round-2 R1 standard an
  unlisted exclusion fails. The exclusion itself would be legitimate: the result is cited, and
  nothing depends on it. See R3.
- Minor and not blocking: "Another primality test from the same era is due to Rabin [Rab80]"
  (p.140) is a historical remark that names an algorithm without stating a property. It may be
  folded into the same literature row, but this is optional.

**Name check.** I extracted all 190 dotted backticked names in SURVEY.md and NOT_FORMALIZED.md.
Every one resolves to a declaration under `TCSlib/`, by a Python regex over every `.lean` file.

## 4. Sorry check

`grep -w` for `sorry`, `admit` and `native_decide` over `Randomized/*.lean` (65 files,
including `BPTIMEThreshold.lean`), `ClassP/BinaryArith/*.lean` and
`SpaceComplexity/Machines/NARM{Prob,PSem,Logspace}.lean` finds no hits. The earlier substring
hits were the English words "admits" (PTM.lean:45) and "admitting" (Yap.lean:248). The
scratch probe has been deleted, and the working tree has no tracked changes apart from this file.

## 5. Problems found (round 3)

- **R3: chapter notes (p.140), [KUW85, MVV87] not listed (since resolved; see §6).** The claim that probabilistic NC
  algorithms can also *find* a perfect matching is a cited literature result with no row in
  NOT_FORMALIZED.md. It needs a row in the "Results the chapter mentions but attributes to … the
  literature" section, either a new row or an extension of the Lovász/NC row. Optionally, add
  Rabin's primality test [Rab80] to the PRIMES row. This is a documentation-only fix.

## 6. Addendum: R3 re-check

**Lovász/NC row (NOT_FORMALIZED.md:18).** The row now also lists "probabilistic NC algorithms
that find a perfect matching [KUW85, MVV87]" as cited research results. It points to the RP test
that the chapter proves, `Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM`, which
resolves. The row is accurate, and the exclusion is legitimate: the result is cited without
proof, and nothing in the chapter depends on it.

**PRIMES row (NOT_FORMALIZED.md:22).** The row now adds Rabin's (Miller–Rabin) test [Rab80]
alongside AKS. It points to `Randomized.PRIMESBin_mem_coRP_PTM`, which resolves. The row is
accurate.

**Last scan of the chapter notes (pp.140–141), citation by citation.**

| Citation | What the book says | Where it is covered |
|---|---|---|
| [dLMSS56], [Gil77] | Historical origin of the definitions | Historical; the definitions themselves are formalized |
| [Gil74] | The class PP | Listed |
| [SS77] | The Solovay–Strassen test | Proved: PRIMES ∈ coRP |
| [Rab80] | Rabin's primality test | Listed (new) |
| [AKS04] | PRIMES ∈ P | Listed |
| [Sho05], [MU05], [MR95] | Textbooks | Pointers only; nothing to formalize |
| [KR81] | Fingerprinting | Proved: `fingerprint`, `ZEROP_mem_coRP_PTM` |
| [Lov79], [KUW85, MVV87] | NC matching algorithms | Listed |
| [Adl78] | BPP ⊆ P/poly | Thm 7.14, proved |
| [Sip83] | BPP ⊆ PH | Implied by Thm 7.15, proved |
| Gács, [Lau83] | BPP ⊆ Σ₂ ∩ Π₂ and the proof the book presents | Thm 7.15, proved |
| [Can96, RS95] | BPP in classes weaker than Σ₂ ∩ Π₂ | Listed |
| [Bar02, FS04, GST04] | Hierarchy theorems for BPP/1 | Listed |
| (no citation) | Promise problems | Listed |
| [Koz06] | BP·P = BPP | Proved: `BPdot_P_eq_BPP_PTM` |
| Ch. 21 | Randomness-efficient error reduction | Listed |
| Ch. 21 | Logspace connectivity analysis | Proved via Ex 7.11 and `UPATH_mem_RL` |

No cited result in the chapter notes is left unlisted. Only `ch7/NOT_FORMALIZED.md` and this
file changed in the working tree. No Lean files changed, so the sorry and axiom checks above
still stand.

GRADE: COMPLETE
