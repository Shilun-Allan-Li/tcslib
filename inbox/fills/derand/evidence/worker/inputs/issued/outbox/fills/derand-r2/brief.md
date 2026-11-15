# Claude fill · pseudorandom generators derandomize `BPP` in subexponential time, with the seed-majority host (`derand`, issued-r2)

**Issue base** `01de2d8baed9113e4a099e13c5d50c81e6dbc66f` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305–#309, #311 and
#312; records-only commits since the #312 merge `8f0b34c9`). **Unit** `derand`. **Worker** Claude (standing ruling,
2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's `lake-manifest.json`.

This reissue replaces `issued-r1`, which was held (Seyoon, 2026-11-14) until the counting enumeration host was
statement-gated. That host is now **H17**: Gate 28 closed CLEAR in round 2, and #312 merged at
`8f0b34c9a5a52f57677f16243370dfed3f811ac4`. The r1 checkpoint "send the host's contract as a scope request" is gone,
because the contract is stated.

Prove three admitted, frozen statements:

| Target | File | Source |
|---|---|---|
| `Complexity.exists_seedMajorityTM` (the H17 machine contract) | `TCSlib/Complexity/Randomized/SeedMajority.lean` | [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4 of the proof] |
| `Complexity.seedMajority_mem_DTIME` (its `DTIME` corollary) | `TCSlib/Complexity/Randomized/SeedMajority.lean` | the same |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | `TCSlib/Cryptography/Randomness/Derandomization.lean` | [PS10, §8.2, Theorem 180.1] |

Theorem 180.1 passed the prong D statement phase (ruling D-6: stated against `main`'s `InBPP` and `DTIME`) and
Gate 06. The host and its corollary passed Gate 28 (round 1 HOLD, round 2 CLEAR). All three are frozen. Their
docstrings hold the maintainer's proof sketches.

## Feasibility (maintainer's assessment)

**Feasible, and dispatchable as a fill.** Codex checked the mathematics twice at Gate 28. The contract is true,
including ties, `w = 0`, `m = 0` and small `n`; the envelope follows from the time bound; and the contract is
sufficient for Theorem 180.1 by the full paper route below. The machine route is feasible: the published
`Turing.FinTM.exists_loopFindTM` accepts arbitrary numerical fuel, and its proof uses the proved private
`loopHost_contracts`, not the admitted `loopHostTM_*`/`timedCondTM_*` specifications. The three shared-file
additions the route needs are pre-approved (*Scope*).

**Estimated size:** 2,800–5,300 lines in all:
- checkpoint 1, 300–500: the generic-fuel harvest (its proof repeats the generalized assembly of
  `polyTimeComputable_find`, about 220 lines), the two readers and the corollary;
- checkpoint 2, 900–1,600: the host proof (the maintainer's estimate for H17; Codex found it plausible but not a
  verified size guarantee);
- the final, 1,600–3,200: the integer-root schedule and its unary word (200–400), the expanded generator and the
  piecewise test in `P` (300–600), the non-uniform-advice gap argument (600–1,200), the majority identification
  (200–400), and the asymptotic time bound and its transport (300–600).

The r1 estimate was 4,000–8,000 lines. It counted a host of 1,500–3,000 lines and a finite table of 500–1,000
lines; the piecewise test removes the table.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/derand` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/derand/` on `exchange/pass-shelat-ch5-8`. The
  issued pack is at `outbox/fills/derand-r2/`; the delivery path does not change. Deliver:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at the base
    reproduces every hash. **Commit with `git -c commit.gpgsign=false`** (prf-mac F-05: the last worker's hashes
    reproduced only with the environment's deterministic SSH signature). If a commit is signed anyway, say so in
    its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/derand/` except itself. The delivered
    paths must equal the manifest's paths exactly, with nothing missing and nothing extra. Check this before each
    push.
- Commit as `fill derand: checkpoint N` and `fill derand: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## Base and parallel work

- **Merged in the issue base:** #303, #305–#309, #311 (B1 statement) and #312 (this host). The lint baselines below
  are re-run at the issue base.
- **In flight, inside this order, not edited by this unit:**
  - `prf-long` (dispatched) owns `Pseudorandom/Functions/Asymptotic/Defs.lean`;
  - the `learning` landing changes `Randomness/Learning.lean` (its admission is still in `base-sorries.txt`);
  - the `prfAdv_eq_expect` promotion (ruling on prf-mac F-01) adds to `Pseudorandom/Functions/Defs.lean`;
  - `canonizer` (dispatched) adds a pre-approved `rfl` reader to `TuringMachine/CodeFormat.lean`.

  They are in the closure only as upstream modules (of the `Randomness` facade and of the machine library). Stay on
  the issue base if any of them merges during the fill; the maintainer rebases at landing.
- **Other fills** (`prf-mac` and `learning` in review, `prf-long`, `canonizer` and `sc-ot` dispatched, `seq-zk` and
  `sc-compose` staged) edit none of the files this unit owns or edits.

## Targets (frozen; quoted from the issue base)

```lean
open Classical in
theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ),
      M.DecidesInTime
          {x : List Bool | 2 ^ w x.length <
            2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
              pairEncode x (List.ofFn u) ∈ V).card}
          (fun n => c * (2 ^ w n * (n + 1) ^ e)) ∧
        ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  sorry
```

```lean
open Classical in
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry
```

```lean
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry
```

- **`exists_seedMajorityTM` and `seedMajority_mem_DTIME`** are in namespace `Complexity`, under `open Turing` and
  `open Classical in`. `Randomized.half_lt_randProb_iff` (same file, proved) is the reader
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A (List.ofFn r)}`.
- **`bpp_subset_dtime_subexp`** is in namespace `TCSlib.Cryptography.Randomness`, under
  `open Complexity TCSlib.Cryptography`. There are no section variables. It takes `hPRG : ∃ G : PRG, G.Secure`,
  `ε : ℝ` and `hε : 0 < ε`.
- **`BPP`** is `Randomized.InBPP Randomized.polyTimeModel` (`Complexity/Randomized/PolyTimeModel.lean`): a
  polynomial-time verifier with randomness `polyLen a k |x|` and error `1/3`.
- **`FinTM.DecidesInTime`** (line 75) and **`DTIME T`** (line 88) are defined in `TCSlib/Complexity/ClassP/DTIME.lean`:
  `L ∈ DTIME T` when a finite binary multi-tape machine decides `L` within `c · T(n)` for some `c`.
- **`subexpBound ε n = ⌈2^{n^ε}⌉₊`** (`subexpBound_eq`, `subexpBound_pos`, owned).
- **The registry row** is H17 in `machine-library-design.md` §14. The Gate 28 records are in
  `briefs/pass-shelat-ch5-8/gates/28-derand-host/`: both findings files and both resolutions. They are working
  material; the route below already carries their route notes.

## Published interfaces

| Interface | Provider |
|---|---|
| `half_lt_randProb_iff`, `randProb_eq` | `Complexity/Randomized/SeedMajority.lean`, `…/Classes.lean` |
| `subexpBound_eq`, `subexpBound_pos` | owned file |
| `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob` | `Cryptography/Randomness/BPPBridge.lean` |
| `PRG`, `PRG.secure_iff`, `PRG.easy_iff`, `prg_expand`, `PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible` | `Pseudorandom/Generators/Asymptotic/{Defs,Stretch}.lean` |
| `Randomized.InBPP`, `polyTimeModel`, `polyTimeModel_eff_iff` and their readers | `Complexity/Randomized/*` |
| `NUPPT.exists_withAdvice`, the `Negligible` readers | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `DTIME`, `DTIME.mono`, `FinTM.DecidesInTime` | `Complexity/ClassP/DTIME.lean` |
| `Randomized.DTIME_const_mul_subset` | `Complexity/Randomized/QuasiPolyHierarchy.lean` |
| `Turing.FinTM.exists_loopFindTM` (proved, from the private `loopHost_contracts`) | `Complexity/TuringMachine/Build/Loop.lean` |
| the clean-module host H14 (`ModuleHost.clean_install`, `clean_emit`, `host_call`, `host_clean`, `host_branch`, `host_halt`, `guard_add`, `request_budget`, `Clean.envelope`) | `Complexity/TuringMachine/Build/ModuleHost.lean` |
| `IterateFind.polyTimeComputable_find`, `step`, `step_eq`, `find?_congr_of_mem`, `find?_range_and_lt`; `hostTM`, `hostCtrl`, `hostRet`, `copyTM` | `Complexity/Randomized/Build/IterateFind{,Host}.lean` |
| `polyTimeComputable_unaryPoly`, `polyTimeComputable_pairTakePoly` | `Complexity/Randomized/Primitives.lean` |
| `FinTM.computesFunInTime_lengthBits`, `FinTM.computesFunInTime_comp` | `Complexity/TuringMachine/Build/Primitives.lean`, `Complexity/TuringMachine/Composition.lean` |
| `FinTM.computesInTime_iff`, `computesFunInTime_iff`, `not_computesInTime_zero`, `MultiTapeTM.workTapePos_runFrom_mem_Icc`, `MultiTapeTM.indicator_def` | `Complexity/TuringMachine/{Finite,Deterministic}.lean` |
| `Cfg.init_workTapePos` (generated by `simps`), `MultiTapeTM.runFrom_add`, `MultiTapeTM.runFrom_of_halt` | `Complexity/TuringMachine/{Configuration,Deterministic}.lean` |
| `BinArith.add`, `lt`, `beq` and their `polyTimeComputable_*` | `Complexity/ClassP/BinaryArith/AddSub.lean` |
| `mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `inter_mem_P`, `compl_mem_P`, `PolyTimeComputable.pairEncode`, `PolyTimeComputable.output_length_le` | `Complexity/ClassNP/{PClosure,CoNP,PolyTimePairing}.lean` and the `PolyTime` layer |
| `exists_proj_decider` (existential enumeration), `polyTimeComputable_blockMajorityTest` | `Complexity/ClassNP/{EXP,PolyTimeBlockMajority}.lean` |

## Scope

**Owned files** (you prove their targets and may add to them):

| File | Lines at base | What changes |
|---|---|---|
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 234 | the proofs of `exists_seedMajorityTM` and `seedMajority_mem_DTIME`; their *Status* and sketch paragraphs; the module title (drop "(statement phase)") and `## Main results`; imports of its helpers |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 97 | the proof of `bpp_subset_dtime_subexp`; its sketch, edited to describe the delivered proof (the finite table of step 3 is replaced by the piecewise test); the module title and `## Main results`; imports of its helpers |

**New helper modules** are permitted in two directories:
- `TCSlib/Complexity/Randomized/SeedMajority/`, imported by `SeedMajority.lean`, for the host proof. This is the
  shared layer: write it at host quality, generic in `V` and `w`, with public readers for every public `def`.
- `TCSlib/Cryptography/Randomness/Derandomization/`, imported by `Derandomization.lean`, for Theorem 180.1.

Each owned file imports its helpers precisely and gets a `## Contents` list. After the facade-lint fix (#305), a
helper under `X/` is covered as long as `X.lean` imports it, so no parent facade (`Randomized.lean`,
`Randomness.lean`) needs an edit. The Derandomization helpers may import `SeedMajority`, the machine library and the
complexity classes in the closure. Check the import graph for cycles (the order's modules include `SeedMajority`,
`IterateFind` and `ClassP/DTIME`, none of which imports `Derandomization`).

**Pre-approved scope exceptions (Seyoon, 2026-11-15): exactly these three.**

| # | File (frozen) | The one addition |
|---|---|---|
| E1 | `TCSlib/Complexity/Randomized/Build/IterateFind.lean` (556 lines) | one public generic-fuel `Complexity.IterateFind.computesFunInTime_find`, with its contract, harvested from the assembly of `polyTimeComputable_find`. It **reuses the private helpers in place** (`Inv`, `inv_*`, `verdictWord`, `stepWord`, `outWord` and their lemmas). |
| E2 | `TCSlib/Complexity/ClassP/DTIME.lean` (117 lines) | `Complexity.mem_DTIME_iff`, beside `DTIME`, by `Iff.rfl`, with a formula docstring and no attribute. |
| E3 | `TCSlib/Complexity/ClassP/DTIME.lean` | `Turing.FinTM.decidesInTime_iff`, beside `DecidesInTime` (inside `namespace Turing.FinTM`), by `Iff.rfl`, with a formula docstring and no attribute. |

Draft signatures for E2 and E3 (binding unless one clashes; disclose any change of binder style):

```lean
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔
      ∀ x : List Bool,
        M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length) :=
  Iff.rfl

theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl
```

For E1 the signature is yours: write it at checkpoint 1 and give it in full in `REPORT.md`. It must
- take an arbitrary numerical fuel `R : ℕ → ℕ` through a fuel machine for `x ↦ Nat.bits (R |x|)` within the common
  budget, as `exists_loopFindTM` does, and conclude a `FinTM.ComputesFunInTime` with the combinator's bound
  `c (T n + 1)(R n + 2)` for an explicit polynomial `T`;
- keep the length-guarded state and the invariant `Inv`, which is closed under the total step function
  (`hInvStep`), so that no fixed state bound is assumed after termination;
- be enough for the host. Note that the step `g` of `polyTimeComputable_find` sees only the second component of
  `⟨x, s⟩`; the seed-majority state must carry what it needs of `x`, or the harvested contract generalizes the start
  word and step. Either way it is **one** public declaration.

`polyTimeComputable_find` itself is **not** in the pre-approval: leave it, and `final_bound`, unchanged. E1's
proof will then repeat the generalized assembly of `polyTimeComputable_find` beside it; disclose that in
*Overlap and reuse*. Re-deriving `polyTimeComputable_find` from E1 (a proof-only change, header byte-identical,
`final_bound` kept as its polynomial-fuel normal form) would remove the repetition, but it is a change to a frozen
proof, so it needs a scope request; ask for it if you want it. Do not use `final_bound` for exponential fuel.

**The frozen-statement rule (binding; checked).**
- **Headers.** Every declaration present at the issue base in `SeedMajority.lean`, `Derandomization.lean`,
  `IterateFind.lean` and `ClassP/DTIME.lean` stays in the same file and the same order, with its header
  byte-identical. The header is the attributes and modifiers, the keyword, the name, the binders and the type, up to
  the `:=`, `by`, `where` or first `|` that begins the proof. `open … in` prefixes count as part of the header.
- **Definitions are statements.** A `def`, `abbrev`, `structure`, `inductive`, `class` or `instance` stays
  byte-identical, body included. Delete nothing, private lemmas included.
- **What may change.** Only the proofs of the three targets (and of `polyTimeComputable_find`, if a scope request
  approves it); the targets' sketch
  and *Status* paragraphs; module docstrings (title, `## Main results`, `## Contents`); and, within the scope above,
  added imports and declarations. Statement prose, `set_option`s and attributes do not change.
- **Check.** Write a `python3 -I` script that extracts every declaration of the four files at the base and at the
  final and compares headers (and whole definitions) byte for byte, and checks that the base declarations appear in
  the same order. Deliver it and its output under `evidence/headers/`, with zero differences. Add a control: a copy
  with one header altered by one character must report exactly one difference.

**Everything else is frozen.**
- `Games/Efficiency.lean` is at 982 lines. Do not add to it.
- **Scope requests.** If the route needs any other change to a frozen file (a reader beside a foreign definition, a
  second public declaration in `IterateFind.lean`, an import, a promotion), stop that line of work. Ask Seyoon in
  your session, giving the exact file, the diff and the reason, and go ahead only on his approval. Record the
  request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon
  prefers a route with no frozen-file edit where one exists.
- A lemma that belongs in an existing file goes in your helper module, with a promotion request.

## Proof route and checkpoints

1. **Checkpoint 1 · the harvest, both readers and the corollary.**
   - E1, E2 and E3 as in *Scope*.
   - Prove `seedMajority_mem_DTIME` from the contract: take `M, c, e` from `exists_seedMajorityTM` (the envelope is
     not needed), and conclude with `mem_DTIME_iff` and the witnesses `⟨c, M, hM⟩` and `e`. Its proof must not read
     `DecidesInTime`, `DecidesInTimeVia` or `DTIME` by definition (Gate 28: the round-2 maintainer proof did, and
     was reverted). After this checkpoint the corollary is proved modulo the contract.
   - Rebuild the order's modules downstream of `IterateFind` and `ClassP/DTIME` (see *Checks*). Send this
     checkpoint.
2. **Checkpoint 2 · the host contract `exists_seedMajorityTM`.** Follow the route of `SeedMajority.lean`'s module
   docstring, steps 1–5, with Codex's Gate 28 route notes:
   - **State loop.** The state word is `⟨x, ⟨i, a⟩⟩` from `⟨x, ⟨0, 0⟩⟩`: the binary rank `i` and the binary
     acceptance count `a`. A step tests `⟨x, word_w(i)⟩ ∈ V` (`word_w(i)` the width-`w(|x|)` binary word of `i`),
     adds the verdict to `a` and increments `i`. The loop stops at `i = 2^{w(|x|)}` with the payload
     `[decide (2^w < 2a)]`. Both counters need at most `w(n) + 1` bits, including the terminal value `R`.
   - **Terminal-step invariant.** The invariant must be closed under the **total** step function (`hInvStep`).
     Make the terminal state fixed, or keep the existing size guard. Never assume that an unbounded increment
     preserves a fixed state bound after termination. With `a_i` the count after `i` tests,
     `a_0 = 0`, `a_{i+1} = a_i + [pairEncode(x, word_w(i)) ∈ V]` for `i < R`, and by induction
     `a_i = #{j < i | pairEncode(x, word_w(j)) ∈ V}` and `0 ≤ a_i ≤ i ≤ R`.
   - **Binary fuel.** The fuel is `Nat.bits (2^{w(|x|)})`, of length `w(n) + 1` (`w(|x|)` zeros, then a one), from
     the unary width; never an exponential-length unary word. `exists_loopFindTM` searches
     `List.range (R(n) + 1)`, so it includes the terminal rank `R(n)` and allows `R(n)` seed tests followed by the
     payload round.
   - **Count.** At `i = R`, the fixed-width binary expansion is a bijection from the ranks `[0, 2^w)` onto
     `Fin (w n) → Bool`, so `a_R` is the contract's `Finset` count. The verdict is the strict `R < 2 a_R`; ties
     reject. At `w(n) = 0` there is one empty seed, and `1 < 2 · count` accepts exactly when it passes.
   - **Direct time bound, not `final_bound`.** `final_bound` is the polynomial-fuel normal form and cannot be
     applied to exponential `R`. Use instead, for fixed `A, e` with `T(n) + 1 ≤ A (n+1)^e`:
     `R + 2 ≤ 3R` and `c₀ (T(n) + 1)(R + 2) ≤ 3 c₀ A · 2^{w(n)} (n+1)^e`. The state words have length at most
     `2n + 3w(n) + 7`, and `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le` on the unary width), so the
     per-round budget `T` is polynomial. At `n = 0` the factor `(n+1)^e` is `1` and the constant pays for the
     initialization.
   - **Envelope.** Fix `x`, a work tape `j`, `b = B(|x|)`, and `p(v)` the head position after `v` steps from
     `M.tm.initCfg x`. Then `p(0) = 0` (`Cfg.init_workTapePos`), `−v ≤ p(v) ≤ v`
     (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), the run is halted at time `b` (the decision bound, read through
     `decidesInTime_iff` and `computesInTime_iff`), and for `b ≤ v` the run is constant (`runFrom_add`,
     `runFrom_of_halt`). So `|p(v)| ≤ min(v, b) ≤ b`, for the same machine and constants. If
     `ModuleHost.Clean.envelope` fits, reuse it rather than restating it.
   - Do not use the admitted `loopHostTM_*`, `timedCondTM_*` or `RecordTable` `exists_*TM` specifications
     (`base-sorries.txt`). Send this checkpoint.
3. **Final · Theorem 180.1.** The paper route, as checked at Gate 28 (rounds 1 and 2), keeping r1's PRG and advice
   steps:
   - **Setup.** From `InBPP polyTimeModel L`, take the Boolean verifier `M` and, by `polyTimeModel_eff_iff`, its
     accepting paired language `V₁ ∈ P`, with coin width `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2` with
     `1/d < min(ε, 1)`, and the integer-root schedule `ℓ(n) = min{t | n ≤ t^d}`. Then `ℓ(0) = 0`, `n ≤ ℓ(n)^d`
     and `ℓ(n) ≤ n^{1/d} + 1`; for `n ≥ 1` a search over `t ≤ n` computes its unary word in polynomial time. No
     real exponent is computed by a machine.
   - **Expand the generator.** Expand to the syntactic polynomial `P(s) = a(s^d + 1)^k + s + 1`, by one-bit
     truncation and `prg_expand` (`PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible`), and take its
     evaluator `F'` through `PRG.easy_iff`. Check `P(s) > s` and `m(n) ≤ P(ℓ(n))` at every length, including `0`.
   - **The gap (non-uniform advice).** Suppose the acceptance-probability gap
     `|Pr_u[M(x; F'(u)↾m(|x|))] − Pr_r[M(x; r)]|` exceeds `1/12` at infinitely many input lengths. Since
     `ℓ(n) = s` implies `n ≤ s^d`, each seed length has finitely many input lengths, so infinitely many seed lengths
     are bad. Choose one bad input `x_s` for each such `s` (empty advice otherwise); its length is at most `s^d`.
     The test `y ↦ M(x_s; y↾m(|x_s|))` is polynomial-time with this advice (`NUPPT.exists_withAdvice`,
     `verifier_toNUPPT` on the prefix-truncated verifier, `polyTimeComputable_pairTakePoly`). Uniform prefix
     projection and `randProb_eq_uprob` identify its advantage with the bad gap. By `PRG.secure_iff` the advantage
     is negligible, a contradiction (already the inverse-linear bound fails for large `s`). Hence a threshold
     `n₀` exists. A threshold from classical existence is harmless: the theorem asks for a decider, not a uniform
     procedure.
   - **The piecewise test and width, together.** Changing the width alone would not remove the generator, and PRG
     security says nothing about finitely many seed lengths:
     `w(n) = m(n)` for `n < n₀` and `ℓ(n)` for `n ≥ n₀`;
     `V''(⟨x, u⟩) = V₁(⟨x, u⟩)` for `|x| < n₀` and `V₁(⟨x, F'(u)↾m(|x|)⟩)` for `|x| ≥ n₀`.
     Both are polynomial-time: hard-code `n₀`, and use the integer-root search, pairing, prefix truncation and the
     `P` closure lemmas. Extend the test to raw words by the total pairing projections; its behaviour on malformed
     words is irrelevant.
   - **Majority identification.** Below `n₀` the coins are true: acceptance is at least `2/3` on members and at most
     `1/3` on non-members. From `n₀` on the bounds are `2/3 − 1/12 = 7/12 > 1/2` and `1/3 + 1/12 = 5/12 < 1/2`.
     `half_lt_randProb_iff` turns this into the count, so `L` is exactly the strict-majority language of
     `(V'', w)`. No finite table is needed.
   - **Apply the host.** `seedMajority_mem_DTIME` gives `e` with `L ∈ DTIME (n ↦ 2^{w(n)} (n+1)^e)`.
   - **Time.** Eventually `w(n) = ℓ(n) ≤ n^{1/d} + 1` and
     `log₂(2^{w(n)} (n+1)^e) ≤ n^{1/d} + 1 + e log₂(n+1) ≤ n^ε`, because `1/d < ε`. Rounding up preserves the
     bound. Since `subexpBound ε n ≥ 1` at every length, one natural constant absorbs the finitely many exceptions:
     `∀ n, 2^{w(n)} (n+1)^e ≤ C · subexpBound ε n`. Finish with `DTIME.mono` and
     `Randomized.DTIME_const_mul_subset`. The maintainer's `probes/ConsumerProbe.lean` (in
     `briefs/pass-shelat-ch5-8/maintainer/stmt-derand-2026-11-15/stmt-derand-evidence.zip`) checks only this last
     transport, through readers.

**Proved-modulo rule** (`policy.md` §1, *Hosts come first*). The Theorem 180.1 proof may consume the host
contract, through `seedMajority_mem_DTIME`, while the host proof (checkpoint 2) is still in progress; you may work
on the final route before checkpoint 2 is done. The final payload's aim is all three targets with the standard
axioms. If the host proof is not finished, a final in which `exists_seedMajorityTM` alone keeps its `sorry` is
allowed: Theorem 180.1 and the corollary are then reported **proved modulo the host contract**, and the axiom
evidence must show that every `sorryAx` reaches them only through `exists_seedMajorityTM`.

Check the edge cases: ties (the host rejects them; the `1/12` margin keeps the probabilities off `1/2`); `w(n) = 0`;
`m = 0` coins; `n = 0` and small `n` (the piecewise test, not a table); `ε ≥ 1` (`d = 2` works); `d` with
`1/d < min(ε, 1)`; seed lengths shared by many input lengths; the expanded generator's envelope at `s = ℓ(n)`; the
terminal rank `R` in the search range; a witness `c = 0` (impossible, `FinTM.not_computesInTime_zero`).

If a sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a checkpoint with
the counterexample or the missing fact. Do not weaken any statement.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  `IterateFind.lean` is at 556; keep it under 1000. Check both with a short `python3 -I` script before each push
  and include its output in `evidence/`.
- **Parallel fills.** See *Base and parallel work*. Edit only the files of *Scope*.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Probability and expectation identities first (prf-mac and learning reviews).** Both units re-proved public
    lemmas: prf-mac re-proved `ETTGame.prfAdv_eq_expect` (F-01, a major), and learning restated
    `OneWay.uprob_eq_one_div_card` and re-proved `MultiMsg.abs_uexp_sub_le_uprob`. Before writing any
    advantage, expectation, uniform-projection or probability-point lemma (the gap step needs uniform prefix
    projection), search for `prfAdv_eq_expect`, `prgAdv_*`, `uexp_*`, `uprob_*` (`uprob_comp_equiv`,
    `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`), `HardcoreBit.pushesUniform_restrict`, `randProb_eq`,
    `randProb_eq_uprob` and `abs_uexp_sub_le_uprob`.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it. E1 is how the `IterateFind` helpers are reused without copying.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration that
    restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its nearest
    relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24 were
    undisclosed duplicates (G23-01, a private copy of `length_le_length_encodeLog`; G24-01, `inputWord_take`, which
    re-proves the public `take_ofFn_castLE`), and so was prf-mac F-01.
  - **Nearest relatives here:**
    - the existential projection decider `Complexity.exists_proj_decider` and its private engine
      `enumMachine_contracts` (`ClassNP/EXP.lean`), `NP_subset_EXP`;
    - `IterateFind.polyTimeComputable_find` and its private helpers (reused through E1), `IterateFindHost`;
    - H16 (one round per counter letter) and `counterLoopTM`; the block-majority tests
      (`ClassNP/PolyTimeBlock*.lean`) and `BPPAmplify`;
    - `ModuleHost.Clean.envelope` for the envelope argument;
    - for ranks and binary words: Mathlib's `Nat.bits`, `Nat.testBit`, `finFunctionFinEquiv`, and
      `Complexity.BinArith`;
    - for the integer root: Mathlib's `Nat.sqrt` family and any `nthRoot`, and the TCSlib unary searches;
    - `Randomized.mem_EXP_of_inBPP_polyTimeModel` (`Randomized/Inclusions.lean`, via Sipser–Gács).
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches; learning: 17 formulas; prf-mac: two
  docstrings) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a source tag where it comes from the source (`[PS10, §8.2, Theorem 180.1]`,
    `[AB09, §7.1, p. 126]`, `[AB09, Definition 1.12]`);
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public `abbrev`
    with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections: for
    example `DTIME` only through `mem_DTIME_iff`, `DecidesInTime` only through `decidesInTime_iff`, `ComputesInTime`
    and `ComputesFunInTime` through `computesInTime_iff` and `computesFunInTime_iff`, `indicator` through
    `indicator_def`, `randProb` through `randProb_eq`, `P` through its readers.
  - E2 and E3 are proved by `Iff.rfl` inside the definitions' own file, which is allowed. E1 may read the private
    helpers of its own file.
  - Your helper modules count as foreign to each other and to the owned files, and the owned files are foreign to
    each other and to the helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (377 modules) and the narrow `roots.txt` (129), following the addendum.
  - The order is the upstream closure of the modules downstream of `SeedMajority` and `Derandomization` (root
    `TCSlib` excluded), and of `IterateFind` and `ClassP/DTIME`. It contains every module between `ClassP/DTIME`
    or `IterateFind` and the two owned files, so a sweep in order rebuilds each of them after your edits.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the four edited files and every helper, then sweep the supplied order with 0 errors.
  - The full downstream sets of the shared files are larger than this order: `ClassP/DTIME` has
    480 downstream modules and `IterateFind` 222 (the union's upstream closure is 972 modules). You do
    not sweep the ones outside the order; the maintainer rebuilds them at review (decision log, 2026-11-15). Instead,
    run a name-clash scan: no new public or private name of E1–E3 may already be declared anywhere in `TCSlib/` at
    the issue base (text-level, with namespaces resolved). Deliver the script and its output under
    `evidence/clash/`.
  - Compare the `sorry` warnings with `base-sorries.txt` (26 declarations in 12 modules). The only change
    must be the removal of `exists_seedMajorityTM`, `seedMajority_mem_DTIME` and `bpp_subset_dtime_subexp`
    (23 in 10 modules), or, for a final under the proved-modulo rule, of the last two only.
- **Axioms.**
  - Print the axioms of the three targets, of E1–E3 and of `polyTimeComputable_find`. Expect only
    `propext`, `Classical.choice` and `Quot.sound` (see the proved-modulo rule for the one allowed exception).
  - Print them for every stored constant of the changed and new files.
  - Also print, at base and final, the axioms of `polyTimeComputable_iterateFind` (`Randomized/Repetition.lean`),
    the main downstream consumer of `polyTimeComputable_find`. They must be identical.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation). Report
    every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for example
    with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` and
    `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity --check8b`, at base and at final.
  - The baselines at the issue base are **92 FAIL / 101 WARN** (Cryptography) and **25 FAIL / 391 WARN** (Complexity), re-run by the
    maintainer at `01de2d8b`.
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
  - `ClassP/DTIME.lean` carries one check-8 WARN line at base (`DecidesInTime` without a lemma beside it); E3 should
    remove it. Disclose that change.
- **Report.** `REPORT.md` gives:
  - the base, and the status of each target (proved, or proved modulo the host contract);
  - the changed and new files, with lines at base and final, and the sketch edits;
  - the new declarations with their final signatures, E1 in full;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control, and the name-clash scan;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, including the
downstream modules of `ClassP/DTIME` and `IterateFind`.

**Ready to dispatch**
