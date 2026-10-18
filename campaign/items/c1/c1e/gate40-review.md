# Gate 40 review: PR #121 round 2, C1-E's statements (`Diagonalization/NTimeDiagonalizer`) (PASS 0/0/1/12)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$Z = $S/review/ntime-diag-r2-gate`.
Every claim cites a saved output under `$Z/out/`.

**The PASS stands: 0 blockers, 0 majors.** Every finding is true at its stated severity. Minor 1's
scope is incomplete: the same superseded route is also in `ntime_hierarchy`'s proof sketch
(`NTimeHierarchy.lean`), which the auditor did not flag (X1 below). The review also found one
route problem for E-D's fill: an import cycle (X2). Neither affects #121's statements.

**#121 (`lean/ntime-diag` at `0a5878ed`): clear to merge** once gate 40's records are committed.
The replay passed (2 of 2, static-equal), the gate is PASS 0/0, and no statement changes.

**Decide X2 (the import topology) before pressing merge.** One of its three options adds a
hypothesis to `exists_diagonalizer`, which would need round 3 of this gate. The other two options
leave #121 untouched.

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Findings | `audits/ntime-diag-statements-r2-findings.md`, SHA-256 `331946f9…7a92`, read as data. Already committed verbatim on the campaign branch at `5de427ed` (the only change since `3888565f`) | `out/bundle-rebuild.txt` |
| Bundle | `infra_local/gate-dispatches/40-…/ntime-diag-statements-r2-bundle.md`, SHA-256 `3e2b3694…32ef`, 576,576 bytes, 55 sections | `out/bundle-rebuild.txt` |
| Lean head | `0a5878edaf7c417839d9d3e61266956ce260749c`. Parent `2738e9da`, which merges `13f52659` (round 1) with `2cce4804` | `out/blobs.txt` |
| Records | campaign `3888565f` (the bundle's source); tip `5de427ed` | — |
| #122 | `lean/nd-api-r2` at `423b6536`, a descendant of `0a5878ed`. `NDCodeSimulator.lean` (`544a6775`) and `NTimeHierarchy.lean` (`cbb0cef8`) are the same blobs as at `0a5878ed` | `out/blobs.txt`, `out/edit-blobs.txt` |
| Elaboration | `tools/leanelab.sh $S/wt-ndiag $S/oleans-lndiag2 <file>`, 4 runs, one at a time | `out/elab-*.out` |

**Task 1, the bundle: verified.** I rebuilt the bundle independently from git (`scripts/rebuild.py`:
the Lean files from `0a5878ed`, everything else from `3888565f`, in `BUNDLE-FILES.txt` order). The
rebuild is **byte-identical**: the same SHA-256, 55 headers in order, and `SHA256SUMS` OK. The
findings were made against this bundle. Row 2 quotes its exact SHA-256 and the 55 sections. Its
blob claims also hold: `29eaf793` → `3f67d257`, facade `43b82304`, `Diagonal.lean` `e8087e57`, and
patch `634320d7…`.

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | **minor, scope incomplete** | Each passage it names is stale at the cited place (b). It misses `ntime_hierarchy`'s sketch (X1), C1's design §0 item 5, and D8's `∃ s` |
| 2 | note | true | note | Head diff `13f52659..0a5878ed` equals the review patch line for line. Freeze: 20 → 22, `STATEMENT CHANGED` none. `exists_diagonalizer` from `theorem` to `sorry` is byte-identical, so the freeze tool's flag is the docstring. 13f52659 is an ancestor of the head (`out/freeze.txt`, `out/blobs.txt`) |
| 3 | note | true (checked) | note | Read at `NTimeDiagonalizer.lean:75–233`. `^` is right-associative, so `2 ^ budget ^ 2` = `2^{T*²}`. `Nat.bits` is little-endian, so `dropLast` removes the top bit. For `α = []`, `m = 1`. The `n ≤ 2` and off-guard cases are proved |
| 4 | note | true (checked) | note | R (`NDCodeSimulator.lean:128–145`): `t ≤ s.length` (131); the verdict along `s.take t` (141–142); first verdict (143–144). `AcceptsWithin` (`NTIME.lean:96`) is a word of length exactly `t`, so `s.take b` with `b ≤ g n = |s|` witnesses acceptance within `b`. `AcceptsWithin.mono` (`NTIME.lean:118`) lifts it to `g n`. The clock's `stopAt` must be R's two verdicts |
| 5 | note | true (checked) | note | `C ≥ 1` gives `t' ≤ g n`, so the word pads to length `g n` and `b = t'` fits the width of `bits (g n)`. R's total-time clause (140) gives `T ≤ C_R(t'+1) ≤ g n = d`. The clock's finish clause allows `τ ≤ d` (`StepClock.lean:1077`). No `|x|` term is used |
| 6 | note | true (checked) | note | R's input is `pairEncode (pairEncode (Nat.bits t) α) x` (132), so canonical `bits b` is required. Bits are little-endian, so normalization strips trailing `false`s; all-false gives `[]`. The rewrite is linear in the word, `O(n + \|α\| + \|bits (g n)\|) ⊆ O(g n + 1)` |
| 7 | note | true (checked) | note | `exists_stepClockTMVia` (`StepClock.lean:1068–1108`): finish within `5τ + 2\|w\| + 2` for `τ ≤ d`, timeout within `5d + 2\|w\| + 2`. With `\|bits d\| ≤ d + 1` the cost is `≤ 7d + 4 ≤ 7(d + 1)`. The host's output always equals the body's at some earlier time (1094–1095), which is why provisional output must be suppressed |
| 8 | note | true (checked) | note | Agrees with the P3.3 r2 locator ledger and the round-1 review. A timeout at `c_f(n+1)` means `f a > n`, hence `ℓᵢ₊₁ > n`. `n ≤ g n` comes from `TimeConstructible` |
| 9 | note | true (read; arithmetic checked) | note | `T* ≥ 2C` gives `C·2^{C(T*+1)} ≤ 2^{C(T*+2)} ≤ 2^{T*²}`. The chain's middle bound is the one I wrote out for X1 |
| 10 | note | true (checked) | note | `g n = 4`: `bits 4 = [f,f,t]`, so the width-3 word 7 exceeds 4 and is rejected before R runs. `b = 0` gives the initial configuration, which is live (R brief's M4 edge case). Premature `[true]`: acceptance needs `state = none` |
| 11 | note | true (checked) | note | R's statement is unchanged (blob `544a6775` at both heads). The clause is an extra conjunct under `∃ T`: it strengthens R and cannot make it vacuous, and the C1 hosts gate passed it as achievable. For what R's brief should say, see (c) |
| 12 | note | true | note | Screen: the records' `pr/r2/screen-head.txt` equals the round-1 review's `screen-r2.txt`. Base vs r2 has identical pair lines, 48 → 49, 1,814 characters. **Lint, 5 files at the head: 0 FAIL, 1 WARN (`EXPCOM`)**, reproduced here (`out/lint-head.txt`). The auditor could check only 2 files |
| 13 | note | true | note | Records' `replay-lndiag2.log` and `-static.txt` equal `$S/fills/replay/` copies (SHA-256). The probe shows 2 sorry warnings at lines 270 and 327, which are the two contracts, and standard axioms (`out/evidence-identity.txt`) |

**Reviewer additions** (not in the findings):

- **X1 (minor; extends minor 1): `ntime_hierarchy`'s sketch describes the superseded route.**
  - **Where:** `NTimeHierarchy.lean:244–264, 274–282, 290–291` at `0a5878ed` and at #122's head.
  - **What it says:** `D` runs R "at nominal simulated budget `g n`" under a countdown of
    `K·(g n + 1)` steps, with "the **prefix-bound obligation** … a clause of the core's contract".
    The chain says "by the core's prefix clause the genuine simulation … costs at most
    `C_α·(… + (n + 1) + |bits (g n)| + 1)`".
  - **The route is still valid at the theorem level.** `hfg` gives `A·(n + 1) ≤ g n` eventually
    for every `A`, so the `|x|` term is absorbed there. It fails only for the contract
    `exists_diagonalizer`, which holds for every `g`.
  - **It is still stale, and it matters for H.** It is the superseded route and a second textual
    consumer of the prefix clause. The round-1 review and the resolutions (line 28: "D's old
    sketch was its only one") missed it. Under the briefs' convention it is binding on H's
    worker.
  - **Edit:** drafted in (b), line-count-preserving.
- **X2 (route; a decision is needed before E-D's brief): an import cycle.** `out/import-topology.txt`
  has the evidence.
  - **The cycle:**
    - `exists_diagonalizer`'s sketch (`NTimeDiagonalizer.lean:300`) and C1-E's design (line 71:
      "E-D … citing E-Q, W, R, BF") have E-D cite BF, `Turing.exists_ndAcceptsWithin_decider`.
      BF is stated in `NTimeHierarchy.lean:190`, as UN's brief's target 2.
    - C1-E's design deviation 3 (lines 52–53) says "`ntime_hierarchy`'s fill adds the import
      later", meaning `NTimeHierarchy` will import `NTimeDiagonalizer`.
    - So E-D's file would have to import `NTimeHierarchy`, and H's file would have to import
      `NTimeDiagonalizer`. Both imports cannot coexist.
  - **No route around it:**
    - BF's derivation `ndAcceptsWithin_decider_of_universal` (`ExhaustiveReplay.lean:79`) is
      upstream, but it needs UN's statement, which is also in `NTimeHierarchy`.
    - Rebuilding a UN inside E-D would break the one-proof-per-shared-argument rule.
  - **Options:**
    - **(i) Re-home UN's and BF's statements upstream**, in a new module (the NF precedent:
      verbatim under their own names, with `NTimeHierarchy` keeping one-line citations). This is
      a statement-move PR with a small gate. UN's in-flight delivery is re-homed at integration.
    - **(ii) Re-home H, H′ and S downstream** of `NTimeDiagonalizer`. That removes statements from
      `NTimeHierarchy`, and H′ and S are UN's brief targets, so it is the most disruptive.
    - **(iii) Add BF's statement as a hypothesis of `exists_diagonalizer`** (the
      `ndAcceptsWithin_decider_of_universal (hUN)` pattern). H then calls
      `exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)`. There is no import
      change, and wave 1 is untouched. It is a statement change to #121: round 3 of this gate if
      made before the merge, or a statement PR and gate after it.
  - **My recommendation: (iii).** It is the smallest and leaves wave 1 alone. If #121 is to
    merge now, (iii) becomes a follow-up statement PR before E-D's brief. Merging does not
    foreclose any option.
- **X3 (note):** two docstrings in #121's own file still describe the middle query word as R's
  input: `NTimeDiagonalizer.lean:32` ("the interpreter's input") and `:197` ("hands to its
  simulators"). D now rewrites the budget field first; `exists_diagonalizer`'s sketch is explicit,
  so nothing is misleading at the statement level. Optional one-line replacements (≤ 100
  characters) for the E-D integration window, lines 32 and 197 in that order:
  ```
    - In the middle it is the flag `false` and `⟨⟨bits (g n), α⟩, 1^{n+1}⟩`; `D` rewrites its budget.
  /-- **The stage query** on an input `x`: the word the diagonalizer builds its rungs from. On a
  ```

## (b) Minor 1's exact edits

The script is `scripts/edits.py`. Every replacement is asserted unique, and every new line is at
most 100 characters, except two Markdown table rows, which must be single lines like every row of
their table. The patches use repository paths and each applies cleanly (`applytest/`). SHA-256 in
`out/patch-hashes.txt`.

### Records: `audits/evidence/c1/C1-design.md` (campaign branch; `records-C1-design.patch`, `dee3383f` → `9b511a56`)

| # | Where (base `5de427ed`) | Stale text | Replacement |
|---|---|---|---|
| R-1 | §0 item 5, line 50 (reviewer addition) | the item presents the prefix clause as discharging the gate's obligation | append to line 50: ``. **Superseded for `D`** (gate 39, finding 1): its mid-rung`` / ``guesses a nominal budget and uses R's total-time clause instead (§3.6). The clause stays in`` / ``R's statement with no consumer (the user, 2026-10-17).`` (new lines 50–52) |
| R-2 | §1.2, lines 164–165 (auditor's §1.2) | "the prefix bound is a clause of the interpreter-core contract, so the sketch's obligation is discharged by the contract" | new lines 166–169, quoted below |
| R-3 | §2.1, lines 202–205 (auditor's §2.1) | D's diagram sends `⟨⟨bits g n, αⱼ⟩, …⟩` straight to R | new lines 206–213, quoted below |
| R-4 | §2.5 D6, line 271 (auditor's §2.5) | "under the step-clocked runner at `K'(g n + 1)`" | the D6 row below |
| R-5 | §2.5 D8, line 273 (reviewer addition) | "(mid: `∃ s`, the clocked `R` accepts;" | "(mid: `∃ s` and `b ≤ g n`, the clocked `R` on `bits b` accepts;" |

R-2:
```
- **Item 4(iii):** the sketch's prefix-bound obligation is met by a guessed nominal budget, not by
  the core's prefix clause (gate 39, finding 1): the mid-rung guesses `b ≤ g n`, and at `b = t'`
  R's total-time clause gives `C·(t' + 1)`. The prefix clause's `|x|` term cannot be absorbed into
  D's uniform `K`; the clause stays in R's statement with no consumer (the user, 2026-10-17).
```
R-3:
```
D   (the diagonalizer of ntime_hierarchy, Turing.NTimeDiag.exists_diagonalizer), an NDTM:
    query: exists_queryTM's machine (unary check, locator, bits (g n), the query word)
    ─▶ bits (g n) by g's witness ─▶ GUESS g n stream bits s
    ─▶ mid:  GUESS a budget b of the width of bits (g n), reject unless b ≤ g n, normalize to bits b
             ─▶ clock( Z1( R on ⟨⟨bits b, αⱼ⟩, 1^{n+1}⟩ with s ) ), accept iff R accepts in time
    ─▶ top:  clock( vhostSilent( BF on ⟨⟨bits T*, αⱼ⟩, 1^a⟩ ) ), accept iff BF outputs [false]
    ─▶ default reject. clock: the step-clocked runner, body allowance g n (counter bits (g n)),
       physical cost at most 7(g n + 1); one uniform K bounds every branch (gate 39, findings 1-2)
```
R-4 (one table row):
```
| D6. Mid-rung: guess a nominal budget `b` of the width of `bits (g n)`, reject unless `b ≤ g n`, and normalize it to `bits b`; run `R` (§3.6) hosted by Z1 on the materialized word with its budget field rewritten to `bits b` (gate 39, finding 1), with the guessed stream, under the step-clocked runner with the body allowance `g n` (its counter `bits (g n)`; physical cost at most `7(g n + 1)`, gate 39, finding 2) | Z1 [pub]; the step-clocked runner [missing]; `R` [missing]; the budget's guess, test, normalization and rewrite (a private leaf of E-D) [missing] | |
```
- **Left as is, on purpose:**
  - §1.1 row 4 (line 87) and §1.2 lines 145–150 record what the P3.3 gate's sketch and
    resolutions said, as history;
  - §3.6 (lines 484–488) was already corrected;
  - §5 C1-C's "prefix ledger" and Appendix A row 7 are R's own still-binding obligations.
- **Unrelated stale text, not minor 1's subject:** the 2-adic schedule `ν₂(i + 1)` (lines 171,
  269, 274) was superseded by `Nat.unpair` (C1-E's design, deviation 2). Optional.
- **Also, by memory rule:** the resolutions need a "Round 2 result" entry. It should correct line
  28's "D's old sketch was its only one" to name X1.

### `.lean` docstrings (a PR; the plan is #122)

**L-1, `TuringMachine/NDCodeSimulator.lean:36–39`** (the module Design bullet; the auditor's
item; `lean-ndcodesim-docstring.patch`, blob `544a6775` → `2d41f8f4`):
```
* **The interpreter core** `Turing.exists_ndInterpreterCore` is deterministic: the stream of
  choices is on a tape before it starts (guess first, user decision 1). Its prefix clause (time in
  the simulated branch's halting time) is kept with no consumer (user, 2026-10-17): the universal
  and the diagonalizer's mid-rung, at a guessed budget, use the total-time clause `C·(t + 1)`.
```
Lines 97 ("shared by the universal NDTM and the diagonalizer's mid-rung") and 107–109 and 123–124
(the clause itself and its ledger) stay as they are: they are still true.

**L-2, `Diagonalization/NTimeHierarchy.lean:244–264, 274–282, 290–291`** (X1;
`lean-ntimehierarchy-docstring.patch`, `cbb0cef8` → `a32bedba`):
- (iii) states the two guesses, the body allowance `g n`, the uniform `K`, and the total-time
  clause. It also says why the prefix clause is unused.
- The chain uses `b = t'` and `A* := C_α·(C₁·c₀ + C₁ + 1)`:
  `C_α(t' + 1) ≤ C_α(C₁c₀ + C₁ + 1)(f(n+1) + 1)`.
- The top compares against `n ≤ g n` instead of `K·(g n + 1)`.

The full text is in the patch (60 changed lines).

**Neither edit changes a declaration:**

| Check | Result |
|---|---|
| Line counts | 147 → 147 and 342 → 342, so every line number in R's and UN's briefs still holds |
| Freeze | NDCodeSimulator 3 → 3 publics, no flag. NTimeHierarchy 5 → 5 publics; the only flag is `ntime_hierarchy`'s docstring, and its `theorem … sorry` text is byte-identical (`out/freeze-*-edit.txt`) |
| Comment delimiters | none added |
| Elaboration (`oleans-lndiag2`) | orig and new give identical output: NDCodeSimulator exit 0, 2 sorry warnings at 91 and 128; NTimeHierarchy exit 0, 5 at 162, 190, 299, 313, 338 (`out/elab-*.out`) |
| R's delivered partial patch | still applies on top of L-1 (`out/r-partial-applies.txt`) |
| UN's regions | 111–198 and 304–340. L-2's hunks, with their context, cover 242–294, so a 3-way merge with UN's delivery is clean |

**For #122 if both edits go in:**
- `replay-lndapi2.sh` has not run yet. Its precheck requires the Lean diff from `0a5878ed` to be
  "exactly the seven files", and it pins seven blobs.
- Add two pins, provided the committed bytes equal `edit/new/`:
  `TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:2d41f8f42288904b84f6e3e869e04ba0b977caea`
  and `TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:a32bedba68164407adc1d03d8da2dc5bf07ee7ef`.
- Change "seven" to "nine" in the precheck, its message and the header comment.
- The 256-module list is unchanged: both modules' downstream closures (2 modules each) are
  already in it (`out/ndcodesim-closure.txt`, `out/edit-blobs.txt`).
- Name both docstrings in #122's gate pack, since that gate audits them.
- If you prefer to keep #122 narrow, take L-1 alone. L-2 is then H's brief's job (c).

## (c) Carry-forward

**R's continuation brief (note 11).** Keep the gate guidance at brief lines 184–187 ("a coarser
bound that loses the prefix clause is a statement failure"), and add:
1. **Status of the clause.** After gates 39 and 40 it has **no consumer**: UN and D's mid-rung
   both use the total-time clause. The user kept it on 2026-10-17. It is still part of the frozen
   target. A proof of the total-time clause alone is a partial, not a delivery. Dropping or
   weakening the clause is a statement change (a PR and a regate of R, undoing the C1 hosts
   gate's M4). The worker escalates (ground rule 4); it never drops the clause.
2. **Correct line 63–64:** both consumers read the total-time clause.
3. **The ledger it needs.** One `C` covers both clauses (line 177):
   - the loop's early-escape bound at the **first** halt `u ≤ t'`, since halting absorbs (the
     clause quantifies over every `t' ≤ t` with a halted branch);
   - the window copy's `O(min(t, |x|) + |bits t|)`, which is where the `|x|` term comes from,
     because the window is copied before the loop whatever the halting time;
   - the two prefix passes, `16|bits t| + 8|α| + 25` each (C1-R review);
   - the saved copy of `bits t`; the verdict.
4. **Edge case:** `t' = 0` is vacuous (the initial configuration is live; M4).
5. **For a partial:** the prefix clause is phase 4's last item, reported with a literal
   "Proof sketch".
6. **The module Design bullet** (lines 36–39) is the maintainer's. If L-1 lands first, the
   continuation's base has the new text at the same lines.

**Note 13's attestation limits** (carried into E-Q's and E-D's briefs and gates):
- **What the auditor could not check:**
  - it could not re-run the elaboration or the replay;
  - it could not verify `oleans-lndiag2` or Git ancestry.

  I verified the ancestry and the log identities locally (`out/blobs.txt`,
  `out/evidence-identity.txt`).
- **The 5-file lint was not reproducible from the bundle.** The bundle had only 2 of the 5
  `Diagonalization/` files. The fill gates' bundles should carry every file the lint scope and
  the screen population read, or scope the lint claim to the bundled files.
- **Execution claims stay maintainer- and user-attested** in the packs.

**E-Q (`exists_queryTM`):**
- **The ledger** (note 8):
  - the capped locator costs `O(n + log³(n + 2))`, with at most one final capped witness run;
  - a timeout certifies `ℓᵢ₊₁ > n`;
  - no monotonicity of `f` or `g` is assumed;
  - an oversized `f a` is compared or timed out before any rung is materialized;
  - `g`'s witness and the materialization cost `O(g n + 1)`, by `n ≤ g n`.

  Note 8 is a mathematical justification, not a Lean route.
- **Read the pure definitions only through their published equations** (rule 10): `budget_eq`,
  `ladder_zero` and `ladder_succ`, `stage_spec`, `stage_eq`, `stage_of_le_two`, `stageCode_eq`,
  `query_eq`, `query_of_not_guard`. Together they now cover every input (note 3).
- **The empty code:** `stageCode i = []` occurs at `j = 0`, and the writer must handle it.
- **E-Q does not rewrite the budget.** The middle word keeps `bits (g n)`; the rewrite is E-D's
  leaf.
- **One worker per file.** E-Q and E-D are both in `NTimeDiagonalizer.lean`, so they cannot run at
  the same time (C1's fill plan: one worker per file). Sequence them, or re-home one contract.
- **Screen and lint bases at `0a5878ed`, to re-measure at issue:**
  - 7-file screen: 49 declarations, 6 pairs, 1,814 characters, all of them in
    `TimeConstructible.lean`;
  - `Diagonalization/` lint: 0 FAIL, 1 WARN.
- **Base:** after #121 (and #122) merge, with a fresh snapshot.

**E-D (`exists_diagonalizer`):**
- **First, X2's decision** (the import topology for BF).
- **The route** (notes 4–7 and 10):
  - **The clock:** `exists_stepClockTMVia` with counter `bits (g n)`; its value is read through
    `counterValue_bits` and #122's `counterValue_eq`, not by defeq (C1-R's E1). `stopAt` is R's
    two verdict states, and the first-verdict clause is kept.
  - **The constants:** `C = max 1 (max C_R C_BF)`, and `K = P + 7 + P'`, using
    `length_bits_le_self`.
  - **The stream:** `expandTM`, W's `ndWriterTM_run_block`, then `skipBackTM`, giving
    `|s| = g n`. The test `b ≤ g n` is what discharges R's `t ≤ s.length`.
  - **The budget leaf** (private, `O(g n + 1)`): guess, test, normalize to canonical `Nat.bits b`
    (strip trailing `false`s; all-false gives `[]`), rewrite the field. The canonical
    `bits (g n)` counter stays intact for the clock.
  - **Output:** suppress provisional simulator output and emit `[true]` only at dispatch. The
    final test must be constant-time and must never scan a timed-out output.
  - **Both exits:** the finish exit includes `τ = d`. Invalid guesses and default branches stay
    within `K·(g n + 1)`.
  - **The transfer to every branch:** `runWith_mapState_of_agreeOn_det` with `phaseHostND`.
- **Sanity lemmas** (note 10):
  - canonicalization at zero;
  - preservation of the selected accepting prefix;
  - rejection on timeout despite provisional output;
  - an out-of-range guess rejected before R runs;
  - `b = 0` rejects.
- **Admissions** (note 9): it is proved modulo E-Q, W, R and BF, or `hBF` under option (iii);
  the step clock is proved.
- **X3's two docstring lines,** if you want them, belong to its integration window.

**H (`ntime_hierarchy`; not asked, but it follows from X1 and X2):**
- **The sketch:** if L-2 does not land in #122, H's brief must refine the binding sketch to the
  route above.
- **The chain** (note 9): fix `N`, `M'`, the code and every constant before choosing a stage.
  Eventual domination gives `C(C₁(c₀f(n+1) + 1) + 1) ≤ g n`; the top needs
  `C₁(c₀ f a + 1) ≤ T*` and `C·2^{C(T*+1)} ≤ n`.
- **The import:** under option (iii), H supplies `exists_ndAcceptsWithin_decider c`.

## (d) Bottom line

- **The PASS stands:** 0 blockers and 0 majors. Minor 1 is true. Notes 2–13 are true; I checked
  3–8, 10 and 11 in substance, and reproduced 2, 12 and 13.
- **#121 (`0a5878ed`): clear to merge** once the records are committed:
  - the round-2 result in the resolutions, with X1 noted;
  - the C1-design patch (R-1 to R-5);
  - this review's pointers.

  The replay passed, 2 of 2 and static-equal (`$S/fills/replay/replay-lndiag2.log`).
- **Before merging, decide X2.** Option (iii) changes `exists_diagonalizer`'s statement and would
  need round 3 here. Options (i) and (ii) do not touch #121.
- **#122: not yet clear to merge.** Its replay has not run. If L-1 (and L-2) go in, its replay
  script's pins and file count change first, and its gate pack must name the docstrings.
