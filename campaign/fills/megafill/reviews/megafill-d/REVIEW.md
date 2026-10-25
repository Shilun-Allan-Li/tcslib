# Review: megafill D's drafting delivery (#163): the triage and the A1 proposal

Reviewer: the maintainer's review sub-agent, 2026-10-24/25. Delivery: PR #163 (merged; `campaign/`
only), drafting base `fe666d60f21e51438374e7c3f3a966eaa93862c0`, reviewed at the campaign tip
`5cade0b848a3bb6d87a2149aacecf4a2af923889`. The tip's Lean equals `1cc8ab3964d63694915297f855dc758458f2d37d`.
Since the base, only #160 changed Lean (NDCodeSimulator, NTimeHierarchy). Every Lean run was
against `oleans-lrcan3`, one at a time, through `leanelab.sh`. Nothing in the repository or
`exchange/` was edited.

**Verdict: the triage is sound.** No candidate is ready at the base. Every paused, held or moved
row and every blocked row matches its plan or backlog entry, and no sorried candidate was missed.
Four records claims are inexact (F4), and one stage-F scan undercounts (F3); neither changes a
verdict.

**On A1: open it, with the listed changes.** The changes:
- `transduce_of_copy` goes in.
- `logSpace_eq` becomes optional: neither route needs it, because the SCP brief must cite the
  published `Complexity.logSpace_le_succ` (F1).
- The `transduce_of_copy` docstring drops its downstream references, and each file's header lists
  the additions (F2).
- Optionally, and at no extra replay cost, add Basic's three readings that H will need.

Why open it: each lemma is exactly its definition's body by `Iff.rfl`/`rfl` in its home file, every
name is unused in the tree and on #161, #162 and #135, and A1 is the only gap between the two
dossiers and their briefs. The review re-proved both dossiers' steps against A1's final forms.
Timing: dispatch the gate now; merge and replay A1 after #161 and #162 (193 modules).

**A1: not yet opened. It is not clear to merge until the user rules on Q-D1, then its API gate
passes, then its merged-tree replay (193 modules, after #161 and #162) passes.**

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 0 | Bases, the tip's Lean content, environment | The base and #160 are as stated. The tip's Lean equals `1cc8ab39`. Toolchain 4.25.0 (`cdd38ac5`) | `out/01-base-tip-and-environment.txt` |
| 1 | A1, statement by statement | Each RHS is its definition's body. Each lemma holds by `Iff.rfl`/`rfl` in an overlay of its home file (4 of 4 elaborate). All 7 names unused on 4 revisions and in the packages; no clash. No `@[simp]`: right. The lint's blind-spot claim is right (all five definitions escape check 8, `transduce` included). `transduce_of_copy` generalizes both instances (checked in Lean). `A1ApiProbe` re-run: exit 0. Complete for both dossiers; `logSpace_eq` unneeded | `out/02-a1-statement-by-statement.txt` |
| 2 | The blockers are real; seal controls | No published eliminator or characterization of the five, on any revision. EQ: 6 of 6 controls fail sealed and close unsealed (control 1 is the `rcases` failure). SCP: 12 of 12 do the same. The review's introduction-form controls: 4 of 4. Both route probes' seals cover every TCSlib definition they touch (metaprogram scan) | `out/03-blockers-and-seal-controls.txt` |
| 3a | Dossier `spaceConstructible_poly` | Every probe reproduces, and the whole target is proved. A consumer probe with A1's final names and `logSpace_le_succ` passes. The route fits the P4.2 gate's note but not the docstring's named rows, so the fill needs an appendix. Duplication: one miss (F1). The base must be after #161 | `out/04-dossier-spaceConstructible_poly.txt` |
| 3b | Dossier E-Q (and E-D's import probe) | Every probe reproduces. The route fits gate 39's locator. At the tip the base sorry set is 22 in 11 (it was 23 in 12 at the base). The order list holds modules of #161 and #162 | `out/05-dossier-EQ-and-ED.txt` |
| 4a | Triage, row by row | 13 of 13 verdicts confirmed, each entry quoted. F6 may become briefable once #161 merges. Lifting H's order would not make H ready. The MIG-1 scan undercounts (F3) | `out/06-triage-rows.txt` |
| 4b | Census, missed candidates | 110 sorried declarations in the campaign's areas at the tip, all accounted for. File for file the census matches the drafter's, minus #160's proof. **None missed** | `out/07-census-missed-candidates.txt` |
| 5 | A1's replay closure and order | 192 modules, reproduced (193 after #162). A1's closure lies entirely inside #161's (325). It shares 4 modules with #162. Order: #161, then #162, then A1 | `out/08-replay-closure-and-order.txt` |
| 6 | Q-D1 to Q-D6 | Recommendations, with whose decision each is | `out/09-open-questions.txt` |
| 7 | Records | Every tcslib hash resolves and means what the text says. The non-tcslib hexes are package and toolchain revisions that match the manifest. The env logs meet addendum v2.5. The file list matches (55 = 55). Some line references are inexact (F4) | `out/10-records.txt` |

Probes are under `probe/` (the A1 overlays and patch in `probe/a1-overlay*/`; `A1ConsumerProbe`,
`ReviewDupProbe`, `ReviewBlockerControls`, the two `*DefScan`). Scripts are under `scripts/`.
Closures are under `closure/`.

## Findings

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | minor | `scp/SCPRouteProbe` · `scp_route` (dominance step); report "A1"/Q-D1 | The route proves `logSpace n ≤ n + 1` inline, through `scp_logSpace_eq` and `Nat.log_le_self`. The lemma is published: `Complexity.logSpace_le_succ`, `SpaceComplexity/Machines/ARMWidth.lean:51`. ARMWidth is in the route's closure, but the dup probe never posed the statement. This is the gate-69/72 failure mode. It also means the claim that the route "needs" `logSpace_eq` is wrong. | `probe/ReviewDupProbe.out` (`exact?` gives `exact logSpace_le_succ n`). `probe/A1ConsumerProbe.out`: the target proves sealed with `logSpace_le_succ` and without `logSpace_eq` | The SCP brief prescribes citing `logSpace_le_succ` and lists it among the hits. `logSpace_eq` stays in A1 only as Basic's formula lemma (optional). |
| F2 | minor | `a1/A1ApiProbe` · `transduce_of_copy` docstring; the A1 plan | The docstring names downstream lemmas and a module: "`Complexity.KarpLipton.transduce_drop_true` and `transduce_fT_copy`, `MeyerVerifierGlue`". The second name is not fully qualified (`Complexity.Meyer.transduce_fT_copy`), and the reference goes stale at re-pointing. The plan also omits the module headers' "Main results" lines, which the gate-73 precedent includes. | `out/02` §Docstrings | Use the review's patch (`probe/a1-overlay/a1.patch`). Put the instance names in the PR body and a ledger row. |
| F3 | minor | `evidence/mig1-moved-proofs-scan.txt` (T12) | The scan says "the other seven pass none". In fact `f2_counter_count_space` passes `MultiTapeTM.initCfg` and `Cfg.init` (`Catalog.lean:4100, 4106`). `f2_counter_heads` also passes `Cfg.inputSymbol` (4143). `f2_counter_space` passes `MultiTapeTM.spaceUsed` (4190). The verdict (a refresh first) stands, more strongly. | `probe/mig1-unfoldscan.txt`; the lines read by hand | Q-D4's refresh decides each moved proof by a seal test at its destination file, not by a name scan. |
| F4 | minor | the report's T1, T2, T7, Dossier 2, Records | Four accounting errors. (a) "No in-flight file" (E-Q) and "no in-flight PR touches its closure" (SCP): both order lists contain `Deterministic` (#161), and E-Q's also contains `NDCodeSimulator` and `NTimeHierarchy` (#162). (b) "#161 and #162 edit" NDCodeSimulator: only #162 does; the evidence diffed #161 against the base, not its merge base `90688cbb`. (c) E-Q's "docstring 239–269" is 248–269. (d) "#126 merged": it merged into a stacked base and landed by #127/#128. Separately, check 8 misses `transduce` too (via `transduce_append`), not only "the first four". | `out/04`, `out/05`, `out/10`; `probe/fi-*-tip/order.txt` | Correct them in the briefs. Issue both briefs at A1's landing commit, which comes after #161 and #162. |
| F5 | note | A1's files; Q-D2's re-pointing | `SpaceComplexity/Basic.lean` and `ClassNP/Transducer.lean` are Hydroxyi's (`Authors: Hydroxyi`; Transducer has never been edited by the campaign). The two copying-state instances are in `CircuitComplexity/*`, outside the standing exceptions. | file headers; `git log` | Adding equation lemmas beside his definitions is mechanical, so the user decides, with an FYI to Hydroxyi. The re-pointing gets a ledger row for the user's 12.2c window and is not part of A1. |
| F6 | note | E-Q dossier | At the tip, E-Q's base sorry set is 22 in 11 (#160 proved `exists_replayCanonizer`). The drafter's 23 in 12 is correct for its base. | `probe/fi-eq-tip/base-sorries.txt` | Re-measure at issue, as planned. |
| F7 | note | `scp/SCPSealControl` | The SCP blocker controls are `rfl` equations. The route meets the blocker as an introduction (`⟨_, _⟩`, `intro`). | `probe/ReviewBlockerControls.out`: all four forms fail sealed and close unsealed | None. Briefs may use the introduction-form controls. |
| F8 | note | T5 H; Q-D3 | Lifting the 2026-10-15 order would not make H ready. H must read SPACE membership and `DecidesInSpace` (check 8 lists both) as well as its corollaries' class readings. U₀ is proved modulo UniversalK. | `out/06` T5, T6 | Q-D3: keep the order. Optionally add Basic's three readings to A1 (free replay). |
| F9 | note | T4 F6 | F6 was correctly blocked at the base. Once #161 merges, the remaining items are the header-ruler leaf (Q-U2: authorize it privately or promote U2-E's), the import union, and a fresh import probe. F6 needs nothing of A1. | `out/06` T4 | Re-triage F6 when #161 merges; it could be megafill D's third item. |
| F10 | note | SCP brief (to draft) | The route does not use the docstring's two named rows (`computesFunInTime_polyUnary_spaceUsed`, the polyBits space clause). `spaceConstructible_linear`'s last calc is the copy hazard. | `Savitch.lean:65–80`; `Constructible.lean:517–537` | The brief requires a "Fill appendix" in the docstring (as B3a's rows have, `Constructible.lean:478, 513`) and puts `Constructible.lean` in the screen population. |

## The A1 PR's exact contents (as recommended)

These are additions only, all public-facing, with no `@[simp]`. The patch is
`probe/a1-overlay/a1.patch`, and `probe/a1-overlay-ext/a1.patch` adds the option. Every overlay
elaborates against `oleans-lrcan3`: exit 0, with only `TimeConstructible`'s two base sorry
warnings. Lint, head against base: 0 FAIL, the same 2 WARN. Freeze: N → N + 7, or N + 10 with the
option. Line numbers are the tip's.

**1. `TCSlib/Complexity/ClassP/TimeConstructible.lean`**: after line 76 (the last line of
`def TimeConstructible`):

```lean
/-- **Time constructibility, unfolded**: `T` is time constructible exactly when `n ≤ T n` for
every `n` and, for some constant `c > 0`, some machine computes `(T |x|).bits` on every input `x`
within `c · (T |x| + 1)` steps. -/
theorem timeConstructible_iff (T : ℕ → ℕ) :
    TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) :=
  Iff.rfl
```
Header, before line 52: `` * `Complexity.timeConstructible_iff` — the definition as an equivalence. ``

**2. `TCSlib/Complexity/SpaceComplexity/Constructible.lean`**: after line 63 (the last line of
`def SpaceConstructible`):

```lean
/-- **Space constructibility, unfolded**: `S` is space constructible exactly when
`logSpace n ≤ S n` for every `n` and, for some constant `c > 0`, some machine computes
`x ↦ (S |x|).bits` in space `c · S` (`Turing.FinTM.ComputesInSpace`). -/
theorem spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n :=
  Iff.rfl
```
Header, before line 41: `` * `Complexity.spaceConstructible_iff` — the definition as an equivalence. ``

**3. `TCSlib/Complexity/SpaceComplexity/Basic.lean`** (Hydroxyi's file; F5). After line 102 (the
last line of `def ComputesInSpace`), inside `namespace Turing.FinTM`:

```lean
/-- **Computing in space, unfolded**: `M` computes `f` in space `s` exactly when on every input
`x` there is a time `t` at which `M` has halted with output `f x`
(`Turing.FinTM.ComputesInTime`), having visited at most `s |x|` work-tape cells by then. -/
theorem computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length :=
  Iff.rfl
```
Optional, after line 162 (`def logSpace`), inside `namespace Complexity`. Neither route needs it
(F1):

```lean
/-- The logarithmic bound's formula: `logSpace n = Nat.log 2 n + 1`. -/
theorem logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl
```
Header, before line 49: `` * `Turing.FinTM.computesInSpace_iff`, `Complexity.logSpace_eq` — the
definitions of `ComputesInSpace` and `logSpace` as an equivalence and an equation. ``

The option for H, at no extra replay cost (the user's call):
- after line 107 (`def DecidesInSpace`), in `Turing.FinTM`:
  ```lean
  /-- **Deciding in space, unfolded**: `M` decides `L` in space `s` exactly when it computes the
  one-bit indicator `x ↦ [x ∈ L]` in space `s`. -/
  theorem decidesInSpace_iff (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
      M.DecidesInSpace L s ↔
        M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s :=
    Iff.rfl
  ```
- after line 139 (`def SPACE`), in `Complexity`, shaped like `mem_NTIME_iff`:
  ```lean
  /-- **Membership in `SPACE`, unfolded**: `L ∈ SPACE s` exactly when some machine decides `L` in
  space `c · s` for some constant `c`. -/
  theorem mem_SPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
      L ∈ SPACE s ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n :=
    Iff.rfl
  ```
- after line 167 (`def LOGSPACE`):
  ```lean
  /-- `LOGSPACE` is `SPACE logSpace`. -/
  theorem LOGSPACE_eq : LOGSPACE = SPACE logSpace := rfl
  ```
- and the header line `` * `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff`,
  `Complexity.LOGSPACE_eq` — the definitions of `DecidesInSpace`, `SPACE` and `LOGSPACE`,
  unfolded. ``

**4. `TCSlib/Complexity/ClassNP/Transducer.lean`** (Hydroxyi's file; F5; `variable {σ : Type}`
is in scope). After line 53 (the last clause of `def transduce`):

```lean
/-- A transducer emits nothing on the empty word: `transduce δ o q [] = []`. -/
theorem transduce_nil (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) :
    transduce δ o q [] = [] := rfl

/-- On `b :: l` a transducer emits `o q b` and continues from `δ q b`:
`transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l`. -/
theorem transduce_cons (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) (b : Bool)
    (l : List Bool) :
    transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l := rfl
```
After line 63 (the end of `transduce_append`):

```lean
/-- **A copying state copies**: if from the state `q` every bit is emitted unchanged
(`o q b = some b`) and `q` is kept (`δ q b = q`), then the transducer started in `q` is the
identity, `transduce δ o q l = l`.

**Proof sketch.** Induction on `l`, by `Complexity.transduce_nil` and
`Complexity.transduce_cons`. -/
theorem transduce_of_copy (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (hδ : ∀ b, δ q b = q) (ho : ∀ b, o q b = some b) (l : List Bool) :
    transduce δ o q l = l := by
  induction l with
  | nil => exact transduce_nil δ o q
  | cons b l ih =>
    rw [transduce_cons, hδ, ho, ih]
    rfl
```
Header, before line 33: `` * `Complexity.transduce_nil`, `Complexity.transduce_cons` — the
function's case lemmas; `Complexity.transduce_of_copy` — a state that copies and is kept gives
the identity. ``

PR body and records. The body and the duplication ledger name the two instances
`transduce_of_copy` generalizes: `Complexity.KarpLipton.transduce_drop_true` and
`Complexity.Meyer.transduce_fT_copy`. Each is the general lemma at `fun _ => rfl` twice, as
`A1ConsumerProbe` checks. They are re-pointed in the user's window (12.2c), not in this PR.

Gate. An API gate, like 65, 71 and 73. Its pack points to the consumer probe
(`probe/A1ConsumerProbe.lean`: the SCP target proved sealed with the final names, and E-Q's
witness step).

Replay. 192 modules at the tip; on the merged tree after #161 and #162 it is 193 (`closure/`).

## Missed candidates

None. Every sorried declaration in `TCSlib/Complexity` and `TCSlib/Programs` at the tip (110) maps
to a triage row, an exclusion, or the out-of-scope stub (`out/07`). One forward-looking point:
re-triage F6 when #161 merges (F9).

## Q-D1 to Q-D6 (details and reasons in `out/09-open-questions.txt`)

- **Q-D1 (the user's):** open A1 with F1's and F2's changes. Decide the option of Basic's three
  readings for H; it is recommended, since its replay is free. The additions to Hydroxyi's two files
  are mechanical, so this is the user's call, with an FYI to him. Dispatch the gate now. Merge and
  replay A1 after #161 and #162.
- **Q-D2 (the user's, inside A1):** include `transduce_of_copy`. It is a verified generalization of
  both instances, and it prevents a third copy. The re-pointing is a ledger row for 12.2c, because it
  edits `CircuitComplexity/*`.
- **Q-D3 (the user's):** keep the 2026-10-15 order (H after F6 integrates), for three reasons:
  - lifting it makes nothing ready (F8);
  - F6 may be briefable as soon as #161 merges (F9);
  - the ruling is the same one-fill-per-file rule as E-Q and E-D.

  If F6 stalls once H is otherwise ready, reverse the order rather than lift it. Do not split off
  the corollaries now.
- **Q-D4 (the maintainer's):** refresh stage F's design first. Widen the refresh per F3, deciding
  each moved proof by a seal test. F-A goes after #161.
- **Q-D5 (the maintainer's):** authorize E-Q's eight imports and SCP's one as region (a). The numbers
  are verified. Re-measure E-Q's base sorry set at issue (F6).
- **Q-D6 (the maintainer's):** do not wait for #135's `BinaryArith`. Name it as a copy hazard in
  E-Q's brief, and ledger any private arithmetic leaves against it later.

## What the maintainer should do next

While this review ran, the campaign moved on (seen read-only in `wt-hk`). #161 merged as
`5bbef333a6769b038db6c61d6aa5d0a9e568a267`. #162's replay on the tree after #161 passed
(`cfaaf75af242b8ffd653b2d816a48df315629a93`, 5 of 5). The only Lean change since `5cade0b8` is
#161's three files. At `cfaaf75a` the seven A1 names are still unused (`git grep -w`, 0 hits), so
nothing above changes: #161 is done, and #162 is next, then A1.

1. Ask the user Q-D1 (with the option and F5), Q-D2 and Q-D3.
2. Merge #162 after gate 74 (its replay on the tree after #161 has passed).
3. On a yes, open A1 from `probe/a1-overlay/a1.patch` (or `a1-overlay-ext/` with the option), on a
   branch from the campaign tip. Dispatch its API gate now. Run its 193-module merged-tree replay
   after #161 and #162 merge.
4. At A1's landing commit, have the two dossiers turned into briefs and a two-item megafill D cover:
   `spaceConstructible_poly` first, then E-Q. The SCP brief cites `logSpace_le_succ`, requires a
   Fill appendix, and puts `Constructible.lean` in the screen population. Re-run both pre-ships
   (order lists, base sorries, screens) at that commit.
5. Re-triage F6 now that #161 has merged, as a possible third item. Settle Q-U2's leaf (private, or promoted
   from U2-E) before its brief.
