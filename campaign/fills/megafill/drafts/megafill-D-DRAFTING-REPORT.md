# Megafill D: the drafting report (drafting agent, 2026-10-25)

The deliverable of `campaign/fills/megafill/drafts/megafill-D-drafting-brief.md` (SHA-256
`9a8229a8bcc7e5f2eca0d786f0a05cd2bd9701eefec923a9867876f9eb441981`, verified against the attached
copy and the repository copy at the drafting base; the commit the dispatch named,
`53253f5941df0397f45803e34110f616150aa0a9`, is an ancestor of the base). **Nothing under `TCSlib/`
changed**; every Lean check ran through `scripts/lean_check_tree.sh`, one Lean process at a time, on
copies of the probes under the clone's ignored `.lake/probes/`; no `lake build`; the cache was
fetched for the union of the candidates' Mathlib roots only.

**The drafting base:** `fe666d60f21e51438374e7c3f3a966eaa93862c0`, the campaign tip when drafting
started. Every line number and measurement below is this tree's. **#160 merged three minutes later**
(`90688cbb645fcf1ef66ff6112c83bd8f0413000b`); it changes only `NDCodeSimulator` and
`NTimeHierarchy`, both excluded files, so no triage verdict depends on it.

**The branch:** `drafts/megafill-d`, from the drafting base; it adds files under `campaign/` only,
and is pushed to the repository (no pull request is opened; the user may open one into the campaign
branch).

## The outcome in one paragraph

**No candidate is ready at the drafting base, so no fill brief and no cover is drafted** (drafting
brief §3: "Do not draft a brief for a blocked or excluded item"). Five of the areas are paused, held
or moved by the user's rulings; the other eight are blocked. The two nearest candidates, the
diagonalizer's query machine (**E-Q**, `Turing.NTimeDiag.exists_queryTM`) and
**`Complexity.spaceConstructible_poly`**, are blocked by one cross-cutting gap: under rule 10 (and
its seal test) a fill cannot eliminate a `Complexity.TimeConstructible` hypothesis, nor introduce
`Complexity.SpaceConstructible` or `Turing.FinTM.ComputesInSpace`, because these chapter predicates
have no published `_iff` (lint check 8 counts them as covered through same-named lemmas, its known
blind spot). **One small API PR, "A1"** (six `Iff.rfl`/`rfl` lemmas, and an optional seventh, beside
their definitions in four files; a 192-module replay) makes both ready. Their dossiers are complete
except for the brief text and the screen bases: route, import probe, a sealed route probe with A1 as
local stand-ins (for `spaceConstructible_poly` it proves the whole target), seal controls, order
lists, base sorries and the duplication searches (`megafill-D-triage-fe666d60/`). **Recommendation
(Q-D1):** land A1 first, then issue a two-item megafill D (`spaceConstructible_poly`, then E-Q); a
proposed cover outline is at the end of this report.

## The environment (addendum v2.5, Part 1)

Logs: `campaign/fills/megafill/drafts/megafill-D-env-fe666d60/logs/`.

| Step | Result | Log |
|---|---|---|
| Preflight | 4 CPUs; cgroup v1 limit 14,341,881,856 B, memory in use (`usage − total_cache + total_shmem`) 40,030,208 B, so the headroom is 13.32 GiB (floor 4); the clone's filesystem ext4 (not memory-backed), 26,444,976,128 B = 24.63 GiB free (floor 12) | `logs/preflight.log` |
| Toolchain | elan, then `leanprover/lean4:v4.25.0` (archives extracted with `TAR_OPTIONS=--no-same-owner`); `lean --version` and `lake --version` in the log | `logs/toolchain.log` |
| Re-check | 22.11 GiB free after the toolchain (floor 8) | `logs/recheck.log` |
| Cache store | `/root/.cache/mathlib` absent before the fetch: 0 archives | `logs/cache-store.log` |
| Roots | 57: the union of `Savitch`'s order list (182 modules) and E-Q's overlay order list (80 modules at the first overlay; the final overlay's 81 add no root beyond `Mathlib.Data.Nat.Log`, which is in the union) | `logs/mathlib-roots.txt` |
| Narrowed fetch | `TAR_OPTIONS=--no-same-owner lake exe cache get <57 roots>`: exit 0; attempted and downloaded 1,029, decompressed 1,029, no failure; 93 s | `logs/cache-get.log`, `logs/cache-get.time` |
| Manifest | 11 packages present, each matching the manifest's URL and revision; 4 absent (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`), imported by no module of the lists: PASS | `logs/manifest-check.log` |
| Cache check | no empty olean among 1,038; a probe importing the first root elaborated (exit 0) | `logs/cache-check.log` |
| Bootstrap | the 213-module union in topological order: 213/213 exit 0, 0 errors, 33 sorry warnings (agreeing module by module with the union of the two base sorry sets); 1,873 s of Lean time; peak 2,970,904 KiB (`Build/CfgRecord`); per-module time and memory logged | `logs/bootstrap.log`, `logs/bootstrap-order.txt` |
| Bootstrap addendum | `ClassNP/Transducer`, the one module the `Savitch` overlay adds: exit 0 | `logs/bootstrap-addendum.log` |

The environment folder's README describes the tools; per-module memory is the children's peak
resident set from `getrusage` (the host has no `/usr/bin/time`).

## The triage (drafting brief §3)

Each row gives: (1) the status under the plan and the backlog, with the entry; (2) the statement
gate; (3) the route; (4) what is published and what is missing; (5) dependencies; (6) size and
verdict. Line numbers are the drafting base's.

| # | Candidate | (1) Status | (2) Statement gate | (3) Route | (4) Published at the base / missing | (5) Dependencies | (6) Size; verdict |
|---|---|---|---|---|---|---|---|
| T1 | **E-Q** `Turing.NTimeDiag.exists_queryTM` (`Diagonalization/NTimeDiagonalizer.lean:270`) | **Active**: C1-E's first fill (backlog, C1-E statement phase and "E-Q, then E-D, after #126"; #126 merged); `campaign/items/c1/c1e/C1E-design.md` ("After the gate"). | **Frozen**: gate 39 (round 2 PASS 0/0/1/12, note 8 on this contract), unchanged by gate 45 (note 9). | The capped locator of the P3.3 gate's round 2, §2: from `ℓ₀ = 2`, per rung run `f`'s witness on `1^(ℓ+1)` under the step clock capped at `c_f (n + 1)`; a timeout or `f a > n` stops inside the stage, else `(f a + a + 1)⁴` against `⌊log₂ n⌋` (power-of-two test at equality) stops, marks the top, or writes the next rung. Then the code `stageCode i`, `g`'s witness (middle) or `T*` (top), and the `pairEncode` materialization. Rounds as contracts under `Round.iterate` (the amortized ledger needs value-dependent round times). | Every host and row the route names is published (import probe 81 checks of 81 names, 0 errors, 0 warnings). **Missing: `Complexity.timeConstructible_iff`** (A1): the witnesses of `hf`, `hg` cannot be obtained without it (control 1 of `EQSealControl`: the sealed `obtain` fails). The locator's arithmetic leaves are private by the C1-E design's approved packaging. | No in-flight file. Eight new imports (overlay: seven TCSlib modules and `Mathlib.Data.Nat.Log`; the module's only importer is the `Diagonalization` facade). E-D waits on it (same file). #135 adds a `ClassP/BinaryArith` layer (not in the campaign branch): a future hazard and source. | 2,000–4,000 lines (C1-E design). **Blocked on A1.** |
| T2 | **E-D** `Turing.NTimeDiag.exists_diagonalizer` (`NTimeDiagonalizer.lean:335`) | **Active**, after E-Q: "E-Q and E-D share a file, so they run in sequence" (gate 39 resolutions, carry-forward). | **Frozen**: gate 39, restated by X2 at gate 45 (PASS 0/0/2/10, `hBF` a hypothesis). | `Turing.NDTM.phaseHostND` assembly (its docstring): the query (E-Q's machine by `exists_inputCallTM`), the guessed stream (`g`'s witness, `expandTM`, `ndWriterTM_run_block`, rewind), the nominal budget leaf, the middle (`exists_ndInterpreterCore` under `exists_stepClockTMVia`), the top (`hBF`'s decider under `vhostSilentTM` and the clock), transfer by `runWith_mapState_of_agreeOn_det`. | Hosts published (import probe 20 checks of 20 names, 0 errors, 0 warnings). **Missing: `timeConstructible_iff`** (A1), as for E-Q. | E-Q (statement, proved modulo); the core `exists_ndInterpreterCore` and its module `NDCodeSimulator` (excluded: #161 and #162 edit it), so its import serializes E-D's landing after them. | 1,000–2,000 lines. **Blocked**: A1, and sequenced after E-Q. |
| T3 | **NF** `FinNDTM.exists_codeNDTM_accepts_linear` (`ClassNP/NDNormalForm.lean:78`) | **Active**, wave 2 of C1 (C1 fill plan; the user's ruling of 2026-10-17: NF's display guess uses a **public controller contract**, stated in `Build/NDHost` by a statement PR with its gate and filled by a W continuation; "NF issues in wave 2"). | **Frozen**: gate 38 (#120, moved byte-identical; closed). | Guess the display records with the controller-flavour writer, verify deterministically; the ND transfer; `relabelState` (C1 fill plan). | **Missing: the controller contract.** `Build/NDHost` publishes only the trivial controller's `ndWriterTM_run_block` (evidence §2). | The contract's statement PR, gate and fill. | 2,500–5,000 lines. **Blocked** on the controller contract. |
| T4 | **F6** `Complexity.space_universal` (`SpaceComplexity/Hierarchy.lean:150`) | **Active**, B6 F6, "off the headline's path; last (no consumer)" (B6 fill plan §2). | **Frozen**: the RD-3 gate (05, PASS 0/0/4) and the B6 hosts gate (13, PASS 0/0/5; `C · s`). | A header-ruler startup (finite-state pair scan), the startup's canonization, H5's ruler host `exists_rulerHostTM` around H2-F's loop on the virtual input, the per-code ledger (its docstring; B6 fill plan §6). | **Missing: `rulerHostCfg` and `forwardLoopCfg`'s field equations and `pairEncode_drop`**, all in **#161** (in flight). | #161; the header-ruler leaf it shares with U2-E (megafill C's Q-U2: publish it when this item is briefed). | 800–1,500 lines. **Blocked on #161.** |
| T5 | **H** `Complexity.space_hierarchy` (`Hierarchy.lean:267`) | **Active**, the headline: critical path F1 → F2 → F3 → H, and F3 landed (#158, 2026-10-24). **Ordered after F6:** "F6 and H: the union [of imports], with H after F6 integrates" (user, 2026-10-15; backlog RD-3, B6 fill plan). | **Frozen**: P4.3 gate and the RD-3 gate. | The window route of its docstring: `D` runs `U₀` (`exists_selfUniversal`) in a window of radius `a · g n` on the record rows under the configuration-count clock (`exists_configWindowRunnerTM`, F3), flips the verdict; the alphabet reduction; the contradiction. | Not probed (blocked by the ruling). Likely also needs eliminators for `SPACE`/`DecidesInSpace` (lint check 8 lists both with no lemma). | F6 (the ruling); `U₀` (U2-U, megafill C; proved modulo). | 2,100–4,500 lines with its corollaries. **Blocked by the ordering ruling** (Q-D3). |
| T6 | **H's corollaries** `LOGSPACE_ssubset_PSPACE` (`:284`), `SPACE_linear_ne_NP` (`:314`) | **Active**, part of batch H ("then `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP`", B6 fill plan §6). | **Frozen**: P4.3 gate. | Pure corollaries of `space_hierarchy` (their sketches); the second also needs a padding decider, a padding reduction and `spaceConstructible_poly` at degree two. | Not probed. `LOGSPACE`, `SPACE` have no characterization lemma (check 8). | H (the ruling); T7 for the second. | 600–1,500 lines. **Blocked** with H; a separate brief would be an item split (Q-D3). |
| T7 | **`Complexity.spaceConstructible_poly`** (`SpaceComplexity/Savitch.lean:81`) | **Active**: "Savitch and `spaceConstructible_poly` are a later batch" (B3a brief, `campaign/fills/ch34/briefs/ch34-b3a.md:48`); not covered by the program-route ruling (2026-10-12, "the remaining **algorithms** are written as programs"; B3a's two constructibility rows were filled as machines the same day) nor by stage 2's pause. Its one consumer is `SPACE_linear_ne_NP`. | **Frozen**: P4.2 gate (`campaign/gates/ch4-p42/`, PASS 0/0/5/3: "the sketch's unary catalog route is also viable once its exact output and positive-bound packaging are supplied"). | A tail transducer, then `polyUnaryTM 1 c` (sharp time `(5c + 5)·n^c`), `prependTM [true]` and the length counter by buffered composition give `bits (n^c + 1)` for `n ≥ 1`; the timed conditional on `x = []` handles `n = 0`; time `O(n^c + 1)` gives the space by `spaceUsed_le_mul_succ`, as B3a's linear row does. | Every row published (import probe 21 checks of 21 names, 0 errors, 0 warnings). **Missing: A1's `spaceConstructible_iff`, `computesInSpace_iff`, `logSpace_eq`, `transduce_nil`, `transduce_cons`** (controls in `SCPSealControl`); one import, `ClassNP.Transducer`. **With A1's stand-ins the sealed route probe proves the target** (`scp_route`: 0 errors, 0 warnings, axioms `[propext, Classical.choice, Quot.sound]`, under a seal of 12 definitions). | None in flight. | 150–250 lines. **Blocked on A1 only.** |
| T8 | `Complexity.savitch` (`Savitch.lean:114`) | **Moved to the program route** (plan decision log, "Language first" and "Five route decisions" (1), 2026-10-12) and **paused** with stage 2 (backlog PROG-4: "Paused (user, 2026-10-14) … general `savitch` stays sorried"). `PSPACE_eq_NPSPACE` is proved through the ARM layer. | Frozen (P4.2). | The Savitch program, compiled by stage 2. | — | Stage 2 (paused). | **Not a fill** (paused; not revived). |
| T9 | The RAM simulation: `RAMSimulation/Classes` (9), `Simulation` (2), `WordSize` (3) | **Paused**: stage 2 (backlog PROG-4, "Paused (user, 2026-10-14) … No stage-2 brief … is written until the user resumes it"; plan decision log 2026-10-14, "stage 2 paused"). | Frozen: the stage-2 statement gate (10, closed 0/0/4). | — | — | — | **Not a fill** (paused). |
| T10 | `Programs/WordRAM/Extended` (18) | **Paused** with stage 2: PROG-2's mirror and PROG-3's footprint, gated with stage 2 (backlog PROG-2 to PROG-4). | Frozen: the stage-2 gate (as a specification mirror). | — | — | — | **Not a fill** (paused). |
| T11 | TQBF and the formula kit: `ClassPSPACE/TQBF` (21), `FormulaKit/Emit` (10), `FormulaKit/Gate` (10) | **Held**: RD-2a/RD-2b, "Fills held (user, 2026-10-14): the ARM merge proves `TQBF_PSPACEHard` without `ConfigCodec` or `FormulaKit`, which now have no consumer" (backlog RD-2). | Frozen: the RD-2 gate (11, PASS 0/0/2). | — | — | — | **Not a fill** (held). |
| T12 | MIG-1 stage S's specifications: `Composition` (3), `Simulation` (1), `Build/Wrappers` (2), `Encoding` (1), `ClassP/TimeConstructible` (2), `Build/Primitives` (3), `Build/Loop` (5) | **Active**, MIG-1's stage F, batches F-A to F-D ("Next for MIG-1: the fill batches F-A to F-D", backlog MIG-1 row; `campaign/items/mig1/MIG1-design.md` §9), never briefed. MIG-24's groups T1–T6 and T2b are **folded into these batches** (user, 2026-10-17). | **Frozen**: the MIG-1 statement gate (16, round 2 closed), landed by #98. | F-A: move each row's body into its spec, swap the 10 rows; move three space proofs from `Build/Catalog` (counter, branch, conditional ledger). F-C (Loop) cites F-A's specs; F-B (Primitives) F-A's and F-C's; F-D deletes the region. | The stage-F plan predates rule 10 (2026-10-16): the moved `f2_branch_space` unfolds `spaceUsed`, `spaceUsedByTape` and `visitedByTapeHead` (evidence: the scan in this report's records), and its rule-10 rewrite needs `spaceUsedByTape_eq_card`, which is in **#161**. MIG-24's T1 needs a general rewind lemma whose statement and home no entry fixes. | #161; F-B and F-C on F-A; F-D on all. F-A edits `Simulation` and `Encoding` (about 300 downstream modules). | F-A about 0.5k lines moved or written (design §9) plus MIG-24's share. **Blocked**: a maintainer refresh of the stage-F plan first (Q-D4). |
| T13 | `Build/RecordTable`'s four rows | **Paused** by MIG-23 (retirement candidates; "Narrow to rows 17–18", user 2026-10-12). | Frozen (wave 1). | — | — | — | **Not a fill** (paused). |

Out of the campaign's scope (not candidates): `Expanders/Chernoff` (chapter 7's disclosed stub) and
the non-complexity areas (`BooleanAnalysis`, `GraphTheory`, `ErrorCorrectingCodes`, `Tactics`).
Excluded by the drafting brief (in flight or running): `NDCodeSimulator`, `NTimeHierarchy`,
`Build/InterpreterStartup`, `Deterministic`, `Build/StepBlockForward`, `Build/InputDevice`,
`CodeSimulator`, `UniversalK`, `Build/ZoneRebalance`.

**Ranking of the ready items:** none. **Ranking after A1** (the drafting brief's preferences:
independent owned files, admissions that others wait on): (1) `spaceConstructible_poly`: small,
independent, its route fully probed; complete, it removes an admission that `SPACE_linear_ne_NP`
cites. (2) E-Q: large; complete, it removes an admission that E-D and `ntime_hierarchy` cite.

## The cross-cutting blocker: rule 10 and the chapter predicates

Ground rule 10 (with the 2026-10-23 scope bullet) binds TCSlib's own definitions: a fill reads
another file's definition only through published lemmas, and its seal test
(`attribute [local irreducible]` on every other-file definition the proofs touch, with an `rfl`
control per sealed definition) must pass. The chapter-level predicates the two nearest candidates
need have no such lemma at the drafting base (evidence:
`megafill-D-triage-fe666d60/evidence/triage-greps.txt`, §3):

| Definition (home) | Needed for | Published at the base |
|---|---|---|
| `Complexity.TimeConstructible` (`ClassP/TimeConstructible.lean:73`) | E-Q and E-D: obtaining the witnesses of `hf`, `hg` | `timeConstructible_id`, `timeConstructible_poly` (introductions only); no eliminator |
| `Complexity.SpaceConstructible` (`SpaceComplexity/Constructible.lean:60`) | `spaceConstructible_poly`: introducing the target | `spaceConstructible_logSpace`, `_linear` (instances); no characterization |
| `Turing.FinTM.ComputesInSpace` (`SpaceComplexity/Basic.lean:100`) | `spaceConstructible_poly`: introducing the space clause | `ComputesInSpace.mono` (Basic), `.computesFunInTime` and `.computesFunInTime_and_forall_spaceUsed_le` (`ConfigCount`): eliminations only |
| `Complexity.logSpace` (`SpaceComplexity/Basic.lean:162`) | `spaceConstructible_poly`: the dominance conjunct | no equation lemma |
| `Complexity.transduce` (`ClassNP/Transducer.lean:51`) | `spaceConstructible_poly`: the tail transducer's function | `transduce_append` only; no case lemmas |

Lint check 8 does not list the first four: each has some lemma named after it, which is the check's
recorded blind spot (backlog, "Lint check 8's blind spot", 2026-10-16). The controls make the gap
mechanical: in `eq/EQSealControl.lean.txt` control 1 is the eliminating `obtain` on
`TimeConstructible`, which closes unsealed and fails sealed; in `scp/SCPSealControl.lean.txt` the
`SpaceConstructible`, `ComputesInSpace`, `logSpace` and `transduce` controls do the same (E-Q's
control 1 fails sealed with "`rcases` failed: `hf : TimeConstructible f` is not an inductive
datatype"; all 6 and all 12 controls close unsealed and fail sealed, one error each). The precedent
is F3's escalation E1 (`RecordAt`, `recordLength`, `posWidth`): after the user's ruling of
2026-10-16 ("specification facts come from published equation lemmas, not from unfolding") they were
published by an API PR before the continuation.

## A1: the proposed API PR ("API PR first")

**Statements** (proved, under `a1_` names, in `megafill-D-triage-fe666d60/a1/A1ApiProbe.lean.txt`:
all seven elaborate, with no error or warning; axioms within the standard three). In the PR each
goes beside its definition, with a docstring stating its formula and no `@[simp]` (`policy.md` §1,
*Definitions land with their lemmas*: a predicate gets an `_iff` characterization, any other
definition an equation lemma or case lemmas):

```lean
-- ClassP/TimeConstructible.lean, beside `Complexity.TimeConstructible`
theorem Complexity.timeConstructible_iff (T : ℕ → ℕ) :
    TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) := Iff.rfl

-- SpaceComplexity/Constructible.lean, beside `Complexity.SpaceConstructible`
theorem Complexity.spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n := Iff.rfl

-- SpaceComplexity/Basic.lean, beside `Turing.FinTM.ComputesInSpace` and `Complexity.logSpace`
theorem Turing.FinTM.computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool)
    (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length := Iff.rfl
theorem Complexity.logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl

-- ClassNP/Transducer.lean, beside `Complexity.transduce`
theorem Complexity.transduce_nil (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) :
    transduce δ o q [] = [] := rfl
theorem Complexity.transduce_cons (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (b : Bool) (l : List Bool) :
    transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l := rfl
-- optional (Q-D2): the copying-state lemma, which the two published instances specialize
theorem Complexity.transduce_of_copy (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (hδ : ∀ b, δ q b = q) (ho : ∀ b, o q b = some b) (l : List Bool) :
    transduce δ o q l = l
```

**Replay closure** (the four files' downstream modules, the root excluded, MEASURED from the import
graph at the base): `ClassP/TimeConstructible` 137, `SpaceComplexity/Basic` 115,
`SpaceComplexity/Constructible` 53, `ClassNP/Transducer` 26; **192 in the union**. None of the four
files is in flight; `NTimeHierarchy` and `NDCodeSimulator` (#161, #162) are in the closure, so A1's
replay chains after theirs or before, as the maintainer orders it. **Gate:** an API gate, as for
#139, #149 and #161. Additions only: the freeze is "N → N + 6 (or 7) public declarations".
**Recommendation (Q-D1): open A1 now**, before any further megafill D work; it is the only thing
between the two dossiers and their briefs.

## Dossier 1: `Complexity.spaceConstructible_poly`

**Target:**
`Complexity.spaceConstructible_poly (c : ℕ) (hc : 1 ≤ c) : SpaceConstructible fun n => n ^ c + 1`
(`SpaceComplexity/Savitch.lean:81`, its `sorry` at 83; the docstring 65–80). Folder:
`megafill-D-triage-fe666d60/scp/`.

**The route in five lines** (a refinement of the frozen sketch: unary, exact output, positivity by
time; the P4.2 gate called the unary route "viable once its exact output and positive-bound
packaging are supplied").
1. A tail transducer (`Complexity.transducerTM` over one bit of state; its function is `List.tail`
   by `transduce_cons` and the copying-state lemma) in time `n + 1`.
2. Buffered compositions (`bufferedCompTM_computesInTime`) with `polyUnaryTM 1 c` (sharp time
   `(5c + 5)·(|y| + 1)^c`, `polyUnaryTM_computes`), `prependTM [true]` and the length counter
   (`computesFunInTime_lengthBits`): `bits ((|x.tail| + 1)^c + 1)`, which is `bits (n^c + 1)` for
   `n ≥ 1`.
3. The timed conditional `computesFunInTime_cond` on `x = []` (decider
   `computesFunInTime_ifEq [] [true] [false]`, constant branch `computesFunInTime_const (bits 1)`):
   `bits (n^c + 1)` for every `x`.
4. Time `O(n^c + n + 1)` ≤ `A·(n^c + 1)` (`n ≤ n^c`); space ≤ `k·(t + 1)` (`spaceUsed_le_mul_succ`).
5. Dominance `logSpace n = log₂ n + 1 ≤ n + 1 ≤ n^c + 1`; package by `spaceConstructible_iff` and
   `computesInSpace_iff` (A1).

**Evidence (all at the drafting base):**

| Check | Result |
|---|---|
| Overlay (`SavitchOverlay.lean.txt`, one import) | exactly the file's two sorry warnings (overlay 82, 115); no cycle (`ClassNP/Transducer`'s closure does not contain `Savitch`) |
| Order list, roots, base sorries (on the overlay) | 183 modules, 54 roots, 27 sorried declarations in 10 modules |
| Import probe | 21 checks of 21 names, 0 errors, 0 warnings |
| A1 probe | the five lemmas this route needs elaborate by `Iff.rfl`/`rfl`, and the optional copying-state lemma by a short induction; the route probe uses all six (without the sixth a fill would re-prove it privately for its transducer: Q-D2) |
| Route probe | **the whole target**, as `scp_route`, sealed over 12 TCSlib definitions with A1 as stand-ins: 0 errors, 0 warnings, the standard three axioms |
| Seal controls | 12 goals: all close unsealed, all fail sealed, one error each; four of them are the blocker |
| Duplication probe | `exact?`: nothing for the three new private statements; `spaceUsed_le_mul_succ` for the space step (cited) |
| Lint | `SpaceComplexity` 0 FAIL, 82 WARN over 107 files; `Savitch` none |

**Semantic duplication (drafting brief §5).** The route's private declarations and their searches
(the tree, #161's and #162's heads, #135's tree; `evidence/open-pr-searches.txt`):
- the tail transducer's two tables (`scp_tailδ`, `scp_tailO`): no published transducer computes
  `tail` (`KarpLipton.dropMarker` strips a marker `1ᵏ0`); `Complexity.polyTimeComputable_tail`
  (`ClassNP/PolyTimeBlockLoop.lean:143`) is polynomial time only, too weak for the linear time the
  space-from-time step needs. New, small.
- "after the first bit it copies": an instance of the copying-state idiom, published twice (Q-D2).
  The probe cites the general lemma proposed for A1, so no private copy is written.
- the tail's value, `(|x.tail| + 1)^c ≤ |x|^c + 1` and the case split at `x = []`: pure list and
  arithmetic facts; no published statement (searched: `tail`, `length_tail` lemmas in TCSlib).
- the space-from-time step: `spaceConstructible_linear` (`Constructible.lean:517`) does the same
  calculation inline at `n + 1`; the probe cites `spaceUsed_le_mul_succ` directly and shares no
  proof text with it beyond that citation. A brief should still list `spaceConstructible_linear` as
  the copy hazard.

**Dependencies:** none in flight (`Savitch`'s downstream is the `SpaceComplexity` facade only, and
no in-flight PR touches its closure). **Proved modulo:** none. **Size:** 150–250 lines (the probe's
sealed section, helpers and docstrings included, is 144). **Budget:** 1.5 hours.

## Dossier 2: E-Q, `Turing.NTimeDiag.exists_queryTM`

**Target:** `Turing.NTimeDiag.exists_queryTM` (`NTimeDiagonalizer.lean:270`, its `sorry` at 273; the
docstring 239–269 with the named fill obligations). Folder: `megafill-D-triage-fe666d60/eq/`.

**The route in five lines** (the docstring's, with the round-2 locator; binding where it names a
host).
1. A guard (a private finite-state leaf: unary and `|x| ≥ 3`), and `computesFunInTime_cond` between
   `[]` and a main machine that reads only `|x|` (it computes `query f g (1^|x|)`).
2. The locator as a `Turing.Round.iterate` loop of contracts (`round_iff`, three escapes): each
   round expands `1^(ℓ+1)` (`expandTM_run_ofCfg`), runs `f`'s witness through `vhostSilentTM`
   (lockstep) under `exists_stepClockTMVia` with the counter `bits (c_f (n + 1))`, and decides.
3. The decision's arithmetic on operands of `O(log n)` bits (private leaves, by the C1-E design's
   approved packaging; or install calls, Q-D6), the next rung written in unary (at most `n`).
4. After the loop: `stageCode i` from the stage index, `g`'s witness by `exists_inputCallTM`
   (middle) or `T* = X²` (top), the `pairEncode` materialization, the flag.
5. The ledger: passed rounds `O(ℓ_{h+1})`, which sum to `O(n)` (`∑ ℓ_{h+1} ≤ 2ℓ_s < 2n`); the last
   `O(n)`; the rest `O(g n + 1)`.

**What the probes establish** (`EQRouteProbe.lean.txt`, sealed; 0 errors, 0 warnings, six lemmas,
each within `[propext, Classical.choice, Quot.sound]`, sealed over 5 definitions):
- `eq_witness`: the witnesses come out of `hf`, `hg` through A1's `timeConstructible_iff` (and only
  through it: control 1);
- `eq_timeout`: a run not halted by `c (n + 1)` certifies `n < f a`;
- `eq_decide_spec`, `eq_stage_of_stop`: the locator's decision at a rung below `n` is exactly the
  comparison with the next rung, so it stops at `stage f n` and knows the top;
- `eq_round_le`: a passed rung's operands (`a`, `f a`, `f a + a + 1`) are at most the next rung;
- `eq_ledger`: `∑_{h < s} ℓ_{h+1} ≤ 2 ℓ_s`.
The machine assembly (the round contracts, the clock's seam, the calls) is not probed: it is the
fill's bulk, and the hosts it composes are published and gated.

**Evidence (all at the drafting base):**

| Check | Result |
|---|---|
| Overlay (`NTimeDiagonalizerOverlay.lean.txt`, eight imports) | exactly the file's two sorry warnings (overlay 278, 343); no cycle |
| Order list, roots, base sorries (on the overlay) | 81 modules, 34 roots, 23 sorried declarations in 12 modules |
| Import probe | 81 checks of 81 names, 0 errors, 0 warnings |
| Route probe | six lemmas sealed over 5 TCSlib definitions, A1's `timeConstructible_iff` a stand-in: 0 errors, 0 warnings, within the standard three axioms |
| Seal controls | 6 goals: all close unsealed, all fail sealed; control 1 is the blocker |
| Duplication probe | `exact?`: nothing for any of the five statements |
| Lint | `Diagonalization` 0 FAIL, 2 WARN over 5 files; `NTimeDiagonalizer` none |

**Semantic duplication.** The probe's lemmas are about the owned file's own definitions; searches
for published statements of the timeout deduction, the stop rule and the ladder ledger found none
(the nearest are `Cfg.stopped_iff` in `Build/StepClock`, which the machine-level timeout step will
cite, and `EmitIterEmbed.runFrom_of_halted`). The capped run must cite the clock and the
virtual-input host, never re-walk them; the copy hazards for the brief are `ExhaustiveReplay`'s
capped replays (`xr_` privates, the same clock), `TimeHierarchy/ClockLoop`, and #135's
`ClassP/BinaryArith` (Q-D6).

**Dependencies:** no in-flight file. E-D follows it in the same file. **Proved modulo:** none.
**Size:** 2,000–4,000 lines (C1-E design); a partial is the likely outcome of one session.
**Budget:** the rest of a megafill session.

## What would unblock the others

- **E-D:** A1, then E-Q's landing (same file; gate 39's carry-forward). Its brief should be drafted
  at E-Q's landing commit, with `NDCodeSimulator` settled (#161, #162 merged), since E-D imports it.
- **NF:** the controller-flavour contract of the choice writer, by the statement PR the user ruled
  on 2026-10-17 (in `Build/NDHost`, with its gate), then its fill (a W continuation). NF's brief
  then cites the contract modulo.
- **F6 (`space_universal`):** #161 (`forwardLoopCfg`'s and `rulerHostCfg`'s field equations,
  `pairEncode_drop`), and the header-ruler leaf's decision (megafill C's Q-U2: published when this
  item is briefed, or shared with U2-E).
- **H and its corollaries:** a ruling on the order (Q-D3). With the order lifted, H still needs a
  pre-ship inventory of the space-class predicates (`SPACE`, `DecidesInSpace`, `LOGSPACE` have no
  characterization lemma: lint check 8 lists them), likely a second API item like A1.
- **MIG-1's stage F (F-A to F-C):** a maintainer refresh of `campaign/items/mig1/MIG1-design.md` §5
  and §9 for the rules adopted after it (rule 10 of 2026-10-16, its 2026-10-23 scope, the
  definitions-with-lemmas rule) and the MIG-24 fold (Q-D4): which moved proofs need rewriting
  (`f2_branch_space` at least, whose rewrite needs #161's `spaceUsedByTape_eq_card`), the statement
  and home of T1's general rewind lemma, T7's two singletons in F-A's files, and how the interim
  copies are ledgered until F-D.
- **Paused, held or moved** (`savitch`, the RAM simulation, `Programs/WordRAM/Extended`, TQBF and
  the formula kit, the four record-table rows): only the user's resumption of stage 2, RD-2 or a
  record-table consumer. Not revived here.

## Open questions, with recommendations

- **Q-D1 (blocking for megafill D; the user's): A1, the chapter predicates' API PR.** Six lemmas,
  each `Iff.rfl` or `rfl`, beside their definitions in four files (statements above; replay 192
  modules; an API gate). *Recommendation:* open it now; it unblocks E-Q and
  `spaceConstructible_poly` at once, and E-D after E-Q. Then this drafting's dossiers become briefs
  with little more work (their pre-ship re-run at the issue commit, the brief text, the screens).
- **Q-D2 (note): the copying-state lemma** `Complexity.transduce_of_copy` in A1. The tail transducer
  of `spaceConstructible_poly` needs "a self-looping copying state is the identity", which is
  published twice, for particular transducers (`Complexity.KarpLipton.transduce_drop_true`,
  `CircuitComplexity/KarpLiptonPrefix.lean:87`; `transduce_fT_copy`,
  `CircuitComplexity/MeyerVerifierGlue.lean:145`; both also on #135's head). A private third copy in
  `Savitch` would be the semantic duplication the drafting brief §5 forbids. *Recommendation:* add
  the general lemma to A1 (the route probe uses it); re-point the two instances in the dedup window.
- **Q-D3 (the user's): the space hierarchy's order.** The ruling of 2026-10-15 puts H after F6's
  integration. F6 is off the headline path, has no consumer, and is blocked on #161, while H is the
  next step of the headline's critical path now that F3 has landed. *Recommendation:* lift the order
  (H and F6 own disjoint regions of `Hierarchy.lean`; each brief authorizes the union of the
  imports, as ruled), and inventory H's space-class predicates before its brief. Splitting off the
  two corollaries as their own small item is the alternative; it is an item split, so it is the
  user's call.
- **Q-D4 (the maintainer's): MIG-1's stage F.** Its design predates rule 10 and the MIG-24 fold.
  *Recommendation:* a short design refresh (the list under "What would unblock the others") before
  any stage-F brief; F-A first, after #161 merges.
- **Q-D5 (note): E-Q's eight imports** (`Mathlib.Data.Nat.Log`, `Build/StepClock`,
  `Build/InputCall`, `Build/Contract/Catalog`, `Build/Contract/Seam`, `Build/VirtualInput`,
  `Build/Primitives`, `Build/Rewind`), as a first-edit overlay; the module's only importer is the
  `Diagonalization` facade, so there is no cycle risk; the order list grows by two modules (79 to
  81) and the roots by one (33 to 34), both already in the cache's union. And
  `spaceConstructible_poly`'s one import (`ClassNP.Transducer`; the order list grows by that module;
  same Mathlib roots). *Recommendation:* authorize both in the briefs, as region (a).
- **Q-D6 (note): #135's `ClassP/BinaryArith`** (binary addition, subtraction, comparison as
  `PolyTimeComputable`, on chapter 7's head, not on the campaign branch). If it reaches the campaign
  branch before E-Q is briefed, the locator's arithmetic should call it through
  `exists_installCallTM` instead of writing private binary leaves; otherwise E-Q's brief should name
  it as a copy hazard.

## The cover, as it would be after A1 (an outline, not a draft)

Not drafted: no item is ready. After A1 the queue would be:

| # | Item | Owned file | Budget | Why here |
|---|---|---|---|---|
| 1 | `Complexity.spaceConstructible_poly` | `SpaceComplexity/Savitch` (its region; `savitch` stays sorried) | 1.5 hours | Small and fully probed (the sealed route probe proves the target with A1's statements); a session that ends early still delivers it. |
| 2 | E-Q, `Turing.NTimeDiag.exists_queryTM` | `Diagonalization/NTimeDiagonalizer` (E-D's region excluded) | the rest | Large (2–4k lines) and checkpointed (the guard and the order list's bootstrap; one locator round as a contract; the loop by `Round.iterate`; the code; `g`'s witness and `T*`; the materialization; the assembly and ledger). |

The two owned files are disjoint and unrelated (neither imports the other). Shared: the preflight,
the toolchain, one clone, one cache for the union of the two order lists' Mathlib roots (57 roots at
the drafting base; the overlays add no root), a re-bootstrap per item (183 and 81 modules on their
overlays), addendum v2.5 with megafill A's lessons (shared environment logs in every item zip,
memory logged per module, "seal not run" and "seal without failing `rfl` controls, one per sealed
definition" as checklist failures), checkpoint zips delivered as written. The agent: Codex.

## Not complete

- **No fill brief and no cover were drafted**, by the drafting brief's rule: no candidate is ready
  at the drafting base (the triage). The two dossiers hold everything a brief's pre-ship needs
  except **the copy-text screen bases**, which were not measured (a screen is a brief's pre-ship
  item, and its population is fixed with the brief); run them at the issue commit.
- The probes of the blocked items other than E-Q, E-D and `spaceConstructible_poly` were not run:
  their verdicts rest on rulings (paused, held, moved, ordered) or on in-flight PRs, which a probe
  cannot change.

## Records

- **Hashes:** every commit hash in these files was inserted by `git rev-parse` through
  `tools/subst_hashes.py` (megafill C's tool, copied unchanged into the environment folder), which
  also checks every remaining hexadecimal word against `git cat-file -t`; no hash was typed by hand.
- **Open PR heads searched (read-only fetches):** PR 161 (`lean/u2-api`) at
  `1849dae6f5427a60814d4120d9258fa4a2f46dd3`, PR 162 (`lean/startup-kit`) at
  `06d314c322a357a471d8597555964b5fa16f1674`, and PR 135 (`complexity/arora-barak-ch7`) at
  `a7433f3f73ff6cb777b1d39fcce55a02347174d7` (`evidence/open-pr-searches.txt`).
- **The moved Catalog proofs and rule 10** (MIG-1's stage F, T12): a scan of the definitions passed
  to `unfold`/`simp`/`rw`/`dsimp` in each declaration that F-A would move, up to the next
  declaration (`evidence/mig1-moved-proofs-scan.txt`): `f2_branch_space` passes `spaceUsed`,
  `spaceUsedByTape` and `visitedByTapeHead` (`Deterministic`'s definitions); `f2_counter_heads`
  unfolds `MultiTapeTM.step` and `Action.apply` for the counter machine, which rule 10 allows only
  in that machine's home file; the other seven pass none.
- **Screens:** none run (see "Not complete").

## Files (all new, under `campaign/`)

55 files.

- `campaign/fills/megafill/drafts/` (1): `megafill-D-DRAFTING-REPORT.md`
- `campaign/fills/megafill/drafts/megafill-D-env-fe666d60/` (1): `README.md`
- `campaign/fills/megafill/drafts/megafill-D-env-fe666d60/logs/` (12): `bootstrap-addendum.log`,
  `bootstrap-order.txt`, `bootstrap.log`, `cache-check.log`, `cache-get.log`, `cache-get.time`,
  `cache-store.log`, `manifest-check.log`, `mathlib-roots.txt`, `preflight.log`, `recheck.log`,
  `toolchain.log`
- `campaign/fills/megafill/drafts/megafill-D-env-fe666d60/tools/` (3): `run_probe.sh`, `runmem.py`,
  `subst_hashes.py`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/` (1): `README.md`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/a1/` (2): `A1ApiProbe.lean.txt`,
  `A1ApiProbe.out`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/ed/` (2): `EDImportProbe.lean.txt`,
  `EDImportProbe.out`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/eq/` (15): `EQDupProbe.lean.txt`,
  `EQDupProbe.out`, `EQImportProbe.lean.txt`, `EQImportProbe.out`, `EQRouteProbe.lean.txt`,
  `EQRouteProbe.out`, `EQSealControl.lean.txt`, `EQSealControl.out`,
  `NTimeDiagonalizerOverlay.lean.txt`, `base-sorries.txt`, `elab-NTimeDiagonalizerOverlay.out`,
  `fillinputs-overlay.py`, `lint-diagonalization.txt`, `order.txt`, `roots.txt`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/evidence/` (3):
  `mig1-moved-proofs-scan.txt`, `open-pr-searches.txt`, `triage-greps.txt`
- `campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/scp/` (15): `SCPDupProbe.lean.txt`,
  `SCPDupProbe.out`, `SCPImportProbe.lean.txt`, `SCPImportProbe.out`, `SCPRouteProbe.lean.txt`,
  `SCPRouteProbe.out`, `SCPSealControl.lean.txt`, `SCPSealControl.out`, `SavitchOverlay.lean.txt`,
  `base-sorries.txt`, `elab-SavitchOverlay.out`, `fillinputs-overlay.py`,
  `lint-spacecomplexity.txt`, `order.txt`, `roots.txt`
