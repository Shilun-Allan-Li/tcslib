# External audit pack — the ARM extensions (received code): fill-style gate of `8c23f3bc`

Campaign: Arora–Barak chapters 3–4 (`AroraBarakChapters3-4Plan.md` §2.5; `backlog.md` §2, "ARM
extensions + colleague sync"). Our side of the conversation is `arm-extensions-proposal.md` and
the plan's §2.5; the colleague's answer is `arm-extensions-response.md` (both attached; the
response is the colleague's account, to be checked, not trusted).

**What arrived.** The colleague Hydroxyi (Jason Dong), owner of the `LogProg` tree
`SpaceComplexity/Machines/`, extended the abstract register machine (ARM) in four ways and used
the extensions to prove ten of our sorried chapter-4 statements. The work came as one merge
commit, `8c23f3bc` ("Merge arora-barak-ch3-4 into arm-extensions; prove the remaining ARM
customers"), pushed **directly** to the campaign branch: no pull request, no statement gate, no
fill brief. Against the campaign head it merged, `069cde82`, it adds **73 Lean files** (26,078
lines) and `arm-extensions-response.md`, and modifies **8 files**: seven of ours (the two facades
among them) and Hydroxyi's own `Machines/Compile.lean`.

**This gate** is a fill-style external gate of that received work, ordered by the user. It checks
that none of our statements moved, that the new definitions on which the proofs' *interfaces*
rest mean what they claim, that the disclosed duplication is the whole duplication, and policy.
The proofs are machine-checked: the maintainer's replay compiled them (below). Do not review
tactic scripts for correctness. The gate closes on zero blockers and zero majors
(`workflow.md` §3–§4). The duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force,
and the user will give an explicit acknowledgement of the disclosed duplication at the end.

**Bundle:** `audits/arm-extensions-fill-bundle.md`. It holds:
- this pack and the standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`);
- the response and the proposal, the plan and the backlog, whole;
- all 73 added files and the 8 modified files at the received commit, with the 8 modified files'
  before state (`audits/evidence/arm-fill/before/<path>.txt`);
- every evidence file and log named below;
- the library files the interfaces rest on, and the library side of every substantive copy pair.

The list is `audits/evidence/arm-fill/BUNDLE-FILES.txt` (199 files). Omitted for size, and named
in its header: the rest of the screen population (the full 210-file screen is reproducible only
in the repository) and seven large library files whose pairs are all incidental (`Build/Catalog`,
`CookLevin/Hardness`, `Build/Loop`, `ClassNP/SAT`, `TuringMachine/Universal`,
`Robustness/SingleTape`, `Logspace/Mult`); the ledger log gives each of their pairs with line
ranges.

## What the code is (summarized from the code, not from the response)

Package sizes are MEASURED (`audits/logs/arm-fill-inventory.log`). "Public" counts comment-stripped
declaration headers.

| Package | Files | Lines | Public / private |
|---|---|---|---|
| Shared ARM kit: `Machines/{ARMReach,ARMLoops,VWord}` | 3 | 732 | 23 / 0 |
| **E1. Nondeterministic ARM**: `Machines/NARM*` (6 files) | 6 | 2,056 | 110 / 0 |
| **E2. Poly-width ARM**: `Machines/ARMWidth{,Example}` | 2 | 660 | 30 / 0 |
| **E3. Configuration codec**: `Codec/` (16 files) | 16 | 6,256 | 362 / 5 |
| **E4. Memory ARM (MARM)**: `Machines/MARM{,Compile,Time}` | 3 | 1,328 | 61 / 1 |
| `PATH ∈ NL`: `Logspace/PathWalk{,Machine,Proof}` | 3 | 1,536 | 77 / 1 |
| `PATH` hardness: `Logspace/PathHard{,Regs,Machine,Walk,Run,Decide}` | 6 | 2,254 | 154 / 0 |
| Immerman–Szelepcsényi: `Logspace/ISCount{Math,Regs,Gen*}` | 8 | 2,310 | 126 / 2 |
| `NPSPACE ⊆ PSPACE`: `SavitchARM/` | 7 | 2,301 | 149 / 0 |
| `NSPACE ⊆ DTIME(2^O(S))`: `ExpBFS/`, `ExpTime` | 7 | 3,082 | 199 / 1 |
| `TQBF ∈ PSPACE`: `ClassPSPACE/TQBFARM/` | 5 | 1,588 | 97 / 1 |
| `TQBF` hardness: `ClassPSPACE/TQBFHard*` | 7 | 1,975 | 104 / 5 |
| **Total** | **73** | **26,078** | **1,492 / 16** |

**E1. The nondeterministic ARM** (`Machines/NARM.lean:61-220`). An instruction is a
deterministic ARM instruction or `choose l₁ l₀`. A run is driven by a *choice word*, one bit per
abstract step, which deterministic steps ignore (`nastep`, `narun`). Two predicates carry the
interface:
- `NHalts A oracle x G a N`: every choice word of length exactly `N` halts the machine from `a`,
  and every live configuration on the way satisfies `G`;
- `NAns A oracle x a N b`: some word of length `N` ends with answer `b`.

`ncompileTM` (`NARMCompile.lean:188`) is the deterministic compilation of `A.detPart false` (the
machine answering `false` at `choose` labels), except at the start state of a `choose` label,
where choice bit `b` jumps to the start of `l₁` or `l₀`. `narm_space` (`NARMRun.lean:226`) turns
`NHalts`/`NAns` into exactly the shape of one input's clause of `FinNDTM.DecidesInSpace`
(`NSPACE.lean:78`): a budget `T` within which every branch halts, a space bound for every branch
of length `T`, and acceptance by some branch iff `NAns … N true`. The bridges `narm_decides_space`,
`narm_decides`, `narm_decides_poly`, `narm_decides_npspace{,_of_logspace}` (`NARMProof.lean`)
conclude `L ∈ NSPACE S`, `NL` or `NPSPACE`. They have the hypothesis shapes of the deterministic
`arm_decides*`. `NARMKit.lean` adds an inductive termination layer (`NTerm`, `NAcc`, `NSem`) and
`NSem.decides`, which produces the uniform `N`.

**E2. The poly-width ARM** (`Machines/ARMWidth.lean`). No new compiler. `arm_decides_space` is
the deterministic bridge for a general register width `W ≤ C·S` with `S ≥ 1`. The deciders' space
on every virtual input a call can form must be `≤ C·S`. Instances: `arm_decides_SPACE`
(`S ≥ logSpace`, logspace deciders) and `arm_decides_pspace` (register digits
`≤ C₀ (|x|+1)^{c₀}`, `PSPACE` deciders), with the variants `_of_logspace` and `_val` (values
`≤ 2^{C₀ (|x|+1)^{c₀}}`). There are also the class facts `LOGSPACE_subset_PSPACE` and
`SPACE_succ_pow_subset_PSPACE`. The example is `searchLang_mem_PSPACE` (`ARMWidthExample.lean`).

**E3. The configuration codec** (`Codec/`, for a fixed `N : FinNDTM Bool`).
- `Codec.InWin s C` (`Word.lean:78`): every work head and every nonblank work cell lies in
  `[-s, s]`.
- `cfgWord s C` (`Word.lean:284`) is `2s + 1` fixed-width cell chunks (cell 0 also carries the
  state and a three-valued output summary; each chunk holds the per-tape symbol and head flag at
  one position), then the input position padded to `|bits(|x|+1)|` bits, then a final `1`.
  `cfgCode` is its value.
- `cfgWord_congr` and `coreSum_eq_of_cfgWord_eq` make the code a function of the
  configuration-graph vertex `NDTM.coreSum`, injective on window-bounded configurations.
  `cfgCode_lt` bounds codes by `2^{codeK N·(s + logSpace |x| + 1)}`, and `decodeCfg_cfgCode`
  gives the decoder.
- Four code languages over `⟨x, ⟨bits c, bits s⟩⟩` (`Langs.lean:62-86`):
  - `validLang`: the code of some window-bounded configuration;
  - `initLang`: the code of the initial configuration;
  - `acceptLang`: the code of a window-bounded halted configuration with output exactly `[true]`;
  - `stepLang`: a pair of window-bounded codes joined by `CfgStep`, i.e. one step under some
    choice bit.

  Each is in `LOGSPACE` (`Deciders.lean:193,221,379`, `StepDecider.lean:293`), by deterministic
  ARMs with `N`'s table hard-wired.
- The bridge `mem_iff_codeChain` (`Bridge.lean:235`): if `N` decides `L` in space `sp` and
  `s ≥ sp |x|`, then `x ∈ L` iff there is a chain of at most `configBound |x| s` step pairs from
  an initial code to an accepting code, all codes below the width bound.

**E4. The memory ARM** (`Machines/MARM.lean`). It is the ARM plus a tape of bits that starts at
`0`, with four instructions: `mread` branches on the bit under the head, `mset` sets it to `1`,
and `mleft`/`mright` move the head. Bits are never reset. `mcompileTM` (`MARMCompile.lean:141`)
adds the memory as the last work tape.
- `runFrom_count_eq` (`MARMTime.lean:214`): a run whose last tape is only ever written with
  `true`, with the other heads in `[-B, B]` and the last head in `[-P, P]`, is at its final
  configuration by a configuration-count time.
- `marm_dtime` (`MARMTime.lean:444`): a halting MARM with logspace deciders, register digits
  `≤ W |x|` and memory head in `[-P|x|, P|x|]` is computed by one `FinTM` in time
  `2^{C (W|x| + logSpace|x| + 1)} · (P|x| + 1)²`.

**Hydroxyi's own file.** `Machines/Compile.lean` gains `compile_correct_from`, the correctness of
the compiled machine from the seam of an arbitrary program configuration. `compile_correct` keeps
its statement and docstring, and is now a three-line corollary.

**The customers** (our sorried targets, now proved), with the route as delivered:
- `PATH_mem_NL` (`Logspace/Path.lean`): `PATH = pathRawLang` (`PATH_eq_pathRawLang`, new, same
  file), and the ND ARM `pathA` walks at most `n` guessed vertices (`pathRawLang_mem_NL`).
- `PATH_NLComplete` (same file): membership as above. Hardness is `pathRawLang_NLHard`: the
  graph on `2^E` vertices of codes (`PathHard.red`), implicitly logspace by a deterministic ARM
  over the codec deciders.
- `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq` (`Logspace/ImmermanSzelepcsenyi.lean`):
  `compl_mem_NSPACE` for `S ≥ logSpace`. One ND ARM, `ISGen.igA`, runs inductive counting over
  codes at radii `0, 1, …` and stops at the first radius whose count equals the previous one.
  `compl_mem_NL` is its case `S = logSpace`.
- `PSPACE_eq_NPSPACE` (`Savitch.lean`): our `PSPACE_subset_NPSPACE`, and `NPSPACE_subset_PSPACE`.
  The latter is a poly-width ARM that evaluates the midpoint recursion over codes with an explicit
  stack. It does not use our sorried `savitch`.
- `TQBF_mem_PSPACE` (`ClassPSPACE/TQBF.lean`): `TQBFARM.truth_mem_PSPACE`. It validates the whole
  input, then walks the AND/OR tree depth first, the assignment held as a binary stack register.
- `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` (same file): `TQBFHard.PSPACE_polyTimeReducible_TQBF`.
  It builds the ∀-folded `ψᵢ` over code blocks. The matrix is one polynomial-time predicate,
  turned into a circuit by the uniform tableau and into a CNF by Tseitin, with the gate variables
  quantified after the prefix. The RD-2 `ConfigCodec` and `FormulaKit` lemmas are not used.
- `NSPACE_subset_exp_dtime` (moved, see below; `ExpTime.lean`, new):
  `NSPACE_subset_exp_dtime_of_le`, a MARM that searches breadth first over codes at growing radii,
  timed by `marm_dtime`.
- `compile_correct` (`Machines/Compile.lean`; not a `sorry`, re-proved): a corollary of
  `compile_correct_from`.

So **nine of the brief's ten "filled" targets were sorries before**. `compile_correct` was
already proved. The tenth `sorry` that fell is `NSPACE_subset_exp_dtime`, at its new home
(MEASURED, `audits/logs/arm-fill-census.log`).

## Provenance (MEASURED from git unless marked)

- **The commit.** `8c23f3bc314abb6c2c55cd2ce218e9771d6e41e0`, author Hydroxyi
  `<jasondong1@berkeley.edu>`, 2026-10-14 03:45 −0700. Parents: `c0cfc92d` (first, Hydroxyi's
  branch `complexity/arm-extensions`) and `069cde82` (second, the campaign head). The campaign tip
  `dc891632` is our PR #88 (H2-M) merged on top of it; H2-M touches only `TuringMachine.lean`,
  `Build/StepBlock.lean` and `CodeSimulator.lean`. None of the three is in the upstream closure of
  any of the 81 changed modules (`audits/logs/arm-fill-imports.log`). All 81 received `.lean`
  files are byte-identical at `8c23f3bc` and at the tip.
- **Two rounds; the second exists only in the merge commit.** `c0cfc92d` (2026-10-12, one commit
  cut at `50678912`) is round one: the ND ARM, the poly-width ARM, the codec, `PATH ∈ NL` and
  `PSPACE = NPSPACE`. Of the 82 changed paths, 33 are byte-identical to `c0cfc92d`. The merge
  commit itself adds 36 Lean files that neither parent has: MARM (3), `ExpBFS` and `ExpTime`
  (7), `PathHard*` (6), `ISCount*` (8), `TQBFARM` (5) and `TQBFHard*` (7). It changes 13 more
  paths, 12 Lean files and the response (`audits/evidence/arm-fill/merge-origin.txt`). Round two
  was therefore never a reviewable commit of its own.
- **No PR and no gate.** It was pushed directly to the campaign branch. It had no statement gate,
  no brief and no zip delivery (`workflow.md` §4). The response says so ("we went straight to
  filled proofs") and invites this audit.
- **Build claims are theirs.** The response claims `lake build` (4,248 jobs, exit 0) and axiom
  prints within the standard three. `lake build` is banned on campaign branches (`workflow.md`
  §6). The pack's author ran no Lean. **The maintainer's replay** (MEASURED, 2026-10-14; run by
  the user with the maintainer's script, `audits/logs/arm-fill-replay.log`): C1's landing branch
  merged with the tip `dc891632`, 147 modules, the downstream closure of C1's ten modules and of
  this merge's 82 changed files; it contains all 117 modules of this gate's closure; **0
  failures**. The root `TCSlib` module is outside the olean snapshot and was not replayed. The
  axiom probe below ran against that replay's oleans. These are maintainer execution claims.

## User decisions (2026-10-14, binding; verify that the pack and records reflect them)

1. **This gate**: a fill-style external gate of the received work, with the user's explicit
   acknowledgement of its disclosed duplication at the end.
2. **Payback in a separate PR, after the B6 hosts land, with its own gate.** That PR makes public
   `InWindow`, `runWith_take_inWindow`, the accept⇒membership argument (all in `ConfigGraph.lean`),
   `values_getD_eq_of_eval_tseitinGates` (`DAGCircuitSat.lean`) and `inWindow_of_coreSum_eq`
   (`ConfigGraph.lean`). It deletes the dead private `s1b_*` block in `ConfigGraph.lean` and
   retires the copies.
3. **RD-2's fill briefs are held.** RD-2's `ConfigCodec` and `FormulaKit` now have no consumer.
4. **Stage 2's remaining work is paused.**

## What changed in our files (verify; `audits/logs/arm-fill-freeze.log`)

- **Statement changes: none.** Both the maintainer's `declfreeze.py` and the independent
  `freeze2.py` find every public statement of the 8 files unchanged, as exact text.
- **`sorry` → proof:**
  - `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` (`TQBF.lean`);
  - `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq` (`ImmermanSzelepcsenyi.lean`);
  - `PATH_mem_NL`, `PATH_NLComplete` (`Path.lean`);
  - `PSPACE_eq_NPSPACE` (`Savitch.lean`).
- **Proved → re-proved:** `compile_correct` (`Compile.lean`). Its statement and docstring are
  byte-identical; its body is now `compile_correct_from` at the initial configuration.
- **Moved:** `NSPACE_subset_exp_dtime`, `NL_subset_P` and `polyTimeReducible_of_mem_NL`, from
  `ConfigGraph.lean` to the new `ExpTime.lean`.
- **Public additions to our files:** `Path.lean` gains `length_adjWord`, `getD_flatMap_rows`,
  `adjWord_getD` and `PATH_eq_pathRawLang`. Hydroxyi's `Compile.lean` gains
  `compile_correct_from`.
- **Privates:** none added, removed or changed in the 8 files.
- **Docstrings rewritten:**
  - the sorried targets, except `TQBF_PSPACEComplete` (unchanged): eight;
  - the three moved theorems;
  - the module docstrings of `TQBF`, `ConfigGraph`, `Path`, `ImmermanSzelepcsenyi`, `Savitch`,
    `Compile` and both facades.
- **Imports added:** `TQBF` +2, `ImmermanSzelepcsenyi` +1, `Path` +2, `Savitch` +1, and the
  `SpaceComplexity` facade +61. None were removed.
- **Facades:** comment-stripped code is identical apart from the added imports. `ClassPSPACE.lean`
  is identical outright: it adds Contents lines only, and no imports.
- **Dead code left:**
  - `ConfigGraph.lean`'s 16 private `s1b_*` declarations are now referenced by nothing; the moved
    body used three of them;
  - `TQBF.lean`'s 45 private `b4m*` declarations are referenced by nothing outside the block.
- **Sizes (lines):**
  - `TQBF` 3,305 → 3,245; `ConfigGraph` 930 → 777;
  - `Path` 136 → 210; `ImmermanSzelepcsenyi` 116 → 120;
  - `Savitch` 131 → 139; `Compile` 266 → 296;
  - the facades: `ClassPSPACE.lean` 32 → 37, `SpaceComplexity.lean` 130 → 244.

**The move is not byte-identical.** The response says the three theorems "moved, byte-identical".
MEASURED (`freeze.log` Part D): **statements byte-identical; docstrings changed in all three**:
- `NSPACE_subset_exp_dtime`: the statement prose has `⋃ c : ℕ` for `⋃ c`; the sketch is rewritten
  for the new route; the S1b fill appendix is removed; the body is no longer a `sorry`;
- `NL_subset_P`: the sketch is rewritten, the fill appendix removed, and **the `[Bon26]` citation
  dropped**;
- `polyTimeReducible_of_mem_NL`: the fill appendix removed, its last sentence merged into the
  sketch.

`NL_subset_P`'s and `polyTimeReducible_of_mem_NL`'s bodies are byte-identical. No `.lean` code
referred to the three names except a docstring mention in `Logspace/Reductions.lean:67` (name
unchanged). Records that still give the old home: plan row B2, backlog MIG-19, several briefs,
and the historical axiom probes `audits/evidence/fills-{6,7,8}/AxF*.lean.txt`, which import
`ConfigGraph` and print `NSPACE_subset_exp_dtime`. Re-run at the tip, those probes would no
longer resolve the three names.

**Citation tags of the rewritten docstrings** (MEASURED, `freeze.log` Part E):
- No `[AB09, …]` location tag was dropped from any target.
- Dropped: `[Bon26]` (`NL_subset_P`), and a bare `[AB09]` mention in `compl_PATH_mem_NL`'s old
  sketch ("the verifier of [AB09]'s proof").
- Added: `[AB09, Theorem 4.14]` (`PSPACE_eq_NPSPACE`); `[AB09, Remark 6.7]` and
  `[AB09, Lemma 6.11]` (`TQBF_PSPACEHard`).

## Evidence (bundle paths)

- Inventory: per-file lines, maximum line width, public and private counts, imports; the
  modified files before and after: `audits/logs/arm-fill-inventory.log`.
- Import graph: acyclicity; the upstream closure (206 modules, 133 of them library); the
  downstream closure; the absence of the H2-M files; the replay order:
  `audits/logs/arm-fill-imports.log`.
- Statement freeze, Parts A–E: `audits/logs/arm-fill-freeze.log`, with the code-only and full
  diffs `audits/evidence/arm-fill/modified-{codeonly,full}.diff.txt` and the before state
  `audits/evidence/arm-fill/before/TCSlib/…/<file>.lean.txt`.
- Merge origin of the 82 paths: `audits/evidence/arm-fill/merge-origin.txt`.
- Forbidden-construct screen: `audits/logs/arm-fill-forbidden.log`.
- Copy-text screens:
  - the full population (210 files): `audits/logs/arm-fill-screen.log`, with the population
    `audits/evidence/arm-fill/screen-population.txt` and its labels
    `screen-population-labels.txt` (flattened name, path, SHA-256);
  - the supplement (the 73 files plus 4 named sources outside the closure):
    `audits/logs/arm-fill-screen-supplement.log`, with
    `audits/evidence/arm-fill/screen-supplement-population.txt`;
  - the 73 added files alone: `audits/logs/arm-fill-screen-added-only.log`.
- The disclosed-copy table, from the response and the files' own disclosures:
  `audits/evidence/arm-fill/disclosed-copies.tsv`.
- The duplication ledger: `audits/logs/arm-fill-ledger.log`.
- Policy checks and the style lint on copies: `audits/logs/arm-fill-policy.log`,
  `audits/logs/arm-fill-lint.log`.
- The sorry census (downstream closure before and after, and the sorried names upstream):
  `audits/logs/arm-fill-census.log`.
- The axiom probe, run by the maintainer against the replay's oleans, and its self-screen:
  `audits/evidence/arm-fill/AxARM.lean.txt`, `audits/logs/arm-fill-axioms.log`,
  `audits/logs/arm-fill-axprobe-screen.log`. The replay log: `audits/logs/arm-fill-replay.log`.
- `machine-library-design.md` §14, verbatim, for brief point 5:
  `audits/evidence/arm-fill/design-14-extract.md`.
- The pack author's scripts and the maintainer tools used: `audits/evidence/arm-fill/scripts/`,
  `audits/evidence/arm-fill/tools/`.

## Duplication ledger (MEASURED screen; classification by the pack's author)

**Method.**
- The screen is the repository's `audits/evidence/retrofit/copy-text-screen.py`, unmodified, at
  its own threshold: a declaration reproduces at least half of another's body of at least 60
  characters.
- **It was run on byte-identical copies named by their flattened paths.** The screen labels a
  file by its basename and skips a pair whose `basename::name` coincide. Ten basenames repeat in
  the population (`Machine.lean` four times, `Run.lean` three times, …), so with the repository
  paths it silently drops true cross-file pairs. The control: over the 73 files alone, 343 pairs
  with flattened names against 326 with repository paths; the 17 hidden pairs are listed in
  `arm-fill-screen-added-only.log`, e.g. `SavitchARM/Machine::shI` = `ExpBFS/Machine::shI`, 100%.
  The tool should key on full paths; that is an open issue, not fixed here.
- The populations:
  - full: 210 files, 4,383 declarations screened, 4,119 pairs, 2,147 s;
  - supplement: the 73 plus `CookLevin.lean`, `CookLevin/Hardness.lean`, `Logspace/Mult.lean`
    and `Inclusions.lean`, the named sources outside the closure; 159 s.

  The ledger reads the union of both.
- Two measures per copy-side declaration:
  - **whole body**, the CH34-D4 precedent, conservative: it counts the whole of a long proof
    that reproduces half of a short one;
  - **shared text**: the screen's tiled overlap with the largest source, capped at the body.

  Denominators: the 73 files' 17,227 comment-stripped code lines and 421,911 extracted body
  characters.

**Pairs touching an added file in another file.** 313 ordered pairs; unordered:
- **120 with library files**: 15 in disclosed families, 105 not;
- **103 among the added files themselves**, in 45 families.

**(a) The disclosed copies of existing material** (`disclosed-copies.tsv`; screen view in
`arm-fill-ledger.log`, "The disclosed families"). Each copy is followed by its original and the
screen's similarity.
- **D1.** `Codec/Word.lean:78-79` `InWin` ← `ConfigGraph.lean:146-147` `InWindow` (private).
  Below the screen's 60-character floor; textually identical. A public equivalent already exists,
  `Turing.Cfg.InWindow` (`Build/CfgRecord.lean:100`, in `Word`'s import closure), and ConfigGraph's
  private `inWindow_iff_cfgInWindow` proves the two agree.
- **D2.** `Codec/Bridge.lean:119-136` `inWin_runWith_take` ← `ConfigGraph.lean:323-340`
  `runWith_take_inWindow` (private), 81% / 80%.
- **D2h.** Its four private helpers, re-proved under the same names in `Bridge.lean:66-110`:
  `take_succ_action`, `abs_lt_card_visitedWith`, `mem_visitedWith_of_ne_none` and
  `visitedWith_take_subset` (`ConfigGraph.lean:262-316`), 77–100%. They are disclosed in
  `Bridge.lean`'s docstring, **not in the response**.
- **D3.** `Bridge.lean:151-163` `mem_of_acceptsWithin` ← the backward branch of
  `ConfigGraph.lean:533-551` `DecidesInSpace.mem_iff_acceptsWithin_configBound`, 66% / 88%.
- **D4.** `TQBFHardTseitin.lean:57-75` `values_getD_eq_of_eval_tseitinGates` (public, same
  name) ← `DAGCircuitSat.lean:322-340` (private, Hydroxyi's file), 100%.
- **D5.** `ExpBFS/Radius.lean:63-69` `inWin_of_coreSum_eq` ← `ConfigGraph.lean:343-347`
  `inWindow_of_coreSum_eq` (private). Re-proved, so no pair at the threshold.
- **D6.** `ClassPSPACE/TQBFARM/Semantics.lean:64-157`, public twins of our dead private `b4m*`
  block in `TQBF.lean:2482-2581`: `synStep`, `synOK`, `synStep_matrix`, `synOK_spec`,
  `truthAux_nil`, `truth_of_not_synOK`, `repr_of_synOK`, at 83–100% (`synOK` is below the
  floor). **The response says "three of its lemmas"; there are seven declarations, six of them
  at the threshold, with no in-file disclosure.**
- **D7.** `Codec/Engine.lean:229-341` `decodeStride_loop` ← `Logspace/InputAccess.lean:1034-1144`
  `boundedDecode_loop` (ours, public), 96% / 91% and 113 code lines; `Engine.lean:61-79`
  `incChain` ← `InputAccess.lean:621-646` `arm_increments` (ours, private), 81% / 91%. Both are
  disclosed in `Engine.lean`'s docstring ("a shared generalization of both is requested"), **not
  in the response**.

Total disclosed: 18 declarations, about 304 code lines (1.8%), 7,712 whole-body / 6,930
shared characters (1.6–1.8%).

**(b) Undisclosed copies of existing material.** There are 47 copy-side declarations. By whole
body they are 1,096 code lines (6.4%) and 29,092 characters (6.9%); by shared text, 9,963
characters (2.4%). Twelve share at least 150 characters with one source (the pack author's cut
between a copied argument and a shared tactic idiom):
- `ARMWidth.lean:104-179` `arm_decides_space`, 1,681 shared with `ARMProof.lean`'s `arm_decides`
  (87% of its own body);
- `MARMTime.lean:444-556` `marm_dtime`, 1,652 shared with `arm_decides`;
- `NARMProof.lean`: `narm_decides` (646), `npre_of_npreS` (642), `narm_decides_space` (583),
  all against `arm_decides`, and `narm_decides_poly` (270, against `ARMKit`'s
  `arm_decides_poly`);
- `Codec/Engine.lean:83-101` `decChain`, 423 shared with `InputAccess`'s private
  `arm_increments`. It is the decrement sibling of D7's `incChain`; `Engine` discloses only
  `incChain`;
- `MARMTime.lean:214-332` `runFrom_count_eq`, 314 shared with `ConfigCount`'s `coreCode_inj`;
- `NARMCompile.lean:139-163` `spaceUsedWith_le_of_ranges`, 240 shared with `Compile`'s
  `spaceUsed_le_of_ranges`;
- `MARM.lean:180-200` `MReach.trans`, `MReach.halt` (200, 233), 99% twins of `ARMProof`'s
  `AReach.trans`/`AReach.halt`. The library already repeats this pair in `DblLang`, `Parse2` and
  `ParseCmp`;
- `TQBFHardParams.lean:175-187` `length_lbStep`, 207 shared with `ClassNP/PolyTimeBlockLoop`'s
  `length_xorPairStep_le`.

Most sources are Hydroxyi's own `Machines/` files: `ARMProof`, `ARMKit`, `Compile`,
`ConfigCount`. The bank-and-precondition plumbing of `arm_decides` is re-derived four times.
The other 35 share 60–148 characters each. They are tactic idioms (`induction` on runs,
`getD`/`drop` index lemmas, `foldr_max_le`, which the library already has three times, and
polynomial-time closure one-liners); the auditor should confirm that they are incidental.

**(c) Internal duplication among the 73 files** (undisclosed; not a copy of existing material).
103 unordered pairs in 45 families. The largest:
- register-machine instruction blocks and their run lemmas, repeated per machine: `shI`,
  `cpI`, `dmI`, `mvI`, `cp_run`, `dm_run`, `sh_run`, `sb_run`, `hv_run`, `preS_A` and `Bd.toV`
  across `TQBFARM/Machine`, `SavitchARM/{Machine,Run}`, `ExpBFS/{Machine,Run}` and
  `PathHardMachine`, many at 100%;
- the oracle-call lemmas `orc_bit`/`orc_len` in `Codec/Run`, `TQBFARM/Machine`, `PathHardRegs`
  and `ExpBFS/Main`;
- `Codec/Layout::layout_run` and `Layout2::layout2_run`: 4,139 shared characters, 76%;
- `NARMCompile` against `MARMCompile`: `detPart_step_choose`/`detM_step_mem`, `ndet_live`/
  `mdet_live`, `ndet_halt`/`mdet_halt`, `NBox`/`MBox`, `ncompileTM_tr`/`detM_tr`;
- `ExpBFS/Relax`'s three run lemmas against `ExpBFS/Search` and `Main`, and `ISCountGen`'s
  walk, stage and loop lemmas;
- `arm_decides_space` against `narm_decides_space` (76%).

**(d) Totals and the one-fifth rule** (`workflow.md` §4: past one fifth, a `backlog.md` §1
human-review item is opened before the pack ships).
- Copies of existing material, (a) and (b): 63 declarations, 1,396 code lines (8.1%); 36,804
  whole-body (8.7%) or 16,893 shared characters (4.0%).
- Everything, internal included: 151 declarations, 3,731 code lines (21.7%), 108,250 whole-body
  characters (25.7%), 42,676 shared (10.1%).
- Net, each internal family minus one original: 134 declarations, 3,303 code lines (19.2%),
  96,272 whole-body characters (22.8%), 37,198 shared (8.8%).

**The received code as a whole is past one fifth on the whole-body measure and below it on
shared text.**

Files past one fifth:
- on the whole-body measure: 33 of the 73 (listed in the ledger);
- on shared text: 14, namely `TQBFARM/Machine` (29.8%), `TQBFARM/Semantics` (55.2%, D6),
  `TQBFHardTseitin` (28.0%, D4), `Codec/Bridge` (40.2%, D2/D2h/D3), `Codec/Engine` (40.3%,
  D7 and `decChain`), `Codec/Layout` (45.2%), `Codec/Layout2` (43.7%), `ExpBFS/Relax`
  (27.5%), `Machines/ARMWidth` (27.7%), `MARM` (24.0%), `MARMCompile` (24.8%), `NARMCompile`
  (34.5%), `NARMProof` (38.3%), `VWord` (44.2%; a 109-line file);
- on library copies alone, by shared text: `TQBFARM/Semantics`, `TQBFHardTseitin`, `Bridge`,
  `Engine`, `ARMWidth`, `MARM`, `NARMProof` and `VWord`.

The maintainer opened it before this pack shipped: `backlog.md` §1 **ARM-1** (2026-10-14,
records commit `351b8d57`), which also records the screen's basename defect.

**(e) Payback.** The user's decision 2, a separate PR after the B6 hosts land with its own gate,
covers D1–D5. The helpers D2h are subsumed: once `runWith_take_inWindow` is public, they go
with it. D1 might instead standardize on the existing public `Turing.Cfg.InWindow`. The
decision does not cover:
- D6 (the natural fix is to delete our dead `b4m*` block);
- D7 and `decChain` (`InputAccess` generalizations, which `Engine` requests);
- the undisclosed copies of Hydroxyi's own `Machines/` plumbing (b);
- the internal families (c).

The user's acknowledgement at the end is of the disclosed duplication. Ruling on whether (b) and
(c) need the same is the auditor's job (brief point 6).

## Brief for the auditor

Restate each definition below **in your own words before reading its docstring**, then compare
with the docstring and with [AB09] (§4.1–4.3, Theorems 4.2, 4.13, 4.14, 4.18, 4.20, Corollary
4.21). Report any daylight. Attempt at least **six adversarial instantiations** covering failure
modes 1–5 of `audits/TEMPLATE.md`; candidates follow point 5. Points to rule on:

1. **Statement integrity of our targets.** Re-establish from the before copies, the after files
   and the diffs that no statement of the 8 modified files changed. The targets: the nine
   sorried ones, `compile_correct`, and the three moved theorems at their new home. Confirm
   that each target's after-body proves exactly the frozen statement, with no new hypothesis
   arriving through a `variable` or a changed `open`. The code-only diffs show the only non-body
   code changes: imports, and the moved and added declarations. Confirm the classification
   above, including that `compile_correct` was not a `sorry`.
2. **The move to `ExpTime.lean`.** Is the import-cycle rationale right? `Codec/Word.lean`
   imports `ConfigGraph`, and the proof needs the codec. Is the new home acceptable for
   statements that our records and earlier audits place in `ConfigGraph`? Rule on the
   non-identical docstrings, against the response's "byte-identical" claim and against
   `workflow.md`'s statement freeze (docstrings are trusted surface, `policy.md` §2). Rule on
   the dropped `[Bon26]`: the old text recorded that the prior art was design context only;
   should the provenance note survive the new route? Say which stale records must be corrected.
3. **The docstring rewrites of our sketches** (`freeze.log` Part E). Check for each target:
   - its opening statement prose still says what the frozen statement says (in particular
     `TQBF_PSPACEHard`'s new "every PSPACE language Karp-reduces in polynomial time");
   - the new sketch describes the proof that is now there (`policy.md` §3, **Synchronization**),
     with no claim the code does not bear out;
   - every location tag is kept, and the added ones are right (`[AB09, Theorem 4.14]` on
     `PSPACE_eq_NPSPACE`; `[AB09, Remark 6.7]`, `[AB09, Lemma 6.11]` on `TQBF_PSPACEHard`).

   In particular, `NSPACE_compl_eq`'s sketch now records a route deviation from [AB09,
   Exercise 4.11]: the window is found by growing, not computed from constructibility. Is it
   declared adequately?
4. **Faithfulness of the interfaces.** Each item below is what a proof's interface rests on.
   Restate it, then check it.
   - *E1, the ND ARM's compilation with space carried over.* Is `narm_space` the per-input clause
     of `FinNDTM.DecidesInSpace`, all-branch halting and all-branch space included? Is the
     length-exactly-`N` quantifier of `NHalts`/`NAns` safe? It relies on halted configurations
     being fixed (`narun_halted`). Can an abstract branch halt with no answer (`res = none`), and
     does `narm_run` then still give every compiled branch an output `out ++ [b]`? (The pack's
     author reads `ARM.lean:116-131` as: every halting instruction, `ret`, `valP` or `valQ`,
     sets an answer.) Is `choose` really one compiled step, and does `detPart false` matter
     anywhere but the overridden start states? Are `narm_decides*`'s hypotheses the honest ND
     twins of `arm_decides*`?
   - *E2, the poly-width ARM.* In `arm_decides_space`, is the decider-space hypothesis `hs`
     quantified over every virtual input a call can form? Are `arm_decides_pspace` and `_val`'s
     width and value bounds polynomial in the right variable? The pack's author finds no earlier
     `LOGSPACE ⊆ PSPACE` in the library, and `SPACE_succ_pow_subset_PSPACE` is derived from the
     existing `space_poly_subset_PSPACE`. Should these class facts live in `SpaceClasses.lean`?
   - *E4, MARM's time bridge.* Is the configuration count of `runFrom_count_eq` right? Its
     factors are states, input positions, the non-memory tapes on `[-B, B]`, heads, and the
     number of `1`s of the memory in `[-P, P]`, which is valid because the memory only grows.
     Is the hypothesis `hwrite` (the last tape is written only with `true`; blank `none` reads as
     `0`) the monotonicity the count needs? Does `marm_dtime`'s bound
     `2^{C(W + logSpace + 1)}·(P + 1)²` give [AB09, Theorem 4.2(iii)]'s `2^{O(S)}` after
     `ExpBFS`'s choices of `W` and `P`?
   - *E3, the codec's correspondence with configurations.* Is `coreSum` (the vertex) exactly what
     the code determines on window-bounded configurations: state, output summary, windowed
     tapes, heads, input position? Is acceptance ("halted with output exactly `[true]`")
     decidable from the summary, as `acceptLang` assumes? Is `stepLang`'s `CfgStep` the
     configuration-graph edge of `ConfigGraph.lean`? Does `mem_iff_codeChain` need `s ≥ sp |x|`
     only for `⇒`? Do `validLang`/`initLang`/`acceptLang`/`stepLang` accept anything malformed?
   - *`compile_correct_from`*: is `seam c₀` of an arbitrary program configuration a meaningful
     start, and is the statement the natural generalization?
   - *The customers' own definitions*: `pathRawLang`/`rawEdge` against `PATH`/`GraphReach`
     (`PATH_eq_pathRawLang`); `PathHard.red` and its vertex numbering, codes at `c + 2` below
     `2^E`; the window-growing stop rule of `ISGen` (`ExpBFS.mem_iff_of_card_eq`,
     `card_rset_succ_of_le`); `SavitchARM`'s `Reach`; `TQBFHard`'s `ψᵢ` blocks and `predB`.
5. **Process and hosts** (`policy.md` §1, **Hosts come first**; review checklist item 8;
   `machine-library-design.md` §14). The delivery introduces public hosts that are not in the
   §14 registry and had no statement gate:
   - a depth-first AND/OR walk (`TQBFARM`; compare H1);
   - a BFS over codes (`ExpBFS`; compare H4);
   - a midpoint recursion (`SavitchARM`);
   - inductive counting (`ISCount*`);
   - a new machine model (MARM);
   - a fifth configuration encoding (the codec).

   It also adds reachability notions: `WalkLe`, `SavitchARM.Reach`, `TQBFHard`'s
   `mid_iff_steps`, `ExpBFS.RCode`. Each customer host has exactly one consumer. Rule whether
   this conforms to the hosts rule, or which hosts must be registered and gated before a second
   consumer (`workflow.md` §4, **Hosts in briefs**).

**Adversarial instantiations** (attempt at least six; add your own):
- (2) a NARM whose start label is `choose l₀ l₀`: can any `N` satisfy `NHalts` (at `N = 0` the
  start is live)?
- (3) `x = []`: `logSpace 0 = 1`, and register digits `|bits (v + 1)| ≥ 1`. Are the bridges'
  width hypotheses satisfiable at length 0?
- (1) a branch that halts early under a word of length `N`: is it counted once, with its answer?
- (2) the codec at `s = 0`: a configuration with a nonblank cell at position `1` is not `InWin`.
  Can such a configuration still get a code that collides with a window-bounded one, and does
  any language accept it?
- (3) the stop rule: try to build a decider whose reachable counts agree at radii `s` and `s+1`
  but grow at `s + 2`. The argument: a step moves each head at most one cell.
- (4) MARM with `P = 0` or `W = 0`: are the hypotheses still satisfiable, and does the bound
  degenerate?
- (2) `TQBF` on junk: odd length, no separator, trailing garbage after a valid prefix. Each must
  be accepted (`QBF.decode`'s true fallback). Does `truth_mem_PSPACE` validate the whole input?
- (1) `PATH` with `n = 1`, `A 0 0 = false`, `s = t = 0`: a member by reflexivity. `n = 0`: no
  instance.
- (3) `PathHard.red`: the largest code `c < 2^{K(s + logSpace|x| + 1)}` against `2^E`, with
  `E = K(c₀ + 1)ℓ + K + 2` and `ℓ = |bits(|x| + 1)|`.
- (5) any copy the ledger misses (rerun the screen; see the ledger section).

6. **The duplication ledger** (failure mode 5). Verify the ledger above independently, and do
   not just check its arithmetic:
   - Rerun the screen on the bundled added files, with flattened names (the 73 alone take about
     80 s), and against the bundled library files. Confirm each reported pair and its
     classification against `disclosed-copies.tsv`.
   - The response names D1–D5, and D6 as "three" twins. The files also disclose D2h and D7, and
     D6 has seven members. Is the disclosure adequate?
   - Rule on the twelve substantive undisclosed copies (b), mostly re-derivations of
     `arm_decides`'s plumbing in Hydroxyi's own tree. Are they debt that needs the same human
     acknowledgement? Rule also on whether the 35 small overlaps are really incidental.
   - Rule on the internal duplication (c): register kits, oracle-call and run lemmas repeated per
     machine, and `Layout`/`Layout2`. It is not copied from existing material, but it is
     undisclosed, and it takes 14 files past one fifth on shared text.
   - Say whether decision 2's PR covers the disclosed families, and name what it leaves: D6, D7,
     (b) and (c).
   - Check the method itself: the screen's basename defect, and the two measures.
7. **Policy** (`audits/logs/arm-fill-policy.log`, `arm-fill-lint.log`):
   - lines over 100 characters: 42 in 17 added files, and 2 introduced in the
     `SpaceComplexity.lean` facade;
   - module docstrings without `## Main definitions` (13 files) or `## Main results` (2 files);
   - two proofs over 20 lines without a sketch (`TQBFHardSemantics.lean:160, 193`);
   - the lint's 12 FAIL: the `ClassPSPACE.lean` facade does not import its 12 new children,
     which are reached through `TQBF.lean`;
   - helper placement: generic list lemmas in `Path.lean` and `VWord.lean`, `NSPACE.mono_const`
     in `NARMProof.lean`, class inclusions in `Machines/ARMWidth.lean`;
   - two namespaces for one package (`Complexity.ExpBFS`, `Complexity.LogProg.ExpBFS`);
   - 1,492 new public declarations, most of them register-file plumbing in inner namespaces;
   - scoped tactic macros and `set_option hygiene false` (forbidden screen, below);
   - `[AB09]` attribution on every textbook-level result (53 tagged publics).

   File sizes are reported only: size is never a reason to split (user, 2026-10-11).
8. Report anything else the code, the response or this pack misstates, in the standard table.

## Repository-side attestations (verify or challenge)

Source facts (checkable in the bundle) are kept apart from maintainer execution claims. MEASURED
= computed by a script over the checkout, log attached. ESTIMATE = a judgement or partial check.
NOT RUN = pending.

- **Identity** (MEASURED): the 81 received `.lean` files are byte-identical at `8c23f3bc` and at
  the tip `dc891632` (`cmp`). The 82-path diff `069cde82..8c23f3bc` has 74 additions (73 `.lean`
  and the response) and 8 modifications.
- **Freeze** (MEASURED, `arm-fill-freeze.log`): as listed above. The two freeze scripts agree.
  No statement changed. Privates in the 8 files are unchanged. No `variable`, `open`,
  `namespace`, `section`, `end` or `set_option` line changed in the 8 files
  (`modified-codeonly.diff.txt`).
- **Move** (MEASURED): statements byte-identical; docstrings differ for all three; bodies
  identical for `NL_subset_P` and `polyTimeReducible_of_mem_NL`.
- **Imports** (MEASURED, `arm-fill-imports.log`):
  - the graph of 707 modules (with the root) has no cycle;
  - every new module is reachable from `TCSlib.lean`;
  - the upstream closure of the 81 changed modules (237 modules) contains neither
    `TuringMachine/CodeSimulator` nor `Build/StepBlock` nor the `TuringMachine` facade;
  - the downstream closure of the 81 is 117 modules plus the root.
- **Sorry census** (MEASURED text scan, `arm-fill-census.log`): over that downstream closure,
  37 `sorry` tokens before and 27 after. Exactly the 10 listed above fell. The 27 left are RD-2's
  21 in `TQBF.lean`, `savitch` and `spaceConstructible_poly` (`Savitch.lean`), and the 4
  hierarchy statements (`Hierarchy.lean`). The 73 added files contain no `sorry`, not even in
  prose.
- **No sorried dependency, statically** (ESTIMATE, text-level): the upstream closure of the 81
  changed modules holds 54 sorried declarations, in `Nondeterministic`, `NondeterministicSpace`,
  `Build/RecordTable`, `FormulaKit/{Gate,Emit}`, `TQBF`, `Savitch` and `Hierarchy`. No added
  file names any of them. Only the axiom prints settle this.
- **Forbidden constructs** (MEASURED, `arm-fill-forbidden.log`, comment-stripped):
  - no `admit`, `axiom`, `#`-command, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`,
    `native_decide` or `opaque` in the 81 files;
  - `sorry` only in our `TQBF.lean` (21) and `Savitch.lean` (2), as above;
  - 23 macro-family hits, all `scoped` or `local` *tactic* macros (`macro`, `syntax`,
    `macro_rules`) expanding to `simp only […]`, `omega`, `ext`, `split_ifs` combinations, in 11
    added files;
  - `set_option`: 237 standard header lines (3 × 79 math files) and 17 others: 14
    `synthInstance.maxSize`/`maxHeartbeats … in` and 3 `hygiene false in` (used by those tactic
    macros), each listed with its line.
- **Names** (MEASURED): no public full name of an added file is declared in any other file of
  `TCSlib`, by text-level namespace tracking. There are no declarations at the root namespace.
- **Duplication** (MEASURED screen; classification by the pack's author against the disclosure
  table): see the ledger section.
- **Policy and lint** (MEASURED): as in brief point 7. Every public declaration of the 73 files
  has a docstring. The lint over copies of `SpaceComplexity/` and `ClassPSPACE/` gives 12 FAIL
  and 5 WARN after the merge, against 0 FAIL and the same 5 WARN before.
- **Axioms** (MEASURED by the maintainer): `audits/evidence/arm-fill/AxARM.lean.txt` prints 60
  names:
  - the ten targets as briefed, the three moved theorems, `compile_correct_from` and
    `PATH_eq_pathRawLang`;
  - the interfaces of E1 (10), E2 (8), E4 (3) and E3 (12);
  - the customers' main theorems (12).

  Every name resolves to a public declaration of an imported module. The file holds only
  imports, `#print axioms` lines and a header comment. Result (`audits/logs/arm-fill-axioms.log`):
  exit 0, 0 errors, all 60 prints exactly `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.
- **Elaboration** (MEASURED by the maintainer's replay, above): 147 modules, 0 failures. Of the
  81 changed `.lean` files, 79 give no sorry warning; `ClassPSPACE/TQBF.lean` gives 21 (RD-2's
  codec lemmas) and `SpaceComplexity/Savitch.lean` 2 (`savitch`, `spaceConstructible_poly`).
  Hydroxyi's `lake build` is not reproduced (it is banned here); the replay covers every module
  the merge affects, except the root.
- **Bundle** (MEASURED: 199 files shipped, as listed in `BUNDLE-FILES.txt`; the pack author's
  estimate for the full list follows):
  - everything listed: 275 files, about 9.4 MB;
  - recommended: sections A–E and the 12 small files of section G, 197 files and about 4.8 MB;
  - dropped first: section F, the rest of the screen population (71 files, 2.6 MB); then
    section G's seven large files (`Build/Catalog`, `CookLevin/Hardness`, `Build/Loop`, `SAT`,
    `Universal`, `Robustness/SingleTape`, `Logspace/Mult`; 2.0 MB), whose pairs are all
    incidental and are reported with line ranges in the ledger.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide as in `audits/TEMPLATE.md` (debt: failure mode 5). Findings go verbatim into
`audits/arm-extensions-fill-findings.md`. The gate closes when a round reports zero blockers and
zero majors; a debt major closes only by the user's explicit acknowledgement, recorded with its
named payback.
