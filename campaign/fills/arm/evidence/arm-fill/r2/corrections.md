# Round-1 findings 6–14: corrections, record reconciliations and the replay statement

Proposed texts for the maintainer's minor-fix PR (#93, open when written, merged 2026-10-14:
findings 6, 10, 11) and for the records. Nothing here is applied by this round's builder; the builder edits no repository file.
Line numbers are at the tip (`e831b5b0`; its Lean tree is identical to `39bfdca4`'s).

## Finding 6 (minor): the `truth_mem_PSPACE` sketch bound — in PR #93 (open)

`TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean`, the docstring of `truth_mem_PSPACE`
(theorem header at `:171`), sketch lines `:168–170`. The theorem itself already uses the correct
bound (`hB' : B = 2 ^ (x.length + 1)`); no statement changes.

Replace

> Every register stays at most `2 ^ (|qs| + 1) ≤ 2 ^ (|x| + 1)`: the stack has at most `|qs| + 1`
> binary digits and the pointer, depth and counters are at most `|x|`.

with

> Every register stays at most `2 ^ (|x| + 1)`, the bound passed to the bridge. The stack register
> holds at most `|qs| + 1` binary digits, so it is at most `2 ^ (|qs| + 1) ≤ 2 ^ (|x| + 1)`
> (`|qs| ≤ |x|`, `length_enc`). The input pointer, the depth and the counters are at most
> `|x| + 1 ≤ 2 ^ (|x| + 1)`; this includes the syntax scan, which runs before `qs` is known.

The auditor's counterexample (`qs = []`, one empty clause, the five-bit word; the scanner's pointer
reaches 5 while `2 ^ (0 + 1) = 2`) is then consistent with the sketch. To check against #93's diff.

## Finding 7 (minor): the pack's adversarial candidates

The round-1 pack is immutable; round 2 supersedes two candidates.

- Superseded: "(2) `TQBF` on junk: odd length, no separator, trailing garbage after a valid
  prefix. Each must be accepted (`QBF.decode`'s true fallback)."
  Read: "**(2) `TQBF` on junk.** The words `[true]` and `[true, true, false, false]` have no
  successful pair parse; the five-bit false formula `[false, true, true, false, false]`
  (`pairEncode [] (CNF.serialize [[]])`) followed by `[false]` has a failing matrix parse. Each of
  these three must be accepted (`QBF.decode`'s true fallback). The five-bit word itself is well
  formed and false, and must be rejected: odd total length is not a malformedness test. Does
  `truth_mem_PSPACE` validate the whole input?"
- Superseded: "(2) a NARM whose start label is `choose l₀ l₀`: can any `N` satisfy `NHalts` (at
  `N = 0` the start is live)?"
  Read: "**(2) a one-label self-loop**: `A l₀ = choose l₀ l₀`, with `l₀` the start label. Can any
  `N` satisfy `NHalts`? (Equal destinations alone do not force nontermination: if they name a
  label holding `ret true`, a two-step bound works.)"

## Finding 8 (minor): records to reconcile

**What the response says, and what is exact** (a correction in our records; the response is
Hydroxyi's text and stays as written):

| Response claim | Exact statement (MEASURED, round 1's freeze log) |
|---|---|
| the three theorems "moved, byte-identical" | statements byte-identical; all three docstrings changed (fill appendices removed, sketches rewritten, `[Bon26]` dropped from `NL_subset_P`); `NSPACE_subset_exp_dtime`'s body changed from `sorry`; the other two bodies identical |
| "Nothing referenced their old module path" | no Lean code did; records did (below), and the historical probes import `ConfigGraph` for them |
| "`compile_correct` is byte-identical" | its statement and docstring are; its body is now `compile_correct_from` at the initial seam |

**Active records** (proposed edits; the maintainer lands them as a records commit):

| Record (tip line) | Now says | Proposed |
|---|---|---|
| `AroraBarakChapters3-4Plan.md:850`, row **B2** | `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL` "(ConfigGraph)"; route "BFS over coded vertices with a visited table (catalog copy/compare/increment, loop host)" | the three "(`SpaceComplexity/ExpTime.lean`; moved from `ConfigGraph` by `8c23f3bc`)"; route "proved at ARM level: a breadth-first MARM search over configuration codes with the MARM time bridge (design §14 H9, H12); `NP_subset_PSPACE`, `SAT3_mem_PSPACE` unchanged" |
| `AroraBarakChapters3-4Plan.md:730`, row **fills-6** | the S1b partial "proved modulo `NSPACE_subset_exp_dtime`" | a dated decision record: keep it; the later row "H2-M landed; Hydroxyi's ARM extensions merged" gains "S1b's open target `NSPACE_subset_exp_dtime` is proved in `ExpTime.lean`; its private `s1b_*` block in `ConfigGraph` is dead and is deleted by the payback PR" |
| `backlog.md` **MIG-19** | re-derive `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P`, Ex 4.3 as programs; retire S1b's private BFS host | **moot**: "Closed 2026-10-14: the three are proved (`ExpTime.lean`, ARM route, design §14 H12); S1b's private block is deleted by the payback PR (backlog ARM-1)." |
| `backlog.md` **MIG-22** | `TQBF_mem_PSPACE` as a program over the pure core `b4mValue`, `b4mValue_truth`, `b4mWalk_value` | **moot**: "Closed 2026-10-14: `TQBF_mem_PSPACE` is `LogProg.TQBFARM.truth_mem_PSPACE`; the pure core is deleted with the `b4m*` appendix (D6). The general AND/OR evaluator stays registry H1." |
| `machine-library-design.md:1426`, §12.8 consumer row **S1b**, and the S1b machine plans (`:1435`, `:1844`) | S1b's machine plan for `NSPACE_subset_exp_dtime` on the record rows | annotate as historical: "S1b stopped (fills-6); the target is proved at ARM level (§14 H12, 2026-10-14). These rows' remaining consumers are B6's window route (rows 17–18)." |
| `machine-library-design.md` §16b, the 2026-10-14 update paragraph and items 1, 2, 4 | the update paragraph already records items 1, 2 and 4 | add: "Item 3's 'S1b's private copies re-pointed in the same PR' is overtaken: the `s1b_*` block is dead and the payback PR deletes it. When the B6 hosts' `ConfigGraph` patch is regenerated on the tip (PR #92), it should not re-point that block." (The 2026-10-13 draft patch, `audits/evidence/b6hosts/gate/patches/ConfigGraph.patch`, edits it and lists `NSPACE_subset_exp_dtime` in `ConfigGraph`'s Main results: to check against #92.) |
| `machine-library-design.md` §14, H1, H3, H4, H6 | language-first H1/H4; S1b and B4 partials | the reconciliations in `registry-rows.md` |
| `backlog.md` §1 **ARM-1**, D6 | "44 declarations, 712 lines" (lines 2474–3185 at `6fbdefac`) | the range holds **45** declarations (13 `def`, 29 `theorem`, 2 `abbrev`, 1 `structure`; all private, all `b4m`-named; MEASURED, `arm-fill-r2-records.log`; round 1 also counted 45); 712 lines is right |

**Historical evidence** (preserved; annotate, never rewrite): the axiom probes
`audits/evidence/fills-6/AxF6.lean.txt` (imports `ConfigGraph` at `:6`; prints and
`#sorry_sources` of the three names at `:214–219`), `fills-7/AxF7.lean.txt` (`:7`; `:211–216`),
`fills-8/AxF8.lean.txt` (`:7`; `:211–216`). Proposed annotation, in the round-2 resolutions record:
"These probes are historical: they ran before `8c23f3bc` moved the three theorems to
`SpaceComplexity/ExpTime.lean`. Re-run at the tip they would not resolve the names."

**Current probe:** round 1's `audits/evidence/arm-fill/AxARM.lean.txt` already imports
`TCSlib.Complexity.SpaceComplexity.ExpTime` (`:15`) and prints the three (`:43–45`), at the replay
revision `733c22b7` (finding 14). Future fill probes that print them must import `ExpTime`.

**`[Bon26]`** (provenance history, not a citation of the new proof). The old `NL_subset_P` sketch
said: the external prior art's `NL ⊆ P` was "[Bon26] context … reachability-table construction;
design only, nothing ported". Proposed record, in design §12 "Citations": "Historical
(2026-10-14): `NL_subset_P`'s former sketch cited [Bon26] as design context for S1b's planned BFS
(reachability-table construction; nothing ported). The ARM proof in `ExpTime.lean` (received
`8c23f3bc`) neither uses nor adapts it, and its docstring drops the tag."

## Finding 9 (minor): methods and labels

- **The screen's basename key.** A fixed v2 keyed on full paths is being written separately; this
  round again runs the unmodified screen on byte copies under flattened, path-encoded names. The
  rerun over the 73 added files at the tip reproduces round 1's output byte for byte (343 pairs;
  `arm-fill-r2-screen-added-only.log`). The same-file analogue of the defect (two same-named
  declarations in one file are never compared) is empty here: no added file has two declarations
  with the same short name (`arm-fill-r2-pairs.log`).
- **Corrected labels** (round 1's pack and ARM-1; superseded by round 2's tables):
  - "63 declarations" is the **screened** library-copy population (16 disclosed copy sides with a
    pair, 47 undisclosed). The **policy** count adds D1's `InWin` and D6's `synOK`, below the
    floor: 18 disclosed + 47 undisclosed = **65**.
  - "33 of the 73 files by whole-body share" means **by whole-body characters or code lines**:
    **32** by characters, **28** by code lines, 33 by either. "14 by shared text" is by characters
    (13 by prorated code lines).
  - The "net" view's originals are the earliest member in import order: an **accounting
    convention**, not provenance; graph components are an accounting device, not semantic
    families (round 2 classifies families by inspection, `ledger-r2-tables.md` §4–§5).

## Finding 10 (minor): the `ClassPSPACE` facade imports — in PR #93 (open)

The facade imports its 12 new children (`TQBFARM/*` and `TQBFHard*`) directly, in the facade's
order; the focused lint returns to 0 FAIL. To check against #93.

## Finding 11 (minor): headings, line widths, sketches — in PR #93 (open)

42 over-width lines in 17 added files and 2 in the `SpaceComplexity` facade; 13 missing
`## Main definitions`, 2 missing `## Main results`; sketches for `prefixTruth_replicate_ex`
(`TQBFHardSemantics.lean:160`) and `prefixTruth_replicate_all` (`:193`). To check against #93.

## Finding 12 (minor): helper homes and namespaces — not in #93; ARM-2 (user, 2026-10-14)

`Path.getD_flatMap_rows`, `VWord.getD_drop`, `NARMProof.NSPACE.mono_const`, `ARMWidth`'s
`LOGSPACE_subset_PSPACE` and `SPACE_succ_pow_subset_PSPACE`, and the `Complexity.ExpBFS` /
`Complexity.LogProg.ExpBFS` split. Two of them are now ledger rows: `VWord.getD_drop` is a Bool
specialization of the public `Programs/Util/List.getD_drop` (row M2, proposed for the payback PR),
and `Path.getD_flatMap_rows` belongs to the list-lemma family G-flatten (ARM-2 (a)). The other
moves are not in #93. **Disposition (user, 2026-10-14): ARM-2**; M2 joins the payback PR.

## Finding 13 (minor): two prose summaries

- **The response's E2 summary** ("`arm_decides_space` (general width `S` with `logSpace ≤ S`)").
  Exact, for our records: "`arm_decides_space` (`Machines/ARMWidth.lean:104`): register digits
  `W ≤ C·S` for any `S` with `1 ≤ S`, given the explicit uniform oracle-space hypothesis `hs` (each
  decider's space at every virtual-input length `v ≤ 2n + 2 + m (2W + 2)` is at most `C·S`); it
  concludes `L ∈ SPACE S`. `arm_decides_SPACE` (`:193`) is its specialization to `logSpace ≤ S`
  with `LOGSPACE` deciders."
- **Round 1's pack, E3** ("Four code languages over `⟨x, ⟨bits c, bits s⟩⟩`"). Read: "Three
  single-code languages over `⟨x, ⟨bits c, bits s⟩⟩` (`validLang`, `initLang`, `acceptLang`) and
  the step language over `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩` (`stepLang`), `Langs.lean:62–86`."

## Finding 14 (minor): the replay revision, stated precisely

Proposed text, for the round-2 attestations and every later citation of the round-1 execution
evidence:

> The maintainer's replay (147 modules, 0 failures) and the axiom probe (60 prints, all within
> `propext`, `Classical.choice`, `Quot.sound`) ran at `733c22b7`, which is C1's branch
> (`21216a49`) merged with the round-1 pack tip `dc891632`, from an existing olean snapshot. The
> 81 received `.lean` files are byte-identical at `8c23f3bc`, `733c22b7` and the tip. The tree
> differs from the received tree exactly by PR #87's diff (`d054888d..4d149798`, 10 Lean files;
> byte-identical to `dc891632..733c22b7`, SHA-256 `7d9dfcf2ac891da013cd182c80c4cdf14853111a8337cb4b2a08171bd468d3bd`). Two of the ten are upstream
> of the received modules: `TuringMachine/Nondeterministic.lean` and
> `TuringMachine/NondeterministicSpace.lean`, where C1 proved the two lemmas that are `sorry` at
> the received tree (`runWith_eq_fixChoice_runFrom`, `spaceUsedWith_eq_fixChoice_spaceUsed`). At
> the received tree no code outside their own headers names either lemma (text scan, ESTIMATE).
> So the logs certify the received code on top of C1, not the received tree itself; a probe of the
> exact received tree was not run.

The ten files, with content hashes (MEASURED, `arm-fill-r2-c1delta.log`; blob ids from
`git rev-parse <commit>:<path>`):

| Path | Status | Blob at `dc891632` | Blob at `733c22b7` | SHA-256 at `733c22b7` | Bytes | Same blob at the tip |
|---|---|---|---|---|---|---|
| `ClassNP.lean` | modified | `fe7a3cad3ef1d95da1f25f1b25bde0b7e0a08b98` | `cecb4d9a8ab1aba009a6dfd7e8909cdeb321eaeb` | `2d24409e723b0c939db752777baaf97a3c26ebf83c97d5d56d725f8636f90f0b` | 3693 | yes |
| `ClassNP/ExhaustiveReplay.lean` | added | — | `78ec52ae323848d72cce3ea2695ea180302ecc1f` | `a2d721ecfee3ad76f40e99762419451d3bd3a427a7553b00dbbe694fa501a286` | 6209 | yes |
| `Diagonalization/NTimeHierarchy.lean` | modified | `0488e98f98f66e55a551e78d3c2c1b605cfbe1da` | `ad262c1492320b05c11fe9ddd1c4950458f804bd` | `2fa273acc56a8b974d66ac7c25df976d679ff55a7f91ed31fddf015514019335` | 23188 | yes |
| `TuringMachine.lean` | modified | `24f337e508ecb1646ae4215b9cbe2300bdcf1bee` | `d71df26046a70c596c3993f9e3a88d3e298bdef1` | `27921038cc8450c7721c46e49a24d311e59c783d4ab3012a32461d2e8b34b69e` | 12940 | no |
| `TuringMachine/Build/InputWindow.lean` | added | — | `5fd86b0392924e50a45df0b373de37f65ebac781` | `488c4ef352f0eb80023ebdb0a74fe2471ae643050bf0548133a3ecb736fd1d93` | 4602 | yes |
| `TuringMachine/Build/NDHost.lean` | added | — | `63d50799d6af7f0fd9cd57fc0a50ad283faedae9` | `9507b89d42771b824c42f9cc53b24cb505a5c08f9afcfb568ff727137ec7ede1` | 10405 | yes |
| `TuringMachine/ChoiceReplay.lean` | added | — | `8c2be4c180ec5f183b6ac690e0ce758eda51daaf` | `665b4ecc83b48ae2418990ea18d87b67fdda866c72b859585019de03fd22c6ac` | 6386 | yes |
| `TuringMachine/NDCodeSimulator.lean` | added | — | `2637a25a354d33dc4b69a873130c2683d5cde5af` | `51dd3667c60805b249d76b635a7ca6c797868332ae4b258bbb163a301df209b3` | 9085 | yes |
| `TuringMachine/Nondeterministic.lean` | modified | `f3f16a7ccd834e40361ce54b861ca3adeff53fb0` | `1eb091adde4e04ac83d69a524546942ca5890016` | `a3bd59ebd8e1b721f5fa3c87fb4967d4421bd43bb7c3ab7a1cd7d86ed39cf628` | 32660 | yes |
| `TuringMachine/NondeterministicSpace.lean` | modified | `a8267803edbfef5adb31a38ccb002841e56def1c` | `f9f2cacf583eb088bb904dc1c5913f675e9b770e` | `5519f3f061d87587a3a041567e7dfcc8906fae48389743f02a0ce96dbab90237` | 9599 | yes |

`TuringMachine.lean` (the facade) changed again after C1, with MIG-0b's split (#90); the other nine are unchanged at the tip.
