# External audit pack: abstract register machines, step equations and block embedding (PR #182, an API gate)

**Why this PR.** The general `savitch` (`SpaceComplexity/Savitch.lean`, a stub) follows route (A),
iterative deepening on the radius (ruled by the user, 2026-10-27). Its machine runs the proved
Savitch search (`SpaceComplexity/SavitchARM/*`) for each radius: once against an edge-code decider
and once against the accepting-code decider. The design note
(`campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`) found that no lemma of the
search needs restating. One generic theorem transports any halting run of a machine `A` into a
larger machine that holds `A`'s table as a block. **Ruled (user, 2026-11-04): the embedding API**,
in place of restating the search for any containing program. Rule 10 forbids unfolding another
file's definitions, so the API sits beside the definitions it reads (`astep`, `PreS`, `AHalt`,
`GuardLe`, `callSegs`, `A`), in Hydroxyi's files. It is additive and within the standing
2026-10-27 authorization to extend his `SavitchARM`/`Machines` layer for the general `savitch`
(FYI only, the user's to send).

**The PR:** #182 on `lean/arm-embed`, head `8fd6f91a270f497a872146765cfab8422c3faf8e`. It holds the
commit `024e19bf` (`evidence/patches/`) and a merge of the campaign's records commit `5d2a16e6`,
which changes no Lean. Against the campaign, #182 changes exactly five files, adding 328 lines and
removing none.

## What changed (verify)

| File | Added (all public) |
|---|---|
| `Machines/ARM` | `arun_zero`; the step equations `astep_inc`, `_dec`, `_clr`, `_half`, `_jz`, `_jodd`, `_jeq`, `_call`, `_ret`, `_valP`, `_valQ`, `_jeqIn`, `_jeqFst`, `_jeqSnd` (`A l = <instruction> → astep A o x (some l, v, res) = …`); a `## Main results` entry |
| `Machines/Program` | `callSegs_congr`: calls with the same mode and argument words have the same virtual input |
| `Machines/ARMProof` | `Ins.embed` (registers along `ρ`, deciders along `σ`, labels along `ι`, `ret b ↦ jz r₀ (k b) (k b)`); the structure `RegExt` (fields `reg`, `ext`) and `RegExt.update`; `preS_of_ins`; `preS_embed`; `astep_embed`; `AHalt.embed` (general guards `G`, `G'` with a transfer hypothesis); docstring entries |
| `Machines/ARMLoops` | `AHalt.embed_guardLe`, the `GuardLe` instance; a docstring entry |
| `SavitchARM/Machine` | `A_noVal`: the Savitch machine has no `valP`/`valQ`; a docstring entry |

Freeze (`evidence/freeze/`): public declarations go 25 → 26, 20 → 35, 19 → 26, 10 → 11 and
79 → 80. Nothing is removed and no statement changes; there are no private declarations. Census
of non-private constants, compiler auxiliaries included (`evidence/census/`):

| Module | Before → after | What is new |
|---|---|---|
| `Program` | 205 → 206 | the lemma |
| `ARM` | 273 → 290 | 15 lemmas, plus `astep.eq_1`, `astep.eq_2`, now realized here |
| `ARMProof` | 48 → 78 | 7 declarations; `Ins.embed`'s 14 equations and `match_1`; `RegExt`'s structure constants; `AHalt.embed._proof_1_1` |
| `ARMLoops` | 38 → 39 | the lemma |
| `SavitchARM/Machine` | 624 → 678 | `A_noVal`, plus `A.eq_1`…`A.eq_47` and the six sub-table equations, now realized here |

Downstream modules that used to realize those equations no longer do; gate 89 recorded the same
effect for `logSpace.eq_1`.

## Brief for the auditor

1. **Homes and shape.** Is each lemma beside the definition it reads? Is the general `AHalt.embed`
   (in `ARMProof`, beside `AHalt`) plus its `GuardLe` instance (in `ARMLoops`, beside `GuardLe`)
   the right split? Is `RegExt` right as a structure (it was first a `def`; see 3)? Is the `ret b`
   ↦ `jz r₀ (k b) (k b)` encoding sound, and the `valP`/`valQ` exclusion necessary? (An embedded
   failed input check halts the host with `false` instead of reaching the exit.)
2. **Statements.** Are the step equations exactly `astep`'s cases, including the classical `if` of
   `valP`/`valQ`? Is `AHalt.embed`'s conclusion strong enough for the deepening machine: the exit
   reached, registers off `ρ`'s range unchanged, and the block's final registers satisfying `G`?
   The consumer probe `evidence/rule10/EmbedFit` transports `SavitchARM.outerU_run` into a host with
   decider `2` rerouted to `4`, sealed.
3. **Rule 10** (maintainer API proofs, scope of 2026-10-23), `evidence/rule10/`. Four sealed copies
   elaborate with 0 diagnostics: `ARMSealed`, `ARMProofSealed`, `ARMLoopsSealed`, `MachineSealed`.
   Their seal lists and controls are in `scripts-note.txt`. Unsealed, 14 of 16 controls pass: the
   recursive `vword` and `argSegs` fail their delta goals and pass their equation controls. Sealed,
   all 16 fail. The first run of `ARMLoopsSealed` failed at `RegExt`'s `.1`/`.2` projections, a real
   hit: `RegExt` was a `def` of another file read by projection. It became a structure, and the head
   is that version. `astep_embed` reads `astep` only through the new step equations, `arun` through
   `arun_zero` and `ARMRun`'s `arun_succ`/`arun_halted`, and a call's virtual input through
   `callSegs_congr`. Is anything else unfolded or closed by reduction? In particular, `hDl`'s
   `rw [hD, hi]` leaves `Ins.embed`'s own-file reduction to `rfl`.
4. **Duplication.** The screen (`evidence/screen/`, 13 files, population in
   `screen-population.txt`) gives 144 → 153 declarations screened, 40 → 40 pairs, 16,495 characters
   both times, and no pair new or gone (`pairdiff.txt`). Three older machine-specific step lemmas
   (`astep_call₁`, `AdjScan.astep_hit`, `AdjScan.astep_jeqFst`) are specializations of the new
   general ones. They are ledgered as AS-1 for the dedup window, not changed here. Is that right?
5. **Names** (`api-copy-search.txt`, every origin ref). No ref other than this PR's declares the new
   names in `Complexity.LogProg`. `BoolCircuit.AdjScan.astep_jeqFst` shares the short name. Its file
   opens `Complexity.LogProg` and still elaborates (`evidence/elab-chain/LogspaceUniformScan.out`),
   the overload resolved by argument type. Should either be renamed now?
6. **Lint** (`evidence/lint/`). `SpaceComplexity`: 0 FAIL and 83 WARN over 110 files at base and
   head. The check-8 warnings for `astep`, `arun`, `PreS`, `callSegs` and `SavitchARM.A` go away,
   since a lemma now sits beside each; `Ins.embed` gains one. The policy linter reports 0 findings on
   the five files at the head; the base had one, `ARM` missing `## Main results`, now added.

## Repository-side attestations (verify or challenge)

- **Elaboration chain** (`evidence/elab-chain/`, method in `scripts-note.txt`). The five files were
  compiled in dependency order into a copy-on-write clone of `oleans-leqc3`, 0 diagnostics each;
  `LogspaceUniformScan` and `EmbedFit` against the same clone, 0 diagnostics.
- **Axioms** (`evidence/census/NewAx-head.out`). Every new declaration other than the structure is
  within `[propext, Classical.choice, Quot.sound]`; `Ins.embed` and `preS_of_ins` use none.
- **Replay:** `replay-larm.sh` (`evidence/merged-tree/`), the five files' downstream closure, 138
  modules, fresh `.olean`s from `oleans-leqc3`, pinning the five blobs. Precheck passed; **not yet
  run.** #181 (gate 89) overlaps this closure (`Machines/ARMWidth` and its users), so whichever of
  #181 and #182 merges second takes a merged-tree replay of the overlap.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/90-arm-embed-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `arm-embed-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
