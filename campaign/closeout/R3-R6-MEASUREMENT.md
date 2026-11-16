# Refactor waves R3–R6: measurement and run/carry table (2026-11-16)

This note is for Seyoon's morning review. It covers every open family of waves R3–R6 in
`REFACTOR-PLAN.md`. For each family it gives:

- **Members and uses:** the agent inventories (`measure/R3.json` … `R6.json` in the
  maintainer's scratch), rechecked on the tree.
- **Rule-10 exposure:** a *what-if seal*. Every member and use site is treated as changed and
  sealed at campaign Lean `68cba664` on `oleans-c68cb`, exactly as a gate does. The figure is the
  number of declarations whose current proof text would fail the sealed check, so would need
  repair if a PR touched them. This is the cost driver that sank R2c and inflated R2a.

Overnight PRs (done under the 2026-11-16 overnight authorization; each has its own gate pack,
ready for Codex):

| PR | Gate | What | Net Lean lines | Status |
|---|---|---|---|---|
| #334 | 145 | R4-1: SG1 kind 4 + riders + PL-1 twins, onto an extended `ClassNP/Transducer` | −161 | staged |
| #335 (stacked on #334) | 146 | R4 SG1-UH: unary-clock host deleted; `clA5Iter_native` cites `BinArith.polyTimeComputable_iterate` | −297 | staged |
| #336 | 147 | R3a: SK-1; dead CC7-1/C1E-1 members; RC-4 buffer half; MIG-8 dead chain; PL-1 `a3n_poly_linear` | −303 | see HANDOFF |
| #337 | 148 | MIG-3: `one_work_tape` through the demand-grown witness; first sweep witness's run layer deleted | −451 | see HANDOFF |

Overnight total: **−1,212 Lean lines**. The only new public API is the three `Transducer`
declarations approved for R4-1.

## R3

Total rule-10 exposure: 35 declarations.

| Family | Members (lines) | Uses | Rule-10 exposure (members/uses) | Recommendation |
|---|---|---|---|---|
| C1E-1 | 26 (218) | 33 | 0 / 0 | Dead `xr_firstArrival` **done** (#336). The rest is marginal. (a) `xr_val` → `counterValue` saves nothing: the public API is only `counterValue_eq`/`_bits`, so the eight `xr_val` lemmas would be re-proved under the public name. (b) `xr_bufferTape_neg` can cite `FinTM.bufferTape_of_neg` (−6). (c) a shared prelude for the two replay exits (about −20). (d) ten two-line `_ne_` lemmas merged into one. Batch (b), (c) and (d) when ExhaustiveReplay is next open. (f) is structural; it goes with IR-1. |
| IR-1 | 6 (144) | 9 | 0 / 0 | **Carry.** Structural: the phase-host arms change. The seam-time arithmetic in the public `exists_selfStartupTMK` must be rechecked. |
| RS-1 | 3 (87) | 2 | 0 / 0 | Small. Needs your import choice (`Build/UniversalParts` vs the `CfgFacts` route). |
| TR-1 | 4 (58) | 8 | 2 / 6 | **Carry**, or a later small PR. Needs new API (`AcceptsWithin.iff_of_haltsWithin`). |
| SK-1 | 1 (39) | 1 | 0 / 0 | **Done** (#336). |
| CC7-1 | 12 (863) | 4 | 0 / 0 | Dead `canonCounterRepeat` **done** (#336). The 7-leg template (about 690 lines) is the largest zero-exposure item. It needs a private template design; recommend a design pass next. |
| RN-1 | 39 (982) | 0 | 2 / 0 | Low exposure, but it touches Primitives (222 downstream modules) and Loop (223). Recommend narrowing it to CodeSimulator's part, with CC7-1. |
| RC-4 | 3 (39) | 5 | 0 / 0 | Buffer half **done** in CodeSimulator (#336). The first-halt row needs new API in `Nondeterministic` (160-module replay): **carry**. |
| F7-1(b) | 9 (229) | 23 | 9 / 15 | **Carry.** High exposure; the backlog assigns it to MIG-14. |

## R4 (ruled 2026-11-16)

| Family | Status |
|---|---|
| SG1 kind 4 + riders, PL-1 | #334 / gate 145 |
| SG1-UH | #335 / gate 146: −297 lines instead of the study's +170 to +370 public host |
| SG1 kinds 1, 2, 5 (R4-2) | Approved with the stop rule; **not started overnight** (maintainer's judgment). What-if exposure: K1 4/4, K2 4/6, K5 0/4, i.e. about 22 proofs to repair, including `clA5Startup` and `satReduction_poly`. See the note after this table. Recommend it as the next maintainer item, run against the +50 stop rule, with the consumer restatement priced first. |
| SG1 kind 3 | Ruled: cite `Build/EmitIterEmbed`. The private signatures differ (no `m ≤ k` argument, no state map), so it rides with R4-2's host edits. |
| SG1 kind 6, item 13 | Carried (ruled). |

**Why R4-2 needs care.** Hardness's copy module (`clA5Copy_clean`) and startup (`clA5Startup`) use
the stop adapter's tape count `D.k` and start state `D.tm.q₀` inside *types*: the words
`stateWord D.k _` and the configurations `Cfg D.k …`.

- Today the adapter is a same-file definition, so `change` and `simp [clA5StopTM]` may unfold it.
- Once the adapter is a public definition in another module, every such unfolding is a rule-10
  read.
- An equation `stopTM_k : (stopTM C e x).k = C.k` cannot be used by `rw` under the dependent
  `Cfg`/`stateWord` types (the motive is not type-correct).
- So the repair is not a substitution. The consumers have to be restated in the adapter's own
  fields, or go through a `CleanModule`-shaped contract. That is a real rewrite of the 55-line
  `clA5Startup` and its legacy reads (`initCfg`, `Cfg.init`, `Cfg.ofWords`, `stateWord`,
  `bufferTape`).
- Keeping a private alias `clA5StopTM := FinTM.stopTM` would hide new foreign reads in unchanged
  proofs, so it is not an option.

The study's estimate (−80 to +50 lines) remains plausible, but most of the effort is this
restatement.

## R5

Total rule-10 exposure: **310 declarations**. Every K-family has members that fail the seal.

| Family | Members (lines) | Uses | Exposure (m/u) | Recommendation |
|---|---|---|---|---|
| K18 (reachability kit) | 28 (161) | 140 | 27 / 116 | **Carry.** 143 proofs to repair. |
| MT-1 | 10 (553) | 71 | 0 / 67 | **Carry**, or per-machine-directory slices later. |
| K2 (input/code banks) | 27 (152) | 91 | 9 / 62 | **Carry.** |
| K1 | 30 (249) | 31 | 10 / 24 | Carry |
| K10, K11, K12, K13, K14 | 4–16 each | 1–18 | all members exposed | Carry |
| AS-2 | 12 (685) | 6 | 12 / 6 | Carry (Seyoon's Mult/QueryReshape) |
| K3, K4, K7, K8, K9 | | | all exposed | Carry |
| K5, K15, K16, K19, K20 | small | 1–22 | K15 0/1, K20 0/14; others exposed | Optional small slices; not worth a gate each |
| ARM-1 residue | 1 (33) | 0 | 1 / 0 | Carry, with K18 |

Recommendation: **carry R5 into the register** (it is the ARM-layer debt, D4 group 3). The
measured repair load is about 9× R3's.

## R6

The what-if seal for R6 (93 files) ran out of memory twice in its single metadata step. A split
run is pending, so the exposure column is not yet measured. The inventory:

| Family | Members (lines) | Uses | New API? | Recommendation |
|---|---|---|---|---|
| MIG-3 | 14 (427) | 1 | no (a private witness) | **Done** (#337, −451) |
| MIG-8 | 14 (184) | 1 | no | Dead chain **done** (#336). The merge half waits on SH-1. |
| SH-1 | 5 (75) | 2 | no; one import (Nondeterminism ← CertShell) | Small; next candidate after a measurement |
| MIG-7 | 8 (126) | 6 | no; but an import of the Build stack into chapter-1 UniversalStartup | Ask. It pulls Build under the universal machine. |
| CK-1, TC-1 | 2 each | 10 / 2 | no | Hydroxyi's files (FYI line per ruling); trivial bodies |
| WL-1, SD-1 | 1–2 | 1–3 | public move/rename | Ask (public name changes) |
| DT-1 | 2 (5) | 26 | `mem_DTIME_iff` | Large replay (DTIME is upstream of most of the tree); carry, or at a quiet point |
| WS-1 | 11 (311) | 14 | a general `Action` lemma in a vendored file | Ask |
| MIG-9 | 34 (615) | 20 | a bit-length counter row | Design first |
| MIG-10 | 5 (47) | 1 | OracleTM relabelling | Small API; ask |
| MIG-24 | 37 (546) | 186 | small symmetry lemmas | **Carry** (186 use sites) |
| U-1/MIG-2 | 72 (1411) | 22 | U-1 host interface | **Carry**, or a design note: the largest item |
| F6-1(b, c, d, f) | 1–4 each | 3–6 | one lemma each | Small, but each needs one API approval |

## Suggested order after the morning audits

1. Dispatch gates 145–148. They are independent, except that 146 builds on 145.
2. R4-2 (SG1-B), with the stop rule.
3. C1E-1 (a, c, d); a CC7-1 template design note; SH-1 after its measurement.
4. Small rulings: RS-1's import, the F6-1 one-lemma APIs, WL-1/SD-1 renames.
5. Carry the rest (R5 entirely; IR-1, TR-1, F7-1(b), RC-4's first-halt row, MIG-24, U-1/MIG-2,
   DT-1) into the register and move on to W4 (sync `main`).
