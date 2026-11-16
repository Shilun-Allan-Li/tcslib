# Closeout refactor plan and debt register (D4, W3), 2026-11-16

**Agreed (Seyoon, 2026-11-16):** all proposals, including §3's three decisions. W9 is deferred,
so §3.3's interleaving with W9 lapses: the order is R0–R6, then W4.

D4 (Seyoon, 2026-11-16): refactor before integration, all three groups — the chapter 3–4
families, the 12.2c infrastructure families and the ARM layer (no Hydroxyi coordination). This
plan is the inventory, the order, and the register (W3) of what is carried.

Source: the duplication ledger (L), the backlog (B) and plan P, each family's status checked
against the Lean at `351ba259` by grep (no build). Size: **S** one PR under ~200 lines;
**M** one to three PRs, no new interface; **L** a new shared interface first (its API goes to
Seyoon before the PR, per the standing rule).

## 1. Finding: much of the ledger is already retired

These families are retired in the Lean but still open in L or B. They close in the records
(wave R0, records only), with the grep evidence:

| Family | Retired by | Evidence at `351ba259` |
|---|---|---|
| D-R2, Catalog members (L318) | MIG-1 F-D (`af3273f75`, in #233): 356 privates, 8,202 lines | `Build/Catalog.lean` has no `f2_`/`a2_` name |
| Loop H3 / RB4 residue (L320, L322) | RB4 (#13), 11A (#20) | `emLoopHost` is an abbreviation of `loopHostM` (`Loop:4898`); no phase copies |
| Three-file relocation (L321) | RB5 (#14); the twin `f2_splitEmbed_run` by MIG-1 | absent |
| CH7-D1 (L323) | #18 | — |
| CH7-D2 (L324) | #20, #243 | five one-line citations (`EmitIterEmbed:106–140`) |
| CH34-D2 (L325) | #19 | one approved residual, `zfBFallback`; MIG-6 stays open (below) |
| FH-1 named copies (B347) | — | all surviving copies call `exists_first_halt` |
| CE-1, ZP-1 | #213, #212 | — |
| R80B-E1 (B406, L327) | **MIG-4 closed as done, kept as is (Seyoon, 2026-10-16; B2621)** | the two rows were never updated |
| ARM-1 (bulk) | payback #101 (+539 −1,549) | one residual, `arm_reach`, rides ARM-2 |

Also to check in R0: whether MT-1/AS-2 were fully covered by #214 (L1289), and a fresh
FE-LIVE-1 count after #241 (the records give none).

## 2. What remains, in waves

Each Lean wave item is a maintainer PR with a gate (Codex audit). Catalog edits replay most of
the library, so they are batched.

| Wave | Families | Files | Size | New API? |
|---|---|---|---|---|
| **R0** | **Done (2026-11-16):** the closures of §1, in the ledger's "Closeout reconciliation" section. MT-1 and AS-2 are open, so they go to R5 | records | — | no |
| **R1 · small mechanical** | **R1a, gate 143 CLEAR (PR #329): BW-1's and CH34-D4's copied proofs retired by citations; the four BW-1 privates are kept as one-line aliases (accepted deviation from the 2026-10-18 deletion wording; gate 143 resolutions), their use sites unchanged.** FE-LIVE-1 recount (2026-11-16): the remainder is the two held fronts of gate 121, `exists_inputLengthTM` (`Build/InputLength`, here) and `clA5Compare_compute` (`Hardness`, to R4); the remaining `Nat.find` selections are the canonical theorem's own and the separate ND first-halt family. **MIG-6 carried** (Seyoon, 2026-11-16: it redefines the frozen two-tape code structures, like CH34-D3). CH34-D4 leftovers (re-point `Separation:78` `bits_two_pow` and `MeyerTableau:416` `incFixed_eq_none_iff` to the #70 lemmas; FYI line per the 2026-11-06 ruling); BW-1 (`StepBlock` imports `BufferWords`, delete 4 privates); FE-LIVE-1 remainder (cite `exists_first_entry_of_fixed`); MIG-6 (parameterize `Codes2Tape` by tape count, about −180 lines) | TimeHierarchy, CircuitComplexity, Build, Codes2Tape, the FE-LIVE-1 sites | S each; 3–4 PRs | the EXPCOM padding-parse uniqueness lemma (one public lemma) |
| **R2 · Catalog batch** | **Ruled (Seyoon, 2026-11-16):** R2a, IW-1 + WA-1: move `Turing.wordPatch` and `wordPatch_of_mem`/`_of_not_mem`/`_append` from `StepClock` into `Catalog` (same names), add the public equation `wordPatch_apply`, delete `catalogTape`, `counterPatch`, `iw_patch`, and cite `wordPatch_append` in `rt_adjacentWrites`. **RW-1 carried** (no proof copied; unifying the tables changes the state type of the public `rewindTM`, 54 uses). R2c, the §12 common scanner: built and measured, then **carried** (Seyoon, 2026-11-16): it grew Catalog by 361 lines and the copy screen by 10 pairs (`R2C-SCANNER.md` §6). R2a **done: #330 merged** (`68cba664`, gate 144 CLEAR round 2; the interval patch, six further public lemmas, the touched proofs' legacy reads repaired). Original scope: IW-1 (move `wordPatch` below Catalog, delete 3 copies), WA-1 (rides IW-1), RW-1 (one public rewind frame and back-pass run), the §12 sibling rows (`clearTM`, `compareTM`, `incrementTM` and the `*_spaceUsedByTape` wrappers as instances of one scanner) | `Build/{Catalog,InputWindow,CounterLoop,StepClock,RecordTable,Rewind}` | M; 2 PRs (one replay each) | the scanner; the rewind frame |
| **R3 · ExhaustiveReplay and CodeSimulator** | C1E-1, IR-1 residual, RS-1, TR-1, SK-1 (after R2's rewind); CC7-1, RN-1 residual, RC-4, F7-1(b) | `ClassNP/ExhaustiveReplay`, `UniversalK`, CodeSimulator, ZoneRebalance, OracleSim | S–M; 3–4 PRs | small |
| **R4 · SAT/Hardness** | **Rulings (Seyoon, 2026-11-16; design study and intake in `r4-design-request/delivery/`):** R4-1 pilot **approved**: SG1-A (kind 4 + `satScan*`/`clFill*` riders) and PL-1, new public module `oneWayWord`/`oneWayTM`/`oneWayTM_computesFunInTime`/`polyTimeComputable_oneWayWord`; SAT may import `Build/WordTests` and `ClassNP/PolyTimeBlockLoop`. R4-2 **approved with a stop rule** (after R4-1 is measured): SG1-B (kinds 1, 2, 5 + `live_prefix`/`guard_add`/first-halt twins), about 8 public declarations (`CleanModule`, `stopTM`, `exists_cleanInstall/_cleanEmit`, `exists_first_halt_pos`); abandon and carry if net > +50 lines or more pairs created than retired. SG1-C **split**: kind 3 cites the public `Build/EmitIterEmbed` padding layer (no new API; SAT may import it); kind 6 (dispatcher) **carried**. SG1-UH: **measure** the route through `BinArith.polyTimeComputable_iterate` (Hardness imports `ClassP/BinaryArith/Iterate`) in scratch, then ask again. Item 13 **carried** (private layout adapter, not copy debt). **R4-1 built** (2026-11-16): PR #334, gate 145; it extends `ClassNP/Transducer` instead of a new module (Seyoon, 2026-11-16) and retires kind 4, its riders and PL-1's SAT/Hardness twins, net −161 lines; kind 3 moves to R4-2. **SG1-UH measured and built** (overnight authorization, 2026-11-16): PR #335 (stacked on #334), gate 146; `clA5Iter_native` cites `BinArith.polyTimeComputable_iterate` and the private host is deleted, net −297 lines, no new API, one new import (`ClassP/BinaryArith/Iterate`). FE-LIVE-1's Hardness front and FH-1's in-file copies are already retired; FH-1's `call_run`/`cleanTM_run` belong to the scheduled reader PR. *Original row:* SG1 kinds 1–6 (22 exact pairs, 298 lines per file), SG1-UH (14 declarations), PL-1's twins, 12.2c item 13 `clPlacement` (17 declarations), FH-1's held implementations (#242) | `ClassNP/SAT` (4,370 lines), `CookLevin/Hardness` (8,701) | **L**; a design note, then 4–6 PRs | yes: the six SG1 interfaces and the unary-clock host contract (B1040) |
| **R5 · ARM-2, then ARM-1** | K1–K20 (129 declarations): a reachability kit over an arbitrary step relation (K18, retires `arm_reach`), one step-semantics interface with a single bridge core (K3), a register/block kit, one generic layout run, one transfer loop; AS-2 and MT-1 (`Logspace/Mult`, `QueryReshape`, `NARMPSem`, cross-file table reads) | `SpaceComplexity/Machines/*`, `Codec/{Layout,Layout2,Parse}`, `Logspace/PathWalkProof`, the SavitchARM/ExpBFS/TQBFARM machines | **L**; a design note, then 5–7 PRs | yes: the kits and the interface |
| **R6 · the rest** | SpaceComplexity cluster (WS-1 after publishing the tape-half lemma; CQ-1, WL-1, CK-1, SD-1); TC-1, F6-1(j) (CircuitComplexity, FYI line); SH-1, DT-1; F6-1(b,c,d,f); MIG-3/7/8/9/10/24; U-1/MIG-2 (the `timedCut*` layer, `Universal:195`, **L**) | various | S–M each, U-1 L; 6–10 PRs | U-1's |

**Dependencies:** IW-1 before WA-1, and R2 before R3's rewind items; K18 and K3 before the rest
of R5, and R5 before `arm_reach`; WS-1 after the tape-half lemma; R4's interfaces approved
before its PRs. R1–R3 are independent of R4 and R5, so R4's and R5's design notes can be drafted
while R1–R3 run.

**Scale.** About 25–35 maintainer PRs and as many gates (audits can be batched where PRs touch
disjoint files), plus two interface reviews for Seyoon (R4, R5). No Codex fills: refactors are
maintainer work. R4 and R5 are the long items.

## 3. Decisions for Seyoon

1. **CH34-D3** (`exists_uniformMachineCode2` vs EXPCOM's structure; acknowledged as forced, B261):
   unifying it redefines two frozen, audited structures (a statement change and its own gate) to
   save about 12 lines. Proposed: **carry it in the register.** **Agreed.**
2. **Optional scope, not counted debt:** the original Loop host's 110 pairs (P item 11), the ch7
   embedding-layer watch (MIG-5), BL-W, WC-1, QF-1, RC-1–3, P item 12's clocks, the SafeSegment
   sibling. Proposed: **leave out of the closeout**, listed in the register as optional. **Agreed.**
3. **Order against W9.** Proposed: R0 and R1 first (quick), then R2/R3 interleaved with W9's
   interface refactor; R4 and R5 design notes in parallel; W4 (sync `main`) after R5. **Agreed**; with
   W9 deferred, R2/R3 run on their own.

## 4. Register (W3): what is carried into `main`

After the waves, the register carries only: CH34-D3, MIG-6, RW-1 and the §12 sibling rows (12.2c item 5; measured in R2c) (Seyoon, 2026-11-16) (both carried, Seyoon 2026-11-16; the item-8 format layer's frozen structures), `zfBFallback` (approved
residual), and the optional items of §3.2. Each entry: family, files, size, why carried, and a
pointer to its ledger row. The register is final at W6.
