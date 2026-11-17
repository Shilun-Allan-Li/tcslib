# Pass–shelat cleanup, Stage 2 (re-point and prune): plan r1, for Seyoon's ruling

**Status: draft for ruling. No job is issued from this plan.** Static work only (git, `python3 -I`, text tools; no Lean,
no `lake`). The machine-readable scope is [`scope.tsv`](scope.tsv) (1,092 work items, one row each). The derivation
scripts are in [`tools/`](tools/) (`reloc.py`, `build.py`, `jobs.py`). Every line number in this plan and in `scope.tsv`
is at the current tip.

## 0. Pins and inputs

| Pin | Value |
|---|---|
| Records tip (`origin/cryptography/pass-shelat-ch2-4`, after `git fetch`) | `2be7eb209ae89c9dfe5ba7b63b115ae486ff9ffd` (tree `127f807b8a6d38de96b14dde15fdc021d4fdb8bb`) |
| #355 merge (Stage 1) | `a1fa7b652f0c235b54fc067e09b669e983daaf71`. `TCSlib/` and `TCSlib.lean` are identical at the tip; the Lean equals TS2 `13fc8060d5b8d08a8f9e80244242118acaa679e2` (`phase2-s6.md`) |
| #347 merge (DW-5) | `7623ae29754002034f6049988106fb3fd6eaeaf7` |
| DW-10 inventory (exchange) | `57cd9272d5739fae252cf486297c696f7b90d2bd`:`inbox/audits/dw10-seal-inventory/inventory.tsv` (2,110 rows; SHA-256 `7e2b2e6a…37b8f`); base `f472accd5e000a53d0fbe02b5414435429ce4a70` |
| Stage 1 re-point table (exchange) | `5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a`:`inbox/fills/cleanup-stage1/evidence/stage2/repoint.tsv` (98 rows; SHA-256 `8fba3337…b7f9`); lines at check tree `01cc6259480ccc9372181cd4d18d4511c87aa048` |
| Maintainer addendum | `cleanup-stage1/final-r1/stage2-addendum.tsv` (19 rows; SHA-256 `b2656ad5…fa73`) |
| DW-10 Stage 2 derivative | `cleanup-dw10/final-r1/stage2-seal-items.tsv` (591; `c0ec4010…59b0`), `stage2-readers.tsv` (74; `d9ea4be6…f3a8`); review evidence `stmtcheck.txt` (F01) |
| PS10 cite-check | `ingests/ps10-cite-check-final-r1/REPORT.md` (`4390cc6a…f1c8`); delivery exchange `69add65448274d7d5dddc79249ff251567fa376c`; site lines at `b76f804b4615123e6084a00d23fd9e6ff88fac92` (Lean-equal to `f472accd`) |
| Stage plan and ledger | `cleanup-stages.md` (`ec99c98d…8e08`), `duplication-ledger.md` (`d500c17e…0cf1`), `deferred-work.md`, plan decision log to row 885 |

**Relocation method.** Base lines were mapped to the tip through `git diff -U0` hunks (base → tip). Declarations were
found at the tip by name, for all 591 derivative items and all 194 SEAL-B-ONLY rows (0 not found). Of the 41 TCSlib files changed since `f472accd`, 18 hold Stage 2 items:
- the #347/#355 host files `IterateFind`, `IterateFindHost` and `ModuleHost`;
- Stage 1's `PPT`, `Trapdoor`, `Entropy`, `EnsembleSecurity`, `BitLists`, `PRF Defs`, `EncodingMachines`, `Interaction` and `Games/Tapes`;
- the bb1-sim/IBE/pairing files of DL-55 to DL-57 and `Games/Probability`.

All of them were re-derived by name or through the diff hunks. Three items carry `?` for the line: two are new declarations (`mul_prob_le_expect`, the `Tapes`
docstring), and one is DL-38's unnamed local `have` in `OracleFromPRF.lean`, which the brief must locate.

**DW-10 F13 confirmed.** The 23 F-01 rows were dropped from the derivative (22 `polyTimeComputable_find`, 1
`computesFunInTime_find`, all `IterateFind.lean`). They stay dropped:
- `phase2.md` records `IterateFind` 20 → 0 in all four seal variants on TS1.
- `git diff 1eaf940b938bb52e3919f5569893b58522df599b a1fa7b65 -- TCSlib/Complexity/Randomized/Build/` (TS1 tree against the merge) is empty, so the merged file is the replayed one.
- Stage 2 has no F-01 row. The Stage 2 gate re-seals `IterateFind`, because J1 touches it (PS10 A1 and E1's local steps).

**Also confirmed out of scope.**
- DL-58 was repaid by LE-g48 on #357.
- `Uniform.lean`'s 4 rows are handed off (Q10).
- The 31 STRICT-ONLY rows are notation and need no fix (Q3).
- The 14 W5 file-level `local irreducible` rows are reported separately by the gate.
- The 608 HANDED-OFF rows and DL-60 B2 belong to the Complexity handoff.
- GSW items are out: DL-50, and the DL-47 copy at `GSW/Eval.lean:263`.
- Complexity-side inline chains stay (CS1-Q12).
- DL-53 consolidation is deferred until after the `main` merge.
- The CS1-Q10 near relatives are notes only: the six "none" or "optional" addendum rows, DL-44 F-03 and DL-45 `flip0`/`flipAt`.
- Promotion requests with no ledgered copy are declined (CS1-Q11): DL-48's four requests.
- The `fwdHandler` generalization is withdrawn (CS1-Q4).
- DL-45's short-name renames (`relabel`, `flipAt`) are not proof-only, so Stage 2 leaves them out.

## 1. Scope and totals

**What Stage 2 contains** (sources → `scope.tsv` id prefixes):
- **`S2-RP` (112 items).** The Stage 1 re-point table and the maintainer addendum, split per owner file. These cover:
  - DL-35 (proof re-derivation), DL-39 to DL-49, DL-51 and DL-52;
  - DW-9/DW-5: E1's three local steps and the three unused `host_*` lemmas.
- **`S2-BK` (22).** The fourteen approved DL-35 `blocks` changes, the proof uses of the aliases, and the removal of the
  private and public aliases.
- **`S2-DL` (28).** Ledger rows with no table row:
  - DL-55, DL-56, DL-57 and DL-59 in full;
  - DL-60 B3/B4, and DL-40's ETT averaging copy (`Forgery.lean:515`);
  - DL-43's promotion and `signatureBlock`;
  - DL-42's `splitBits_pad_concat` and `lamport_forgerCodec`, and DL-46's `adviceBound`;
  - DL-38's located folds;
  - the nits: `BobIO`'s `simpa` (whose site is also an uncatalogued DL-47 getD chain), and CS1-C1-F10's `Tapes` docstring.
- **`S2-SL` (591) and `S2-RD` (74).** The DW-10 derivative's seal items and new readers. These include DW-9's 52 host items
  and Q11's two provider readers.
- **`S2-W6` (4).** The four shadow retirements (W6).
- **`S2-BO` (194).** The SEAL-B-ONLY rows (Q8): 143 proof-level and 51 statement-level.
- **`S2-PA` (40), `S2-PB` (21) and `S2-PR` (6).** PS10 Tier A, Tier B, and REPORT §3's related notes (the sixth note,
  `Signatures/Defs.lean:156`, is judged OK and left out).

**Seal scope.** There are 785 DW-10 items: 591 derivative items and 194 B-only rows. Seal B is now in the target, so the
gate's "no seal failure in a touched file" covers coe-A and coe-B. Strict-only failures are reported, not failed (Q3).
W5 lines are reported separately.

**Estimates.** Line counts are heuristic and accurate only to about ±40%:
- a re-point is about 4 lines per site, and a seal fix 3–4;
- a reader is 8 lines with its docstring;
- a B-only fix is 4 lines at proof level and 8 at statement level;
- a deletion counts its measured extent at the tip;
- each W6 retirement is a design estimate (§2, J5/J6).

### 1.1 Totals by kind

| kind | items | files | est. lines | sources |
|---|---:|---:|---:|---|
| seal fix (proof-only) | 562 | 56 | 2117 | DW-10 |
| B-only fix proof-level | 143 | 48 | 572 | DW-10 |
| re-point | 104 | 73 | 544 | DL-35, DL-38, DL-39, DL-40, DL-40/DL-59, DL-41, DL-41/DL-44, DL-42, DL-43, DL-44, DL-46, DL-47, DL-48, DL-49, DL-51, DL-52, DL-55, DL-56, DL-57, DL-60 B3/B4, DW-9/DW-5, Stage 2 nits (BobIO) |
| add reader | 74 | 24 | 592 | DW-10 |
| B-only fix statement-level [freeze exception] | 51 | 20 | 408 | DW-10 |
| citation fix | 40 | 24 | 80 | PS10 |
| seal fix (after shadow retirement) | 29 | 3 | 116 | DW-10 |
| citation fix (advisory) | 27 | 18 | 27 | PS10 |
| delete | 24 | 23 | 277 | DL-35, DL-38, DL-40, DL-40/DL-44, DL-42, DL-45, DL-46, DL-47, DL-57, DW-9/DW-5 |
| re-point (definition body) | 14 | 11 | 170 | DL-39, DL-40, DL-40/DL-59, DL-43, DL-48, DL-49, DL-59 |
| alias change | 14 | 8 | 56 | DL-35 |
| promote | 5 | 5 | 76 | DL-42, DL-43, DL-55, DL-57, DL-59 |
| retire shadow | 4 | 4 | 1380 | DW-10 |
| doc nit | 1 | 1 | 2 | Stage 2 nits (CS1-C1-F10) |

The seal-fix rows include DW-9's 52 host items: `ModuleHost` 20 and `IterateFindHost` 32.

### 1.2 Totals by owner area

The file count is of existing files. W6 adds up to 4 new modules and their facade lines.

| owner area | files | items | statement-visible | est. lines |
|---|---:|---:|---:|---:|
| Complexity (campaign-created T1 files; Encoding.lean for Q11) | 13 | 156 | 1 | 519 |
| Cryptography/Asymptotic | 21 | 210 | 13 | 940 |
| Cryptography/Authentication | 11 | 31 | 16 | 198 |
| Cryptography/Composability | 8 | 13 | 0 | 19 |
| Cryptography/Encryption | 33 | 98 | 19 | 568 |
| Cryptography/Games | 2 | 3 | 1 | 24 |
| Cryptography/Pseudorandom | 14 | 88 | 9 | 455 |
| Cryptography/Randomness | 7 | 15 | 2 | 79 |
| Cryptography/SecureComputation | 28 | 71 | 17 | 333 |
| Cryptography/ZeroKnowledge | 33 | 348 | 8 | 2939 |
| Cryptography/{AdvancedEncryption (IBE), Pairing} | 5 | 8 | 0 | 104 |
| Cryptography/{Candidates, Foundations, Encoding, Hashing, HardcoreBit, NumberTheory} | 16 | 40 | 3 | 197 |
| InformationTheory | 2 | 11 | 0 | 42 |
| **total** | **193** | **1092** | **89** | **6417** |

### 1.3 Items that change a statement, a definition body, or the API (freeze-visible; 89 items)

Seyoon asked for per-item visibility. These are the `scope.tsv` rows whose `statement_change` is not `no`.

| group | items | ruling | status |
|---|---:|---|---|
| (a) SEAL-B-ONLY, statement-level (F01) | 51 | Q8 (granted, meaning-preserving through the `PolyExpr.eval` readers) | approved; listed below |
| (b) DL-35 `blocks`-alias changes | 14 | CS1-Q2 (six), the seventh, Stage 1 final Q2 (seven) | approved; listed below |
| (c) public alias removal `EnsembleLemmas.blocks`, `blocks_eq`, `blocks_apply`, `blocks_symm_apply` (and the private `blocks`, `blocks_eq`) | 1 row (S2-BK-22; S2-BK-21 private) | CS1-Q2 (decls2 REMOVED approved) | approved |
| (d) **definition-body re-points** of public duplicate *definitions* (old def `:=` promoted def; their lemmas re-derived) | 14 | **none yet** | **Q7** |
| (e) W6 shadow retirement: verbatim moves of the canonical definitions below the proof files, shadow-namespace statements restated over them, shadow definitions removed | 4 rows (~49 shadow definitions; the restated lemmas are to be listed by the brief) | W6 (retire), design not ruled | **Q9** |
| (f) DL-59: `Games.extTape` family generalized from `Type` to `Type*` (4 declarations of #355) | 1 row | DL-59 says "stated at `Type*`" | confirm in **Q8** |
| (g) verbatim moves, same full name (REMOVED/ADDED pairs): `MachineCodec.ext_of_fields` → `Games/Machines.lean` (S2-RP-103); `decide_singleton_eq_true` → `Foundations/BitLists.lean` (S2-DL-01) | 2 | CS1-Q3; DL-55 | approved |
| (h) deletions of public declarations: `host_dispatch`, `host_branch`, `host_halt` (S2-RP-004); `adviceBound` (S2-DL-20) | 2 rows | cleanup-stages Stage 2 and DW10-Q9; DL-46 frozen-file exception | approved |

The additive promotions are not counted as statement changes: DL-43 `mul_prob_le_expect` (CS1-Q9), DL-57 `IBEScheme.*`,
any DL-56 reader, and the 74 readers.

**(a) The 51 statement-level SEAL-B-ONLY declarations** (F01's list, `stmtcheck.txt`; all coe-B/strict-B failures in
the header). Each needs a header restated through `PolyExpr.eval`'s readers. Several are headline targets:
- `lamport_oneTimeSecure` [PS10, Thm 137.2];
- `yaoProtocol_hbcSecure` and `yaoHybrid_hbcSecure` [Thm 163.7];
- `thm_97_3_1`;
- `specialScheme_multiMessageSecure`;
- `garbling_good_whp`.

These touch Stage 3's census and axiom prints (see A4).

| # | scope id | inventory id | owner file:line (tip) | declaration | job |
|---:|---|---|---|---|---|
| 1 | S2-BO-001 | (SEAL-B-ONLY; | `Asymptotic/Ensembles.lean:232` | `Ensemble.copies_X` | J2 |
| 2 | S2-BO-002 | (SEAL-B-ONLY; | `Pseudorandom/Generators/Asymptotic/FromPermutation.lean:239` | `PermFamily.iterPRG_eq_expand` | J3 |
| 3 | S2-BO-013 | (SEAL-B-ONLY; | `SecureComputation/GarblingSecurity.lean:77` | `SecureComputation.nestedSpecial_wrongKeyBot` | J3 |
| 4 | S2-BO-014 | (SEAL-B-ONLY; | `SecureComputation/GarblingSecurity.lean:106` | `SecureComputation.garbling_good_whp` | J3 |
| 5 | S2-BO-017 | (SEAL-B-ONLY; | `SecureComputation/SpecialEncryptionSecurity.lean:76` | `SecureComputation.prfOut_var_iff` | J3 |
| 6 | S2-BO-018 | (SEAL-B-ONLY; | `SecureComputation/SpecialEncryptionSecurity.lean:200` | `SecureComputation.specialScheme_multiMessageSecure` | J3 |
| 7 | S2-BO-019 | (SEAL-B-ONLY; | `SecureComputation/SpecialEncryptionSecurity.lean:286` | `SecureComputation.specialScheme_wrongKey` | J3 |
| 8 | S2-BO-021 | (SEAL-B-ONLY; | `SecureComputation/SpecialEncryptionSecurity/WrongKey.lean:100` | `SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision` | J3 |
| 9 | S2-BO-024 | (SEAL-B-ONLY; | `SecureComputation/Yao.lean:598` | `SecureComputation.yaoHybrid_callA` | J3 |
| 10 | S2-BO-025 | (SEAL-B-ONLY; | `SecureComputation/Yao.lean:606` | `SecureComputation.yaoHybrid_callB` | J3 |
| 11 | S2-BO-027 | (SEAL-B-ONLY; | `SecureComputation/Yao.lean:809` | `SecureComputation.yaoSeed_good_whp` | J3 |
| 12 | S2-BO-029 | (SEAL-B-ONLY; | `SecureComputation/Yao.lean:1037` | `SecureComputation.yaoHybrid_simulators` | J3 |
| 13 | S2-BO-030 | (SEAL-B-ONLY; | `SecureComputation/Yao.lean:1184` | `SecureComputation.yaoHybrid_hbcSecure` | J3 |
| 14 | S2-BO-036 | (SEAL-B-ONLY; | `Asymptotic/Collections.lean:927` | `Collection.collInverter_success` | J2 |
| 15 | S2-BO-037 | (SEAL-B-ONLY; | `Asymptotic/Collections.lean:987` | `Collection.fiber_le` | J2 |
| 16 | S2-BO-069 | (SEAL-B-ONLY; | `Asymptotic/HardCorePermutation/GoldreichLevin.lean:606` | `ofFn_oddCoins` | J2 |
| 17 | S2-BO-072 | (SEAL-B-ONLY; | `Asymptotic/OneWay.lean:362` | `FunFamily.ofFn_ofString_f` | J2 |
| 18 | S2-BO-073 | (SEAL-B-ONLY; | `Asymptotic/OneWay.lean:375` | `FunFamily.ofString_id_f` | J2 |
| 19 | S2-BO-076 | (SEAL-B-ONLY; | `Asymptotic/OneWay.lean:407` | `FunFamily.prod_f` | J2 |
| 20 | S2-BO-084 | (SEAL-B-ONLY; | `Asymptotic/OneWay.lean:957` | `PermFamily.toFunFamily_f` | J2 |
| 21 | S2-BO-095 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:516` | `Authentication.lamportOWF_f` | J4 |
| 22 | S2-BO-096 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:510` | `Authentication.lamportOWF_inLen` | J4 |
| 23 | S2-BO-097 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:513` | `Authentication.lamportOWF_outLen` | J4 |
| 24 | S2-BO-098 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:901` | `Authentication.lamport_exists_best_position` | J4 |
| 25 | S2-BO-099 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:849` | `Authentication.lamport_forgeGame_accept_eq_honestProbability` | J4 |
| 26 | S2-BO-100 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:784` | `Authentication.lamport_forgerCodec` | J4 |
| 27 | S2-BO-101 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:615` | `Authentication.lamport_gen` | J4 |
| 28 | S2-BO-102 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:823` | `Authentication.lamport_loggedSignImpl_expect` | J4 |
| 29 | S2-BO-103 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:609` | `Authentication.lamport_msgLen` | J4 |
| 30 | S2-BO-104 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:943` | `Authentication.lamport_oneTimeSecure` | J4 |
| 31 | S2-BO-105 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:612` | `Authentication.lamport_sigLen` | J4 |
| 32 | S2-BO-106 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:618` | `Authentication.lamport_sign` | J4 |
| 33 | S2-BO-107 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:808` | `Authentication.lamport_signImpl_expect` | J4 |
| 34 | S2-BO-108 | (SEAL-B-ONLY; | `Authentication/Signatures/Lamport.lean:621` | `Authentication.lamport_ver` | J4 |
| 35 | S2-BO-112 | (SEAL-B-ONLY; | `Candidates/Factoring.lean:702` | `Candidates.fac_prodInverter_eq_yaoB` | J2 |
| 36 | S2-BO-117 | (SEAL-B-ONLY; | `Candidates/Factoring.lean:155` | `Candidates.fmult_f` | J2 |
| 37 | S2-BO-119 | (SEAL-B-ONLY; | `Candidates/Factoring.lean:170` | `Candidates.fmult_inv_factor` | J2 |
| 38 | S2-BO-132 | (SEAL-B-ONLY; | `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean:103` | `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | J4 |
| 39 | S2-BO-142 | (SEAL-B-ONLY; | `Encryption/PublicKey/AdaptiveCPA/Handler.lean:120` | `Composability.AdaptiveCPA.acTapes_apply` | J4 |
| 40 | S2-BO-147 | (SEAL-B-ONLY; | `Pseudorandom/Functions/Asymptotic/Defs.lean:474` | `OracleEnsemble.Indist.negligible_prfAdv` | J3 |
| 41 | S2-BO-150 | (SEAL-B-ONLY; | `Pseudorandom/Functions/Asymptotic/Defs.lean:486` | `prfAdv_toOracleAdversary` | J3 |
| 42 | S2-BO-151 | (SEAL-B-ONLY; | `Pseudorandom/Functions/Asymptotic/Defs.lean:458` | `prfAdv_toOracleAdversary_out` | J3 |
| 43 | S2-BO-153 | (SEAL-B-ONLY; | `Pseudorandom/Functions/Asymptotic/GGM.lean:105` | `thm_97_3_1` | J3 |
| 44 | S2-BO-158 | (SEAL-B-ONLY; | `Pseudorandom/Generators/Asymptotic/FromPermutation.lean:93` | `owpGenPRG_G_castSucc` | J3 |
| 45 | S2-BO-159 | (SEAL-B-ONLY; | `Pseudorandom/Generators/Asymptotic/FromPermutation.lean:98` | `owpGenPRG_G_last` | J3 |
| 46 | S2-BO-168 | (SEAL-B-ONLY; | `Pseudorandom/Generators/Asymptotic/Stretch.lean:61` | `PRG.oneBit_G` | J3 |
| 47 | S2-BO-174 | (SEAL-B-ONLY; | `SecureComputation/Defs.lean:214` | `SecureComputation.otFunctionality_f` | J3 |
| 48 | S2-BO-175 | (SEAL-B-ONLY; | `SecureComputation/Defs.lean:219` | `SecureComputation.otFunctionality_f_snd` | J3 |
| 49 | S2-BO-181 | (SEAL-B-ONLY; | `SecureComputation/YaoReal.lean:95` | `SecureComputation.yaoProtocol_hbcSecure` | J3 |
| 50 | S2-BO-184 | (SEAL-B-ONLY; | `ZeroKnowledge/Commitment.lean:531` | `owpComStr_ofFn` | J6 |
| 51 | S2-BO-191 | (SEAL-B-ONLY; | `ZeroKnowledge/NP.lean:342` | `outV_pullback_cheat` | J6 |

**(b) The fourteen DL-35 changes** (`EnsembleLemmas.blocks`/private `blocks` → `FunFamily.blocks`, definitional). The
lines are at the tip. The proof uses of the aliases are S2-BK-15 to S2-BK-20.

| scope id | ruling | owner file:line (tip) | declaration | change | job |
|---|---|---|---|---|---|
| S2-BK-01 | CS1-Q2 #1 | `Asymptotic/EnsemblesLemmas.lean:815` | `EnsembleLemmas.exists_copiesRed` | statement | J2 |
| S2-BK-02 | CS1-Q2 #2 | `Asymptotic/EnsemblesLemmas.lean:433` | `EnsembleLemmas.ofFn_blocks_symm` | statement | J2 |
| S2-BK-03 | CS1-Q2 #3 | `Asymptotic/EnsemblesLemmas.lean:427` | `EnsembleLemmas.take_drop_ofFn_blocks` | statement | J2 |
| S2-BK-04 | CS1-Q2 #4 | `ZeroKnowledge/CommitmentLemmas.lean:486` | `CommitmentLemmas.ComLoop.emit_init_of_lt` | statement | J6 |
| S2-BK-05 | CS1-Q2 #5 | `Encryption/PrivateKey/OracleFromPRF/Handler.lean:139` | `PRFGame.pkTapes` | body | J4 |
| S2-BK-06 | CS1-Q2 #6 | `Asymptotic/Ensembles.lean:223` | `Ensemble.copies` | body | J2 |
| S2-BK-07 | CS1-Q2 #7 (seventh) | `Encryption/PrivateKey/EncryptThenTag/Handler.lean:179` | `ETTGame.dTape` | body | J4 |
| S2-BK-08 | S1-final Q2 #8 | `Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean:180` | `bTapeOf` | body | J4 |
| S2-BK-09 | S1-final Q2 #9 | `Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean:90` | `bTapes` | body | J4 |
| S2-BK-10 | S1-final Q2 #10 | `Encryption/PrivateKey/EncryptThenTag/Reduction.lean:89` | `dTapes` | body | J4 |
| S2-BK-11 | S1-final Q2 #11 | `Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean:185` | `bTapeOf_eq` | statement | J4 |
| S2-BK-12 | S1-final Q2 #12 | `Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean:94` | `bTapes_eq` | statement | J4 |
| S2-BK-13 | S1-final Q2 #13 | `Encryption/PrivateKey/EncryptThenTag/Reduction.lean:93` | `dTapes_eq` | statement | J4 |
| S2-BK-14 | S1-final Q2 #14 | `Encryption/PrivateKey/EncryptThenTag/Handler.lean:183` | `dTape_eq` | statement | J4 |

**(d) The fourteen definition-body re-points (Q7).** The "proof-only" stage cannot remove a duplicated public
*definition* without changing either its body or its consumers' statements. These rows come from the Stage 1 table, plus
DL-43 and DL-59.

| scope id | ledger | owner file:lines (tip) | definitions (readers re-derived) | promoted form | job |
|---|---|---|---|---|---|
| S2-RP-007 | DL-40 | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:116,122` | freshImpl, freshImpl_apply | Games.freshImpl, Games.freshImpl_apply | J4 |
| S2-RP-008 | DL-40 | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:130,135` | tapeImpl, tapeImpl_apply | Games.tapeImpl, Games.tapeImpl_apply | J4 |
| S2-RP-011 | DL-40 | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:219,224,228,234,246,262,281` | expect_sample_ovr, ovr, ovr_cons, ovr_nil, ovr_of_mem, ovr_of_not_mem, ovr_update | Games.ovr and readers, Games.expect_sample_ovr | J4 |
| S2-RP-013 | DL-40/DL-59 | `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:211,215,221` | extTape, extTape_of_lt, extTape_update | Games.extTape, Games.extTape_of_lt, Games.extTape_update | J4 |
| S2-RP-025 | DL-40 | `Encryption/PrivateKey/EncryptThenTag/Handler.lean:134,139,143,147` | length_recBits, recBits, recBits_none, recBits_some | recordBits, recordBits_none/_some, length_recordBits (S1-07) | J4 |
| S2-RP-026 | DL-40 | `Encryption/PrivateKey/OracleFromPRF/Handler.lean:109,114,117,121` | length_recBits, recBits, recBits_none, recBits_some | recordBits and readers | J4 |
| S2-RP-068 | DL-48 | `SecureComputation/ObliviousTransfer/Simulators.lean:52,57` | splitLen, splitLen_symm_ofFn | (EnsembleLemmas.coinsEquiv h).symm, Asymptotic/EnsemblesLemmas.lean:141, :145 (n | J3 |
| S2-RP-080 | DL-49 | `SecureComputation/ComposeSecurity/Accept.lean:52` | appendCoins | EnsembleLemmas.coinsEquiv | J3 |
| S2-RP-086 | DL-39 | `Randomness/Extraction/Rejection.lean:395,406,413` | mixture, mixture_apply, mixture_isSource | FinDist.mixture and readers (S1-25); consumers Randomness/Extraction.lean:168, : | J3 |
| S2-RP-087 | DL-39 | `Randomness/Extraction/Rejection.lean:144` | tupleEquiv | Mathlib (Fin.consEquiv _).symm (no new form) | J3 |
| S2-RP-097 | DL-49 | `SecureComputation/ComposeSecurity/Machines.lean:223,226,232,239` | length_padTo, padTo, padTo_eq, padTo_poly | EncodingMachines.padTo family | J3 |
| S2-RP-099 | DL-49 | `ZeroKnowledge/ThreeColoring/Machines.lean:303,306,312,316` | getD_padTo, length_padTo, padTo, padTo_poly | EncodingMachines.padTo family | J6 |
| S2-DL-11 | DL-59 | `Pseudorandom/Functions/LazySampling.lean:196` | extendStream,  extendStream_def,  extendStream_update_of_ne,  extendStream_update_self | Games.extTape | J3 |
| S2-DL-17 | DL-43 | `Authentication/Signatures/Lamport/Planted.lean:204` | signatureBlock | FunFamily.blocks n n σ i (blocks_apply) | J4 |

## 2. Job split

### 2.1 Dependency facts that shape the split

- **Readers and promotions first.**
  - 12 of the 74 new readers are used in files outside their home's natural job. These are:
    - `Repetition`'s `iterateFind_elim`, used by `Candidates/Concrete` and `GGM/Reduction`;
    - Q11's two `Encoding.lean` readers, used by `PairSplit`, `UnaryMul` and `Universal`;
    - `Ensemble.distAdv_uniform`, `indist_iff` and `samplable_iff`, used by `PRG/Defs`;
    - `swapAux_apply`, used by `CommitmentLemmas`;
    - `fisherYates_def` and `permFromCoins_def`, used by `EncodingPermutations`;
    - `owpGen_apply`, `owpGenNot_apply` and `owpPair_apply`, used by `Trapdoor`, `FromPermutation` and `Commitment`.
  - The promotions' homes are shared too: `Games/Probability` (DL-43), `Games/Tapes` (DL-59), `IdentityBased/Defs`
    (DL-57), `Foundations/BitLists` (DL-55) and `Games/Efficiency` (DL-56, if a reader is needed).
  - All of these go into one small first job (J0). After it merges, the other jobs are file-disjoint and independent.
- **Same-name moves are atomic.** DL-55 (`TCSlib.Cryptography.decide_singleton_eq_true`) and DL-42
  (`Games.MachineCodec.ext_of_fields`) keep their full names. A REMOVED and an ADDED in different PRs would clash, so each
  move is done in one change: DL-55 in J0, and DL-42 in J4, which then owns `Games/Machines.lean`.
- **W6 first inside the ZK jobs.** All 48 W6-dependent items and all 33 W6 readers live in the ZK files: 29
  BRIDGE-SHADOW items and 19 readers' users. Their fixes are re-derived after the retirement.
  - J5 retires `GI` and `GIZK`; J6 retires `ColProofs` and `ColSimMachine`.
  - The only cross-file coupling is `ThreeColoring/ColRepWitness` importing `GIZK/Simulator`. It uses
    `GIZK.decGraph_eq_of_sqrt`, which is not a shadow and is unaffected.
- **DL-59 with DL-40.**
  - J0 generalizes `Games/Tapes`.
  - J4 re-points `AdaptiveCPA.extTape` (S2-RP-013) together with the DL-40 ETT tools and the `bTapes`/`dTapes` changes in
    the same files.
  - J3 re-points `extendStream` (S2-DL-11; `LazySampling` gains `import …Games.Tapes`, which is acyclic: neither module
    imports the other today).
- **DL-35 alias removal last.** S2-BK-21/22 need every one of the fourteen sites moved first: J2 (#1–3, #6), J4 (#5,
  #7–14) and J6 (#4, and `ColRepSound`'s proof uses). The closer J7 does it.

### 2.2 The jobs

| Job | Route | Owner files (at the tip) | Items | Est. lines | Prerequisites | Gate |
|---|---|---|---:|---:|---|---|
| **J0 Foundations** | in-house (maintainer) | `Games/Probability`, `Games/Tapes`, `Foundations/BitLists`+`TrapdoorPredictor`+`Pairing/Assumptions` (DL-55 move), `IdentityBased/Defs`, `Games/Efficiency` (DL-56 reader, only if needed), `Complexity/TuringMachine/Encoding` (Q11), `Complexity/Randomized/Repetition`; cross-job readers in `Asymptotic/{Ensembles, EnsemblesLemmas, Permutations}` and `Pseudorandom/GeneratorFromPermutation` (12–14 files) | 19 | ~180 | DW-11 sequencing (Q5) | statement-style audit of the new API, combined with DW-11 (Q5a) |
| **J1 Complexity hosts and derandomization** | in-house (rec.; Q13) | `Randomized/Build/{IterateFind, IterateFindHost, PairSplit, UnaryMul}`, `TuringMachine/Build/ModuleHost`, `Randomized/{Primitives, PPT}`, `SeedMajority{,/Enumeration,/State,/Words}`, `Randomness/Derandomization/RootSchedule` (12) | 153 | ~490 | J0 (Q11 readers) | Codex proof audit + 4-variant seals of its owners; checks the 3 `host_*` deletions (DW10-Q9) |
| **J2 Asymptotic layer (ch. 2–4)** | external Claude (lead + 2) | `Asymptotic/*` (21), `Candidates/*`, `Foundations/BitLists`, `Encoding/*`, `Hashing/*`, `HardcoreBit/InnerProduct`, `NumberTheory/*`, `InformationTheory/{Entropy, LeftoverHash}` (38) | 253 | ~1,100 | J0 | Codex proof audit + seals; checks DL-35 #1–3, #6 and 11 B-only headers one by one |
| **J3 Pseudorandom, Randomness, secure computation, composability** | external Claude (lead + 2) | `Pseudorandom/**` (incl. `LazySampling`), `Randomness/**` (not `Derandomization/RootSchedule`), `SecureComputation/**`, `Composability/**` (55) | 183 | ~860 | J0 (DL-59 `Tapes`) | Codex; checks 6 body re-points and 22 B-only headers (Yao, SG-F07, PRF `Defs`, `thm_97_3_1`) |
| **J4 Encryption, authentication, IBE/pairing re-points** | external Claude (lead + 2) | `Encryption/**`, `Authentication/**`, `Games/Machines` (DL-42 move), `AdvancedEncryption/IdentityBased/{BonehBoyenMachine/{Words, Oracles}, BonehBoyenSecurity/Lazy}` (47) | 134 | ~820 | J0 (DL-43, DL-55, DL-57, DL-59 homes) | Codex; checks DL-35 #5, #7–14, 7 body re-points, 16 B-only headers (Lamport ×14), the DL-42 move and `adviceBound` |
| **J5 ZK: graph isomorphism + W6 (`GI`, `GIZK`)** | external Claude (lead + 2) | `ZeroKnowledge/GraphIsomorphism{,/*}`, `GraphIsomorphismZK{,/*}` (12), plus 1–2 new `…/Defs.lean` modules and facade lines | 136 | ~1,500 (W6 ±40%) | J0 | Codex; decls2 of the W6 moves and restatements checked one by one; seals of every ZK owner it touches |
| **J6 ZK: three-colouring, shared ZK + W6 (`ColProofs`, `ColSimMachine`)** | external Claude (lead + 2) | `ZeroKnowledge/ThreeColoring/*` (11), `ZeroKnowledge/{Defs, NP, NPLemmas, InteractiveProofs, Interaction, Commitment, CommitmentLemmas, Encoding, EncodingMachines, EncodingPermutations}` (21), plus 1–2 new modules | 212 | ~1,450 (W6 ±40%) | J0 | as J5; checks DL-35 #4 and the `padTo` body re-point |
| **J7 Closer** | in-house | `Asymptotic/Ensembles`, `Asymptotic/EnsemblesLemmas` (alias removal); records (ledger closure, DW-9/DW-10/PS10 rows) | 2 (+ records) | ~30 | J2, J4, J6 merged (all fourteen DL-35 sites moved) | **the Stage 2 gate** (§2.4) |

Totals: J0–J7 hold 1,092 items and about 6,400 lines over 193 existing files, plus up to 4 new W6 modules. The maximum
external job is about 1,500 lines (J5). J5 and J6 carry the W6 uncertainty. If either looks larger at checkpoint 1, its
W6 retirement can be split out (W6-GI alone is about 700 lines) as a predecessor job on the same files.

### 2.3 Waves and merge order

1. **Wave 0.**
   - DW-11's gate is dispatched now (Q5).
   - J0 is in-house, on the tip after the snapshot-#7 adoption.
   - J0 is validated by one merged-tree replay. It is deep: `Encoding.lean`, `Games/*` and `Foundations/BitLists`
     rebuild almost the whole closure, `DetMod` included. J0 merges when the gate clears.
2. **Wave 1 (parallel, file-disjoint).**
   - J2–J6 go to external Claude workers, and J1 is in-house.
   - All are pinned on the post-J0 tip, each with its own `CHANGED`/`DOWN` closures and the snapshot replay recipe
     (`workflow.md` §6.1).
   - If worker or replay capacity is short (local hosts run 3 Lean processes at most), dispatch J5, J6 and J2 first,
     since they are the longest. J3 and J4 follow.
3. **Merge order.**
   - J2 merges first, because it is the deepest (`Asymptotic`).
   - J1, J3 and J4 follow, then J5 and J6.
   - Each later merge re-replays its own closure on the newest snapshot.
4. **Wave 2.** J7 (in-house), then the Stage 2 gate, then Stage 3.

### 2.4 Gates

- **Per-job gate (Codex, standing route).** Each gate contains:
  - a proof audit;
  - decls2, checked against the job's approved list (§1.3), with no other CHANGED or REMOVED;
  - canonical seals A/B, strict and coe, on every owner the job touches, with targets coe-A = coe-B = 0;
  - strict-only failures reported;
  - W5 `local irreducible` lines reported separately (W5);
  - the admissions count, the axioms of the named targets, and lint.
- **The Stage 2 gate (with J7)** is the stage-level check of `cleanup-stages.md`:
  - the full Rule 10 seal sweep over the union of touched owners, after all merges;
  - the union decls2 equal to §1.3's list;
  - every ledger row named in Stage 2 closed (DL-35, DL-38–49, DL-51, DL-52, DL-55–57, DL-59, DL-60 B3/B4), each with a
    closing note where part of it was ruled out (DL-38 loops, DL-45 renames, DL-44 F-03; see Q11);
  - DW-9 and DW-10 closed;
  - PS10 Tier A at 0;
  - `IterateFind` sealed clean.
- **Alternatives:** the stage plan's literal form, two jobs and one gate (Q1b), or a single end gate (Q1c).

### 2.5 Maintainer pre-dispatch work (static, for the briefs)

- The 8 non-W6 readers without a concrete statement (F07) need statements. Two of them are J0's (`indist_iff`,
  `samplable_iff`, in `Ensembles.lean`). The others are:
  - `lengthRegular_iff`;
  - `YaoMachine.sampleAll_eq` and `yaoRaw_eq`;
  - `queryOf_eq_some_iff_decode`;
  - `trialIdx_def`;
  - `giProver_next`.
- The 20 W6 readers are redesigned by the Q9 ruling.
- **28 needs-check items** (F06) go first in their jobs as probes. They are in `OneWayYao` 8, `HardCore/Functions` 4,
  `EnsemblesLemmas` 3, and 2 each in `Hybrid`, `TrapdoorPredictor`, `CommitmentLemmas`, `SoundnessRepGI` and
  `Simulator`, plus `UnaryMul`, `Primitives` and `Primality`.
- **B-only recipe.** The inventory gives no fix text for the 194 rows ("separate ruling"). The brief must give the
  pattern: use `PolyExpr.eval_var`, `eval_const`, `eval_add`, `eval_mul`, `eval_pow` and `eval_normal`
  (`Randomized/PolyExpr.lean:116–131`) instead of definitional unfolding, and add casts in headers for the 51 rows.
  Each worker probes before writing.
- **The brief must locate:** DL-38's local `have` (`OracleFromPRF.lean`), DL-57's exact homes and names
  (`IBEScheme.sidSpec_*`), DL-56's obstruction, the W6 restated-lemma list, and line numbers at each job's issue base.
- **The DL-60 B3 route** (Q15) and the body-re-point form (Q7) go into the briefs as rulings.

## 3. Interactions with in-flight work

| In-flight | Files | Overlap with Stage 2 | Sequencing |
|---|---|---|---|
| **GSW 6a landing** (#358/#359/#360; `land/gsw-6a-fills`, local head `ccca6f804552f72b400c09e7a3bd694371bdf568`, phase 2 on snapshot #6) | `Complexity/CircuitComplexity/**` (`Basic`, `Adder`, `TreeDAG`, `FormulaArith/*`, `NANDForm`, `NANDLayering`, …), `Complexity/BranchingPrograms/**`, `ComputationalModels.lean`, `machine-library-design.md` | **No owner file in common.** Shared downstream: `SecureComputation/{Yao, Garbling}`, `Yao/HybridProof/*` and `Complexity/Randomized/*` import `CircuitComplexity` (J1, J3 closures). | Snapshot #7 adoption waits for the 6a re-replays (records row 885). **Pin Stage 2 bases after #7 is adopted. Preferably also after the 6a PRs merge, so J1/J3 replays include them; otherwise whichever merges second re-replays (§6.1).** DL-54 touches `FormulaArith/Combinators.lean` (a 6a file), so it cannot run before 6a lands (Q6). |
| **`gsw-6b-statements`** (external; base `3e51b5f2`) | new `GSW/*` files, `LWE/Ratio`, `LWE/BitEncoding`, facades `LWE`, `GSW` | none (no Stage 2 item in GSW/LWE; DL-50 out) | none beyond the snapshot. Its Gate 46 is independent. |
| **Complexity handoff** (Arora–Barak; held until the `main` merge) | the 21 handed-off files | Q11 only: two insertions in `Complexity/TuringMachine/Encoding.lean` (J0). **The Arora–Barak branch `complexity/arora-barak-ch3-4` also changes `Encoding.lean`**, so expect a merge interaction at `main` | Insert the readers next to their definitions as pure additions. Tell the handoff chat (DW10-Q11). Add DW10-F11's id crosswalk when the handoff is released. DL-60 B2 stays with the handoff. |
| **DW-11** (combined small gate: #351, #352) | #351 `Games/Probability.lean` (`ProbComp.abs_expect_sub_le_expect`), `Games/Relational.lean`; #352 `Pairing/Group.lean` | J0 adds `mul_prob_le_expect` to `Games/Probability.lean` and re-points `Pairing/Assumptions` (DL-55). J4 re-points the ETT averaging copy onto #351's lemma | DW-11 must clear before J0 merges and before J4 is issued (a DW-11 landing edit to `Games/Probability` would otherwise race J0 or J4). Recommended: fold J0 into DW-11 as its third member (Q5a). |
| **Snapshot / host capacity** | — | J0 is a near-full rebuild; the wave-1 replays overlap the 6a replays | One replay per tree; at most 3 Lean processes per local host (`workflow.md` §4.1); in-house J1/J7 coordinate slots with the 6a jobs. |

## 4. Questions for Seyoon (recommended option first)

- **Q1. Job split and gating.**
  - **(a) Recommended:** eight packages as in §2.2:
    - J0, J1 and J7 in-house; J2–J6 to external Claude workers;
    - one Codex gate per job;
    - the Stage 2 gate with J7.
    - This amends `cleanup-stages.md`'s "one external job, or two with disjoint file sets" and "gates only between
      stages". Stage 2 is about 6,400 lines, so the ≤ 1,500-line target cannot hold with two jobs.
  - (b) The stage plan as written: two external jobs, ZK + Pseudorandom/SC/Composability (~3,300) against the rest
    (~3,100), each about twice the size target, with one Stage 2 gate.
  - (c) (a)'s jobs with no per-job gates, and one Stage 2 gate over everything at the end. This means fewer gates but
    later feedback and a very large audit.
- **Q2. The 51 statement-level SEAL-B-ONLY fixes.**
  - **(a) Recommended:** they ride with their owner-file jobs (J2 11, J3 22, J4 16, J6 2). Each job's gate checks its
    listed headers one by one, and the Stage 2 gate re-checks the union against §1.3(a). This keeps one owner per file
    and touches each file once.
  - (b) One dedicated statement job after wave 1 merges, with one statement gate. The audit is cleaner, but 20 files are
    touched twice and the job is sequential.
  - (c) As (a), but the six headline targets (`lamport_oneTimeSecure`, `yaoProtocol_hbcSecure`, `yaoHybrid_hbcSecure`,
    `thm_97_3_1`, `specialScheme_multiMessageSecure`, `garbling_good_whp`) wait for a separate statement gate.
- **Q3. PS10 Tier A (40 sites).**
  - **(a) Recommended:** ride with the owner-file jobs: J1 20 (A1, A2), J2 1 (A8), J3 13 (A5, A9–A13), J4 6 (A3, A4, A6,
    A7). They are docstring-only, so each gate checks them against the REPORT's corrections.
  - (b) One docs-only pass in J7 after every owner job has merged. This is file-safe, but it delays the fixes.
  - (c) A docs-only external job now. Not recommended: it would share owner files with the running jobs.
- **Q4. PS10 Tier B.**
  - **(a) Recommended:** apply all 21 advisory sites plus the 6 related-note sites (REPORT §3). Each labels a repository
    step as the book's (or, for the related notes, misstates a hypothesis or bound), which changes what a reader is told.
    The fix in each case is the REPORT's "repository step" marker. `Signatures/Defs.lean:156` stays as it is.
  - (b) Apply the 21 only.
  - (c) Record them and change nothing.
- **Q5. DW-11 timing.**
  - **(a) Recommended:** dispatch DW-11 now and add J0 to it as a third small member. J0 touches #351's file
    (`Games/Probability`) and is additive. J0 merges when DW-11 clears, and J4 is issued after that.
  - (b) Dispatch DW-11 now, separately; J0 gets its own small gate.
  - (c) DW-11 after Stage 2. Not recommended: J0 and J4 edit #351's file, and J4 re-points onto #351's lemma.
- **Q6. DL-54 (the `reidx` move, lattice).**
  - **(a) Recommended:** leave it to the lattice campaign, as the ledger says ("out of the Pass–shelat cleanup"). It
    targets `FormulaArith/Combinators.lean`, a 6a landing file, and can only follow the 6a merge.
  - (b) Fold it into Stage 2 as an in-house item after the 6a fills merge, gated with J7.
- **Q7. Duplicate public *definitions* (14 rows, §1.3(d)).**
  - **(a) Recommended:** approve them as the same kind as the fourteen `blocks` changes:
    - each old definition becomes `:=` its promoted form (definitional);
    - its lemmas are re-derived from the promoted readers;
    - consumers are unchanged;
    - each body is listed and checked by its gate.
    - The old public names stay, because consumers' statements use them (some outside the campaign, for example the IBE
      files that use `AdaptiveCPA.extTape`).
  - (b) Leave the old definitions untouched, add `rfl` bridge equations, and re-derive their lemmas only. This is
    proof-only, but the duplicate definitions remain and the rows stay partly open.
  - (c) Delete the old definitions and restate every consumer. This means many more statement changes, including IBE
    statements (`BonehBoyenMachine/{Handler, Reduction}`).
- **Q8. DL-59 shape.**
  - **(a) Recommended:**
    - generalize `Games.extTape`, `extTape_of_lt`, `extTape_of_not_lt` and `extTape_update` to `Type*` (a universe-only
      statement change of #355 API, in J0);
    - `AdaptiveCPA.extTape` and `extendStream` become body aliases under Q7(a), and `LazySampling` imports
      `Games.Tapes`;
    - their own lemmas are re-derived;
    - `extendStream_update_self` and the private `combine` lemmas stay as `LazySampling`'s local API.
  - (b) Keep `Games.extTape` at `Type`, and re-point only `AdaptiveCPA.extTape`; `extendStream` stays separate. This
    contradicts DL-59's "one family".
- **Q9. W6 design (retire the four shadows).**
  - **(a) Recommended:**
    - move each canonical definition verbatim (same full name) into a new lower module that both the main file and the
      proof file import (for example `GraphIsomorphism/Defs.lean`);
    - restate the shadow-namespace lemmas (`GI.*`, `ColProofs.*`, `GIZK.*`, `ColSimMachine.*`) over the canonical names;
    - delete the shadow definitions;
    - the main files' frozen theorem statements stay byte-identical, and the over-limit main files shrink;
    - the brief lists every moved definition and every restated lemma, and decls2 must match.
  - (b) Promote the shadows in place: rename `GI.X` → `X` in the proof file and delete the main file's definitions.
    The net effect is the same, but the definitions' homes and docstrings move into the proof files.
  - (c) Re-rule W6 back to bridges (the inventory's option a).
- **Q10. DL-43 against Q8 for `lamport_oneTimeSecure`.** The DL-43 ledger row says the frozen restatement "needs its own
  gate". Q8 puts all 16 Lamport B-only rows into Stage 2 under its gate.
  - **(a) Recommended:** Q8 supersedes. The restatement rides with J4 and is checked individually by J4's gate (and
    again by the Stage 2 gate).
  - (b) Keep DL-43's own gate for that one statement (with Q2c).
- **Q11. DL-38 remainders.**
  - **(a) Recommended:**
    - Stage 2 does the located small folds: `acHandler_impl_forward` → `impl_of_query`, `pkHandler_finish` →
      `finish_of_ret`, the local `polyTimeComputable_ansRead` `have`, `Primality.ofFn_chunk`,
      `ColRep.drop_take_ofFn_blockRead` and `fac_ofFn_halves` → `FunFamily.ofFn_blocks`.
    - The five iterate-and-emit loops (`BlockEncryptor`, `CopiesLoop`, `StretchMachine`, `ComLoop`, ZK
      `EncodingMachines`) → `Games.iterEmit` are recorded as relatives (as under CS1-Q10), and DL-38 closes with that note.
    - DL-45's renames and DL-44 F-03 close the same way.
  - (b) Include the loop folds as well: machine-proof rewrites, about 300–600 more lines across J2, J3 and J6.
- **Q12. Ledger rows DL-1 to DL-29.** Their statuses are stale: "scheduled", "noted", "rest noted". `cleanup-stages.md`
  scopes Stage 2 to DL-35, DL-38–49, DL-51 and DL-52 (and the later rows), but its gate target is "every Pass–shelat
  ledger row closed".
  - **(a) Recommended:** a records-only reconciliation in J7 marks each row paid (with the PR: #203, #232, #248, #298, …)
    or deferred with its reason (DL-21/22 Mathlib, DL-20 `main` landing). The gate then checks that the ledger has no
    open Pass–shelat row without a ruling.
  - (b) The gate checks only the rows named in Stage 2.
- **Q13. J1 routing (Complexity hosts, DW-9; 12 campaign-created Complexity files).**
  - **(a) Recommended:** in-house, continuing DW-5/DW-9 (the maintainer knows the host typed views).
  - (b) An external Claude worker.
- **Q14. Issue base.**
  - **(a) Recommended:** J0 starts on the tip once snapshot #7 is adopted, and wave 1 on the post-J0 tip. If the 6a PRs
    (#358/#359/#360 and the 6a fills) have merged by then, include them.
  - (b) Issue everything now on `a1fa7b65`'s Lean, and re-replay at merge.
- **Q15. DL-60 B3 (`padTo` against `List.takeD`).**
  - **(a) Recommended:** keep S1-27's `padTo` body. Add a bridge reader `padTo_eq_takeD`, which is additive, and
    re-derive the `padTo` lemmas from Mathlib's `takeD_length`, `takeD_eq_take` and `takeD_left'` (proof-only).
  - (b) Restate `padTo := List.takeD …`, a body change of gated #355 API, under Q7(a).

## 5. Ambiguities and contradictions in the inputs

- **A1. Stage size against the stage rule.** `cleanup-stages.md` allows one or two jobs per stage, with rebuilds and gates
  only between stages. Stage 2's scope grew afterwards: DW-10 brought 785 seal items, W6 retirement and Q8 statement
  fixes; PS10 brought 67 sites. The ≤ 1,500-line job target therefore needs about seven jobs (Q1).
- **A2. "Proof-only" against the content.** Stage 2 has 89 freeze-visible items (§1.3). The fourteen DL-35 changes, Q8's
  51 headers, the moves and the deletions are approved. The 14 definition-body re-points, the W6 design and DL-59's
  universe change are not yet approved (Q7–Q9).
- **A3. GSW/IBE scope.** The stage plan's header puts GSW and IBE out of scope. Later rulings put IBE/pairing items into
  Stage 2: DL-55 (pairing T1), DL-56 and DL-57. DL-59's `AdaptiveCPA.extTape` is also used in IBE statements and bodies
  (`BonehBoyenMachine/Handler.lean:843`, `Reduction.lean:68`). These are outside the campaign, so under DL-59 they force
  the alias to stay (Q7a/Q8a). The IBE work has merged (#346, #357) and those files are free.
- **A4. Headline statements.** Q8's statement-level rows include campaign headline targets (§1.3a). Stage 3's census,
  axiom prints and completion record must then use the restated headers. DL-43 asked for a separate gate for one of them
  (Q10).
- **A5. B-only fixes are undetermined.** The inventory's fix text for every SEAL-B-ONLY row is "separate ruling". Q8 came
  after the inventory, so no reader or route is proposed for these 194 rows. They need a recipe and probes (§2.5).
- **A6. W6 against the derivative.** The derivative's 29 BRIDGE-SHADOW fixes and 33 `GI.*`/`ColProofs.*`/`GIZK.*`/
  `ColSimMachine.*` readers assume bridges (option a). Under retirement they are re-derived on the canonical owners. 20 of
  those readers have no statement anyway (F07). The derivative's fix text does not apply to those 48 items.
- **A7. Over-limit files.**
  - `GraphIsomorphism.lean` has 1,004 lines, `ThreeColoring/Simulator.lean` 1,664 and `ThreeColoring/Protocol.lean`
    1,362, against a 1,000-line limit.
  - Readers added there grow them; W6 moves shrink them.
  - The briefs should state the inherited size exceptions and forbid net growth past the base.
- **A8. Reader homes in handed-off files.** Q11's two readers go into `Encoding.lean`, which the Arora–Barak branch also
  changes (§3). Q1 handed the file off; Q11 permits pure insertions.
- **A9. Same-name moves.** CS1-Q3 (DL-42) and DL-55 promote by moving a declaration that keeps its full name. A split
  REMOVED/ADDED across PRs would clash, so each move must be atomic (§2.1). DL-42's target `Games/Machines.lean` is a
  shared `Games` file.
- **A10. Records gaps.**
  - DL-38's "opportunistic folds" have no `path:line` in any record. They are located here, except the local `have` in
    `OracleFromPRF.lean`.
  - `BobIO:218` (the `simpa` nit) is also an uncatalogued DL-47 getD chain.
  - Ledger rows DL-1 to DL-29 have stale statuses (Q12).
  - DW10-F14's cosmetic change texts are records-only.
- **A11. DL-57 bodies.** The bb1-sim fill's copies (`BonehBoyenSecurity/Lazy.lean:89–99`, public) are "re-pointed",
  which means re-derived from `IBEScheme.*` with their names kept. T4's private copies (`Oracles.lean:77`, `:84`) are
  deleted. The ledger does not say whether the public fill names should go. This plan keeps them, as proof-only.
- **A12. Stage 2's seal target with seal B.** The "no seal failure in any touched file" target now covers coe-B (Q8).
  Strict-only failures (Q3) and W5 lines are reported, not failed. The gate brief must state this explicitly; the stage
  plan predates Q8.

## 6. `scope.tsv` columns

| column | meaning |
|---|---|
| `id` | `S2-RP` Stage 1 table and addendum, `S2-BK` DL-35, `S2-DL` other ledger and nit rows, `S2-SL` DW-10 seal items, `S2-RD` new readers, `S2-W6` shadow retirements, `S2-BO` SEAL-B-ONLY, `S2-PA`/`S2-PB`/`S2-PR` PS10 Tier A / Tier B / related notes |
| `source` | ledger row or ruling, plus the upstream record id (inventory item id, table source) |
| `owner_file`, `tip_line` | at `2be7eb20`. `new` means a new declaration; `?` means the brief locates it. W6 rows name the shadow file and the main file |
| `declaration` | at the tip (the enclosing declaration for inline sites) |
| `kind` | `re-point`, `re-point (definition body)`, `delete`, `promote`, `add reader`, `retire shadow`, `seal fix (proof-only)`, `seal fix (after shadow retirement)`, `B-only fix proof-level`, `B-only fix statement-level [freeze exception]`, `alias change`, `citation fix`, `citation fix (advisory)`, `doc nit` |
| `statement_change`, `freeze_ref` | `no`, or what changes and the ruling that covers it (`Q-DEF (proposed)`, `Q-W6 (proposed)` and `DL-59 (proposed Q)` are Q7, Q9 and Q8 here) |
| `depends_on` | readers (`S2-RD-*`) and W6 (`S2-W6-*`) for items, otherwise the job-level prerequisite |
| `est_lines` | heuristic changed lines (§1) |
| `job` | §2.2 |
| `target`, `notes` | the promoted form or fix text, the confidence (`needs-check`), and corrections (F02/F03) |

Regenerate the scope from the records checkout with:

```
python3 -I tools/build.py <scratch> <out>
python3 -I tools/jobs.py <scratch> <out>
```

`<scratch>` must hold:
- `s1/repoint.tsv` (from the exchange, as pinned);
- `inv/inventory.tsv` (from the exchange, as pinned);
- `dw10ev/outputs/stmtcheck.txt` (from the DW-10 review evidence ZIP).

The scripts read git objects only.
