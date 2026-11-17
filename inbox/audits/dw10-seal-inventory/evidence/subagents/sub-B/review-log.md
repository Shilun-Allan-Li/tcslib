# sub-B review log (DW-10 classification review)

Agent: sub-B. Inputs: EV = /home/user/dw10/sub/snap-r1 (frozen), WT = /home/user/dw10/subB (read-only, base).
Output: `overrides-sub-B.tsv` (120 rows, one per open item with agent `sub-B`), this log, helper scripts in `scripts/`
(Python run as `python3 -I`; `scripts/rows.json` is a copy of the 120 rows, `scripts/owners.txt` is the owner set
derived from `seals/queue.txt`, 434 files). No Lean, lake, git or network was run.

## Scope and method

- The `agent` column holds `sub-B`, not `B` (the brief's literal filter matches 0 rows). Per the coordinator's correction, the
  120 `sub-B` rows were reviewed.
- Reader index: `readers/readers-v4.json` (coordinator's instruction). Every reader named in the overrides was checked against it
  and against WT sources. Re-checking the earlier rows against v4 changed none of the conclusions. v4 adds no definitional reader
  for the definitions marked "add" below: GGMRed.start, buildTreeQ case forms, ggmBitsDist/ggmDist/tableDist/levelAdv,
  Ensemble.Indist (definitional), Ensemble.Samplable, prgStep, owpPair, owpGen, owpGenNot, expandRedMachine coins.
- For each seal item I read the declaration's coe-A errors in `seal-errors.jsonl` (all of them, not only the first), the goal in
  the message and the tactic at `source_line` in WT. The header was compared with the error position: line plus the term or
  tactic that fails.
- Owner status was taken from the seal queue. Every provider named in a fix is in an owner file (Randomized/*, Cryptography/*), or
  the reader already exists outside the campaign (ClassNP/PolyTimePairing, TuringMachine/Encoding). So no row needed
  STAGE2-PROVIDER-READER.
- Note on line numbers: the `record` column of H:/SEAL- rows uses an older numbering (for example Stretch "l.493/494").
  `seal-errors.jsonl` source lines match WT and were used throughout.

## Items per file (tool class -> reviewed class)

| file (under TCSlib/Cryptography) | rows | tool class | result |
|---|---|---|---|
| Encryption/PrivateKey/{EnsembleSecurity,FromPRF,FromPRF/MultiMsgOut,FromPRF/ReductionMachine,FromPRG} | 13 | SEAL-B-ONLY | confirmed |
| Encryption/PublicKey/{AdaptiveCPA/Handler,EnsembleSecurity,OracleSecurity} | 6 | SEAL-B-ONLY | confirmed |
| Encryption/PublicKey/EnsembleSecurity | 10 | STAGE2 | class kept; 6 fixes changed |
| Encryption/PublicKey/Hybrid | 5 | STAGE2 | class kept; all fixes changed |
| Encryption/PublicKey/HybridMachine | 2 | STAGE2 | class kept; fix changed |
| Encryption/PublicKey/Trapdoor | 6 | STAGE2 | 4 confirmed, 2 fixes changed |
| Encryption/PublicKey/TrapdoorPredictor | 4 | STATEMENT | all -> STAGE2 (statement_level no) |
| Games/Probability | 1 | STRICT-ONLY | confirmed |
| Pseudorandom/Functions/Asymptotic/{Defs,GGM} | 7 | SEAL-B-ONLY | confirmed |
| Pseudorandom/Functions/Asymptotic/GGM/Reduction | 7 | STAGE2 | class kept; all fixes changed |
| Pseudorandom/Functions/Asymptotic/GGM/Run | 20 | 17 STAGE2, 2 STATEMENT, 1 SEAL-B-ONLY | STATEMENT -> STAGE2; STAGE2 fixes changed |
| Pseudorandom/Functions/{GGM,SubHybrids} | 2 | STAGE2 | kept; HARNESS note |
| Pseudorandom/Generators/Asymptotic/Defs | 7 | STAGE2 | 2 confirmed, 5 fixes changed |
| Pseudorandom/Generators/Asymptotic/FromPermutation | 14 | 11 SEAL-B-ONLY, 3 STAGE2 | B confirmed; 1 confirmed, 2 fixes changed |
| Pseudorandom/Generators/Asymptotic/Stretch | 15 | 7 SEAL-B-ONLY, 6 STAGE2, 2 STATEMENT | B confirmed; STATEMENT -> STAGE2; 4 fixes changed |
| Pseudorandom/Generators/Asymptotic/StretchMachine | 1 | SEAL-B-ONLY | confirmed |

Totals: 120 rows. 58 rows are marked CHANGED: 8 class changes (all STATEMENT -> STAGE2, statement_level yes -> no) and 50
STAGE2 rows with only the fix changed. 60 rows are confirmed (13 STAGE2 including C1-0277, 46 SEAL-B-ONLY, 1 STRICT-ONLY), and
2 are HARNESS. Final classes: STAGE2 73, SEAL-B-ONLY 46, STRICT-ONLY 1, STATEMENT 0.

## Patterns found

1. **Line-only STATEMENT verdicts are wrong when the proof shares the last header line.** All 8 STATEMENT rows fail in the proof:
   - `GGMRed.start_rawInput` (one line, `:= rfl`) and `PRG.expand_G` (`... := rfl` on line 116) fail on the `rfl` term.
   - `tdpPredictor_runAtL` and `uprob_tdpPredictor` report "unsolved goals" at the `by` that ends the header line. The goal
     shown is the one the closing simp leaves.
   In every case the statement mentions only local definitions, or foreign definitions without unfolding them, and it
   elaborates. None of these needs Seyoon as a statement ruling.
2. **The tool's single-reader pick often names a definition that occurs identically on both sides.** Examples:
   - verdictOf in concrete_zero; histEnc in move_eq; coinBlock in blockEncFun_flatten and bitwise_enc_runAtL.
   - Negligible in pseudorandom_iff_prgAdv and secure_iff; PolyTimeComputable in stateLoopFun_poly, lookup_poly and prg_expand.
   - inArg in bitwiseEncFun_poly.
   The definition actually read was taken from the goal instead.
3. **Sealed matchers in foreign statements or readers:**
   - `Complexity.polyTimeComputable_iterateFind.match_1` (stateLoopFun_poly, lookup_poly; same as the lead's C3-0004 in
     Concrete). One reader in Repetition.lean in `Option.elim` form fixes all of them.
   - `GGMRed.buildTreeQ.match_1`, left by the buildTreeQ_zero/succ readers (concrete_zero/succ). Case readers on
     `queryOf ... = none/some` are needed in Reduction.lean.
   - `GGMRed.queryOf.match_1` (eqn items). A reader on `queryOf ... = some x` in Reduction.lean is needed.
4. **NUPPT activation layout:** the goal `output (layout (replicate n true) y a r) = output (pairEncode (pairEncode (advInput n y) a) r)`
   (runAt_ggmRedMachine, bitwise_enc_runAtL, blockEncFun_flatten, move_eq) needs `NUPPT.layout_eq` + `NUPPT.advInput_eq`
   (+ `NUPPT.coinLen_eq` where `coins.eval n` meets `coinLen n`), or `NUPPT.runAtL_eq_output_layout`. Tool picks such as
   `uniform_iff` and `coinLen_eq` alone do not close these.
5. **GeneratorFromPermutation has no field readers** for owpPair/owpGen/owpGenNot. Three readers in that file (`owpPair_apply`,
   `owpGen_apply`, `owpGenNot_apply`) cover 7 rows: FromPermutation and Trapdoor.
6. **distAdv/acceptProb:** `abs_nonneg`/`abs_sub_comm` against `distAdv` -> `distAdv_def` (5 rows confirmed). A `rfl` between
   distAdv of encoded samples and distAdv with an encoding distinguisher is exactly the published `distAdv_comp`.
7. **Ensembles.lean** lacks a definitional reader for `Indist` and for `Samplable`. One `samplable_iff` and one `indist_iff` (plus
   `distAdv_uniform`) cover the Generators/Defs rows.
8. **SEAL-B-ONLY (46) and STRICT-ONLY (1):** counts fit the classes in every row (coe_A = strict_A = 0 < coe_B; resp.
   coe = 0 < strict). The B messages show `PolyExpr.eval` conversions. NEW:148, 157, 159, 160 and 163 do not print PolyExpr
   in the first B message; their declarations depend on B-failing definitions (owpGenPRG, truncate, ...) and are cascades.
   Kept as is.

## Readers to add (all in owner files), with the rows they cover

- TCSlib/Complexity/Randomized/Repetition.lean: `polyTimeComputable_iterateFind_elim` (SEAL-0207, EFF72:SEAL-0207, SEAL-0209).
- .../GGM/Reduction.lean: `buildTreeQ_of_queryOf_none`, `buildTreeQ_zero_of_queryOf_some`, `buildTreeQ_succ_of_queryOf_some`
  (H:55, H:56, SEAL-0211..0214); `start_eq`, `tblOf_nil` (H:57, SEAL-0215, and SEAL-0217 through it);
  `queryOf_eq_some_iff_decode` (C3-0002, C3-0003, NEW:294).
- Pseudorandom/Functions/GGM.lean: `ggmBitsDist_apply`, `ggmDist_eq`, `levelAdv_apply`. SubHybrids.lean: `tableDist_apply`
  (H:61, SEAL-0219).
- Asymptotic/Ensembles.lean: `Ensemble.indist_iff`, `Ensemble.distAdv_uniform` (SEAL-0260, SEAL-0263 through it);
  `Ensemble.samplable_iff` (SEAL-0264/0265).
- Pseudorandom/Generators.lean: `prgStep_eq` (H:64, SEAL-0223, SEAL-0225 through expand_G).
- Generators/Asymptotic/StretchMachine.lean: `expandRedMachine_coinsEquiv` (SEAL-0226).
- Pseudorandom/GeneratorFromPermutation.lean: `owpPair_apply`, `owpGen_apply`, `owpGenNot_apply` (H:63, H:111-113,
  SEAL-0221/0222, SEAL-0272-0274).

## Unresolved or low-confidence cases

- **SEAL-0277 (Hybrid.exists_hybridBound l.322)** and **SEAL-0279 / H:117 (tdpPredictor_runAtL l.114):** the residual goal
  prints as `decide P = decide P`, with identical sides. The difference is in hidden arguments (a stale Decidable instance or an
  implicit coin length). I cannot name the read without the infoview (`set_option pp.explicit true`). The class is STAGE2 (the
  failure is in the proof); the fix is "to be identified". In tdpPredictor_runAtL the closing `simp` is not `simp only` and
  the simp lemma `decide_eq_decide` did not close it. So the difference is probably inside P, not only in the instance.
- **SEAL-0280 / H:118 (uprob_tdpPredictor):** the local `ite_eq_xor_not` did not fire on `if decide (...) = true then c else !c`.
  The suggested reorder (rewrite the ite before unfolding distinguisherL) is a hypothesis.
- **SEAL-0226 (prg_expand l.230):** the tool marks it as a cascade. I read it as independent: a `Fin.appendEquiv` at the
  machine's coin type needs the expandRedMachine coins field. The suggested `expandRedMachine_coinsEquiv` is a new equivalence
  plus its ofFn lemma, more than a one-line field equation; the maintainer may prefer a simpler `coins_expandRedMachine`
  (+ `NUPPT.wrapCoinsEquiv`).
- **C3-0002 vs NEW:294:** both name `queryOf.match_1.eq_2` (C3-0002 under the old module prefix GGMReductionEval, with
  evidence eqrefs.tsv:2, which is the splitter line). These look like duplicates: lead to dedupe.
- **NEW:150 / NEW:151** (`<outside src:68>`, GGM.lean and SubHybrids.lean): the tool's class and fix are kept. The note
  marks them HARNESS: inherited_source_attribute_interaction (lead decides), as instructed. The message confirms that the
  file's own `attribute [local irreducible] uprob acceptProb` meets the seal.
- **SEAL-0263 / SEAL-0217 / SEAL-0225** depend on in-file theorems that are themselves open: pseudorandom_iff_prgAdv,
  start_rawInput and PRG.expand_G. They are fixed by reusing those once repaired. No separate reader is needed.
- **SEAL-0271 (multiMessageSecure l.455):** reported as "unsolved goals" at the theorem's `by`. I attribute it to the final
  `exact hB ...`, which needs multiDist/singleDist = pkMultiEncDist/pkEncDist (`multiDist_eq`, `singleDist_def`) and PolyExpr
  arithmetic. The exact failing sub-step is inferred, not printed.

## Surprises

- The brief's AGENT filter (`B`) matched no row; the column value is `sub-B`.
- The record column's line numbers lag WT by a constant offset in several files (for example +378 in Stretch). Evidence
  pointers (log line numbers) are consistent with `seal-errors.jsonl`.
- `Complexity.pairFstD_nil` exists (ClassNP/PolyTimeBlockLoop.lean), but no public `pairSndD_nil` exists in a provider
  file: there is only a private one in BlockEncryptor and `pairSndD_nil'` in SecureComputation/ObliviousTransfer/Efficiency.
  Hence the two-lemma form `pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil`. A public `Complexity.pairSndD_nil` next to
  pairSndD in PolyTimePairing.lean would be the cleaner reader (provider outside the campaign), if the maintainer wants it.
