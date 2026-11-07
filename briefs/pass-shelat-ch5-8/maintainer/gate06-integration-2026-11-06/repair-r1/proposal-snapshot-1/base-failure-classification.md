# Gate06 base-failure classification: three completed head seals

**Frozen head:** `e9d64158461bfe24ddc88ab885bc4017899b4c16`. **Actual comparison base:** `c7d8753a548ced71c1e1ea70e012c365af5c2171`.
**Result:** 16 diagnostics in 15 declarations; every failing declaration is truly untouched
at source level. None is new or code-edited against this base. **All three sealed modules
still failed**; this classification is not a pass, exemption, or proof repair.

## Evidence and method

Inputs are `pins.json`, `touched.json`, `seal-manifest.json`, and completed runs 002/004/005
under `briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2`. Diagnostic locations were inverted through the manifest's explicit
`source_to_probe_lines`; none falls in inserted imports, seal preambles or EOF verifiers.
Each saved run probe hash matches the manifest and run JSON, and the manifest's original
source hash matches `git show` of the frozen head. Run JSON reports unchanged probe bytes,
RC 1 and no fresh object. All observed errors are proof/type diagnostics at mapped source
sites; there is no seal-installation diagnostic among these 16 errors. Runtime summaries
record requested/verified counts of 690/690, 554/554 and 1036/1036 respectively.

For every failing declaration, the complete header/body block was extracted from both exact
Git revisions, ending before the following top-level docstring/command. The raw blocks,
including their separator whitespace, are byte-identical. They are also absent from the
module's `touched.json` name list. Imports/namespaces and existing declaration context do
not change in these three file diffs: changes are the supporting reader additions and the
coin-block move/repoint. The separate `decListFun_poly` range overclassification is noted below.

No Lean/cache, source edit, Git mutation or new seal run was performed. Read-only Git show/diff
was used. **No native base-seal replay is supplied by this review**: source identity is evidence
of untouchedness, not proof that the actual base was rerun under an identical seal set.

### TCSlib.Complexity.ClassP.BinaryArith.Loops

Completed run: **10 diagnostics, RC 1, no fresh object**. Source mapping and probe hash match the manifest.

| Probe line:column | Actual-base source line | Frozen source line | Failing declaration | Classification / observed blockage |
|---|---:|---:|---|---|
| `874:33` | 132 | 132 | `polyTimeComputable_forLoop` | **Untouched**; `isNilB` conversion at `polyTimeComputable_ite`. |
| `967:11` | 222 | 225 | `transduce_head_false` | **Untouched**; foreign `transduce` on the empty word. |
| `973:11` | 228 | 231 | `transduce_rest_true` | **Untouched**; foreign `transduce` on the empty word. |
| `993:45` | 248 | 251 | `uHead_nil` | **Untouched**; local `uHead` reduces to foreign `transduce`. |
| `996:45` | 251 | 254 | `uRest_nil` | **Untouched**; local `uRest` reduces to foreign `transduce`. |
| `1011:11` | 266 | 269 | `decodeNat_eq` | **Untouched**; foreign `BoolCircuit.decodeNat []`. |
| `1088:13` | 343 | 346 | `polyTimeComputable_hasFalse` | **Untouched**; foreign `transduce []` in local `heq`. |
| `1107:13` | 362 | 365 | `iterate_pairSndD_encWords` | **Untouched**; foreign `encWords []` / empty projection conversion. |
| `1116:11` | 371 | 374 | `getW_pairEncode` | **Untouched**; foreign `encWords []` / empty projection conversion. |
| `1268:33` | 523 | 526 | `polyTimeComputable_chunkW` | **Untouched**; `isNilB` conversion at `polyTimeComputable_ite`. |

Touched names recorded for this module: `hasFalse_eq`.

### TCSlib.Cryptography.Asymptotic.Adversary

Completed run: **3 diagnostics, RC 1, no fresh object**. Source mapping and probe hash match the manifest.

| Probe line:column | Actual-base source line | Frozen source line | Failing declaration | Classification / observed blockage |
|---|---:|---:|---|---|
| `812:9` | 192 | 208 | `invProbOpt_le_invProb` | **Untouched**; combined-seal type inference at `uprob_mono` (specific cause not isolated). |
| `860:58` | 240 | 256 | `_root_.Complexity.NUPPT.computes_iff_uprob` | **Untouched**; foreign `NUPPT.Computes` treated as a function/binder. |
| `862:12` | 242 | 258 | `_root_.Complexity.NUPPT.computes_iff_uprob` | **Untouched**; foreign `NUPPT.Computes` treated as a function/binder. |

Touched names recorded for this module: `coinBlock`, `coinBlock_eq`, `length_coinBlock`.

### TCSlib.Cryptography.Asymptotic.BlockEncryptor

Completed run: **3 diagnostics, RC 1, no fresh object**. Source mapping and probe hash match the manifest.

| Probe line:column | Actual-base source line | Frozen source line | Failing declaration | Classification / observed blockage |
|---|---:|---:|---|---|
| `1157:11` | 63 | 63 | `encodeList_eq_flatMap` | **Untouched**; foreign `PrivateKeyScheme.encodeList []`. |
| `1228:51` | 125 | 134 | `pairFstD_nil` | **Untouched**; foreign empty-word pair projection. |
| `1231:51` | 128 | 137 | `pairSndD_nil` | **Untouched**; foreign empty-word pair projection. |

Touched names recorded for this module: `blockState_eq`, `blockEncFun_eq`, `decListFun_poly`, `blockList_ofFn`.

`decListFun_poly` is listed as touched even though its full declaration block is byte-identical
between these pins. The neighboring removal/move of `coinBlock` causes an overinclusive
source-range attribution. It is not one of the failing declarations above; this mismatch
does not change their classification. `blockList_ofFn` really changes its explicit reader
items and remains touched; do not exempt that theorem or the whole module.

## Exact source/probe fingerprints

| Source file | Actual-base SHA-256 | Frozen source SHA-256 | Executed probe SHA-256 |
|---|---|---|---|
| `TCSlib/Complexity/ClassP/BinaryArith/Loops.lean` | `46e2d496b6437f806232a009ff0958acaa137adb286ae93626819d700f37449c` | `61cc82ebe34284b0171ea4c256e1f8a986c7465719d0991c083850bea9563045` | `f56021b13d9b6acc0dc202fa07e9e1b3e79bd915af674a2697c8a1af66ef8db1` |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | `4e9b47534922e6397b823173b00ab6ed2cb393b4e88ad4bc81a9065d4656cb0d` | `e5e324ef115ccd00b3910a7f5389afa28df7582c2d97f67b7619bcf3bcaff6c5` | `dfcf6bf8e05dc92894589226b7e88f129dee69474658378b40a4722aaa9116f4` |
| `TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean` | `75c51d072f6908383950f230f1983932cea0c763e8e9ed0f99490e6b679a2dc8` | `30d6f54a17c2fccff091d67af1e33498a68587698309be588eef2e477c66f112` | `0e5e2731933fd644d453f131d90ac7a52ca0965c7f11526a765ac6f713b51b10` |

## Declaration identity and cleanup linkage

Ranges below identify the raw blocks compared; the shared SHA-256 is equal at both revisions.
`cleanup-b-decls.tsv` links use the existing historical module/name key, not historical line
numbers (which precede later source shifts).

| Module/file | Declaration | Base range | Head range | Shared raw-block SHA-256 | Historical cleanup declaration row |
|---|---|---|---|---|---|
| `Loops` | `polyTimeComputable_forLoop` | 126–160 | 126–160 | `377bbaaf2fe6c1d506a02d910d638f322ce64ff62158a6edc7d2ebcbd91c140d` | **Absent** |
| `Loops` | `transduce_head_false` | 220–224 | 223–227 | `fed502a8565559238b5018f86cd3ec0c26a6e5c917089fc9f090cc265c8e6a58` | **Absent** |
| `Loops` | `transduce_rest_true` | 226–230 | 229–233 | `93f2a5a1d16f325e7919ef4128ac7de168cdc572f5bc6304ea3d527c9674b049` | **Absent** |
| `Loops` | `uHead_nil` | 248–249 | 251–252 | `89790ee301a6ecfc5c44319591ef87d9e3450a7f33632bff8e687fe9a290b59e` | **Absent** |
| `Loops` | `uRest_nil` | 251–252 | 254–255 | `3c0e9dcbc3d0d8297b9c8c03a7113c404b177ca7e84b2561e73c74b7fe18c375` | **Absent** |
| `Loops` | `decodeNat_eq` | 262–273 | 265–276 | `08e092f70305c4a684ae51d7950d29f8351d13fc157a349d68541a0a2199b058` | **Absent** |
| `Loops` | `polyTimeComputable_hasFalse` | 336–348 | 339–351 | `06144ccbe05d7a58d17e93f3e71044ca091354f1a5184e1cfbe60641f8ee77a9` | **Absent** |
| `Loops` | `iterate_pairSndD_encWords` | 355–364 | 358–367 | `cf1d4517f612a852474b51dc94bab9b1ad7acd91b26e0e0ee4c43ec4831a6ee1` | **Absent** |
| `Loops` | `getW_pairEncode` | 366–373 | 369–376 | `f6439b2199985275c874733499fbd4b98b6c38fe2843f500cec7537f31f6b5ec` | **Absent** |
| `Loops` | `polyTimeComputable_chunkW` | 519–551 | 522–554 | `d0d49cf46893354ede1f8c6fd78652404cb99ef0eed90f2170fc571f4648f78b` | **Absent** |
| `Adversary` | `invProbOpt_le_invProb` | 189–195 | 205–211 | `0b18221464f61fb4b1e834c095a5ef3a876d43fd7775db8e86f58326b73cbd1a` | 32 |
| `Adversary` | `_root_.Complexity.NUPPT.computes_iff_uprob` | 234–244 | 250–260 | `7950e8c57e5b092894f92271285baa5db94e9f04c483492bdca13d88a98c290a` | 31 |
| `BlockEncryptor` | `encodeList_eq_flatMap` | 60–65 | 60–65 | `0a070e8884151beb638dee5b020ae21cc190b33c96cfd88a2aa298997c2f3527` | 35 |
| `BlockEncryptor` | `pairFstD_nil` | 125–126 | 134–135 | `c621b66d9edd6832bec157ae976aac065bf4e902dc7e216c4246200a247bc8ba` | 39 |
| `BlockEncryptor` | `pairSndD_nil` | 128–129 | 137–138 | `18fcf1dfc89c6feb36803e93acb2f65c15a1b357c27dd37386b927898421e158` | 40 |

The two Adversary declarations already match `cleanup-b.tsv` rows 28–29 and
`cleanup-b-decls.tsv` rows 31–32. The three BlockEncryptor declarations match `cleanup-b.tsv`
rows 30–32 and `cleanup-b-decls.tsv` rows 35, 39–40. Keep these as refreshed observations linked
to clean-up part 2(b), preserving the new pin/map/hash evidence; they are not newly repaired.
The existing `encodeList_eq_flatMap` explicit `pairEncode` read also has an inherited unfold
inventory entry (`cleanup-b.tsv:270`); the nil-case diagnostic is a distinct observed site.

**Required inventory addition:** none of the ten Loops declarations appears under its
module/name in either historical cleanup TSV. Record all ten as newly observed **inherited,
unchanged main-library proof** inputs to the clean-up part 2(b) reconciliation, with their
head/base ranges and hashes above. Historical inventory absence does not make them new
Gate06 proof edits, and adding the inventory rows would not repair them. No canonical cleanup
ledger was edited here. Preserve the separate S2-before-clean-up-part-2 ordering.

## Limits and ambiguities

- The location/declaration and unchanged-source classification are unambiguous for these
  diagnostics. They do not imply that other touched declarations or anonymous commands pass.
- These are combined import-closure seals. The specific minimal blocked foreign constant
  was not isolated. In particular the `Fintype ?m` failure in `invProbOpt_le_invProb` should
  not be relabelled as a typeclass-library bug: the unchanged proof relies on conversion to
  `uprob_mono`, with foreign `invProb` in its target. Causal isolation would require a separate
  root-coordinated probe, not inference from this diagnostic alone.
- Builder fields such as `PREPARED_NOT_RUN` are construction-time manifest data. The later
  completed run logs/JSON supply runtime outcomes; their RC 1 outcomes remain failures.
- Earlier source inventories use older line numbers and narrower coverage. Match by exact
  module/declaration and retain the current location map; do not claim historical base seals
  were rerun or that the historical inventory covers the ten additional Loops declarations.

## Input-log fingerprints

| Relative to evidence-rule10-r2 | SHA-256 |
|---|---|
| `seal-manifest.json` | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |
| `touched.json` | `0fa835152e0028c397d195c6e6045ad43695ded0df68a154c4c18a285c7a77f3` |
| `pins.json` | `bd228171ea567980a833427db4a0aa92a155846d4a2fe75058d6db1c77827e5b` |
| `runs/G06Seal_002_TCSlib_Complexity_ClassP_BinaryArith_Loops.log` | `37e2160212152cdc35d0d21f4282418cb7cf0aed19c6abfb8bae69b75c8c6b06` |
| `runs/G06Seal_004_TCSlib_Cryptography_Asymptotic_Adversary.log` | `d105fa9a971784efec7520968ed408855a2781d852f196cd7a31813707d09e0b` |
| `runs/G06Seal_005_TCSlib_Cryptography_Asymptotic_BlockEncryptor.log` | `dfd973afdc382a092c5109f893e67fba30b6744ee42a01dafc31b6035a646720` |

**Not yet clear to merge — the failed observations remain; cleanup-inventory reconciliation and the broader Gate06 verification are pending.**
