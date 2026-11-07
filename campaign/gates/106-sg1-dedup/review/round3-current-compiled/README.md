# Current gate106 round3 compiled comparison

**Not yet clear to merge: #215** — the current replay and compiled comparison pass; external gate closure remains separate. This report is pinned to the exact source below and does not extend to later source/import changes.

The comparison uses actual campaign base `3023dc1408c3d216fc07a7cbba9ae30135b861ed` / complete MAC4 and actual #215 head `d0c4a292e781b55617e05b33fdd423bb059fd735` / complete MSG5. Head probing began only after root explicitly reported MSG5 PASS. Root's archived receipt records329 modules, zero failures/errors/static mismatches, static total66, and329 actual `-j4` launches. This child read/pinned that completed receipt and its three raw artifacts; it did not execute the replay. See `HEAD-REPLAY-PASS.json` and `root-replay-evidence-pins.json`.

## Exact original nine-owner result

| Measurement | MAC4 base | MSG5 head |
|---|---:|---:|
| All compiled constants | 7,101 | 7,065 |
| Private | 5,750 | 5,714 |
| Nonprivate | 1,351 | 1,351 |
| Selected repaired proof roots | 16 | 16 |
| Generated descendants of those roots | 25 | 7 |
| Owned effective simp rules | 168 | 168 |
| Constants with nonstandard axioms | 9 | 9 |

All **1,351 nonprivate constants** retain their exact compiler names, owners, kinds, privacy/internal flags, full raw types, structural CI, reflected attributes, simp rules and axiom sets. There are no nonprivate additions/removals. The comparisons retain exact private IDs; no normalization or renaming is used.

Per-owner totals (nonprivate counts are unchanged): SAT737→723(15); Tautology428→425(6); Hardness1425→1411(7); Frag79→79(73); Catalog2178→2178(626); Contract.Basic276→276(274); CounterLoop289→287(204); Primitives1281→1281(136); SingleTape408→405(10). These are compiler counts, including generated constants, not authored-source export counts.

All names in each census have exact ALLAX coverage; PUBLICAX covers exactly each nonprivate subset. All selected16 roots and their respective25/7 descendants use only standard axioms. Across **all retained constants**, no axiom set grows. The sole change drops `Classical.choice` from private `clA5Pair_sizes`, leaving `[propext, Quot.sound]`. Every added constant has standard axioms. The identical nine inherited Primitives `sorryAx` constants remain: eight nonprivate rows and private `split_fuel`; their complete names/axes are retained. No whole-repository sorry-free claim is made.

These are current post-#230 results. The earlier MSG4 integrated count7,063/5,714/1,349 remains separate historical evidence and must not replace the MAC4→MSG5 comparison.

## Source and compiler deltas

The exact Git archives and source freeze cover all nine owners. Four source files are byte-identical; the other five preserve all public exports, headers, visibility and executable chunks. Authored-source totals remain1,986 =349 public +1,637 private. There are39 changed common proof chunks, plus three private lemma replacements. The final SAT and Hardness hashes remain respectively `682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba` and `a6edf9fe11e89d71a028143d1cedf9be896124bbcbc5a86d779e6c6278b5c597`, exact-equal to the earlier integrated native-source archives.

The full compiled delta is **six additions and42 removals, all private**:

| Classification | Added | Removed |
|---|---:|---:|
| Authored private lemmas | 3 | 3 |
| Generated auxiliaries | 3 | 39 |

The authored replacements are `tautDual_segment_add`→`tautDualSegment_iff_segment`, `counter_span_append`→`counterSpan_iff_segment`, and `dgSpan_add`→`dgSpan_iff_segment`. The other changes are generated proof/simp/matcher/equation auxiliaries. By compiler kind, additions are four theorems/two definitions; removals are39 theorems/three definitions. Six removed generated names carry `extract_run`'s matcher basename under SAT/Hardness ownership; they are not authored SAT/Hardness source declarations. No source API/home-change permission is inferred from such compiler artifacts.

Ten retained-name raw-type differences are **private generated proof auxiliaries only**; none maps to an authored source declaration. Exact complete before/after blocks and a diff are retained as `changed-private-types-{Base,Head}.txt` and `.patch`. All common structural CI and reflected attributes remain equal. `delta-classification.json` and `comparison-staged.json` retain every exact changed name and field, rather than treating compiler artifacts as source declaration changes.

## Native methods, complete raw evidence and limits

The same three successful stage sources ran separately on both snapshots, one managed Lean process at a time through `leanelab.sh`, local budget3/machine5. Every imported nine-owner artifact was hashed before/after every stage and remained unchanged. No compiled outputs were written.

| Stage | Base seconds | Head seconds | Base raw UTF-8 bytes | Head raw UTF-8 bytes |
|---|---:|---:|---:|---:|
| Census + all AX + root/desc AX | 100.87 | 93.39 | 2,114,776 | 2,102,333 |
| Full raw types | 21.09 | 20.64 | 113,922,909 | 114,083,881 |
| Structural CI + reflected attributes/rules | 11.69 | 12.32 | 5,383,361 | 5,362,345 |

All six successful stages have zero errors/warnings. Their full output is retained without caps as deterministic gzip encoded to ASCII base64; every raw/compressed/encoded hash is independently verified by the retained parser. `map-Base.json` and `map-Head.json` contain complete name maps and raw-type indexes, while `.out.gz.b64` retains every raw expression byte. Exact commands and source/snapshot/module hashes are in each request/run receipt. Run `python3 -I parse-staged.py complete Base`, `complete Head`, and `compare` to reproduce (the frozen phase artifacts should otherwise remain untouched).

ConstantInfo value/proof bodies are intentionally omitted in both successful contexts, not truncated. Structural CI includes recursor reduction rules. Reflected attribute coverage is explicit: simp/inverse/unfold and effective rule priorities/flags, reducibility, protected, instance priority/kind, class, noncomputable, inline and match_pattern. Source attribute commands are separately preserved. No claim about arbitrary third-party extension state or full proof-value equality is made.

Earlier unsuccessful/incomplete attempts, their observed partial outputs, cancellation receipts and the v3 one-second message-rendering sample remain retained. Their unrendered message content was not observed; no successful-data claim depends on them. The71 baseline payloads under `BASE-MANIFEST.json` were reverified unchanged before head probing and at final freeze. `BASE-README.md`'s head-pending status is a historical phase record.

No source edit, screen, Git mutation, shared snapshot/cache write, new opacity run or blanket legacy-source seal claim occurred here. Existing separately pinned seals/controls remain separate evidence. New host-debt rulings/accounting are recorded in separate addenda; they are not compiler census classifications or an external gate verdict.
