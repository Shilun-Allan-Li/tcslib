# Current gate106 round3 baseline — complete, head pending

**Not yet clear to merge: #215** — current head metadata awaits root's successful MSG5 replay authorization; gate closure remains separate.

This baseline is actual campaign commit `3023dc1408c3d216fc07a7cbba9ae30135b861ed`, using the complete read-only `oleans-mac4` supplied by root. The comparison head is verified Git object `d0c4a292e781b55617e05b33fdd423bb059fd735`. The MSG5 snapshot has not been read or probed by this task. `context.json`, exact Git source archives, the five-file patch, and read-only Git command receipts retain the pins.

All three successful baseline stages passed with zero errors and warnings, sequentially through `leanelab.sh` (local budget3/machine5; one own Lean process):

| Stage | Seconds | Full raw UTF-8 bytes |
|---|---:|---:|
| Census, ALLAX/PUBLICAX and selected roots/descendants | 100.87 | 2,114,776 |
| Uncapped raw type representations | 21.09 | 113,922,909 |
| Structural CI and reflected attributes/simp rules | 11.69 | 5,383,361 |

The `.out.gz.b64` files preserve every output byte losslessly as UTF-8 compressed with gzip and encoded as ASCII base64. Receipts contain hashes of raw, compressed and base64 forms; `parse-staged.py complete Base` independently verifies those hashes and exact name coverage. There are no output caps. `map-Base.json` indexes the full retained raw types by name, hash and block index rather than duplicating their 113MB of expression text.

Current baseline census: **7,101 constants = 5,750 private + 1,351 nonprivate**, in the same original nine owners. ALLAX covers every constant and PUBLICAX exactly the nonprivate subset. The 16 selected repaired proof names already exist in the baseline; their **25 generated descendants** are retained too, all with standard axioms. Nine inherited `sorryAx` constants remain in Primitives (eight nonprivate and private `split_fuel`), individually listed in `primary-Base.json`/`map-Base.json`. No head AX-regression claim is made yet.

All 7,101 names have complete raw types, structural CI and the reflected attribute fields prescribed in the probe; 168 owned simp rules are retained with effective priorities/flags/proof expressions. ConstantInfo value/proof bodies are omitted, rather than truncated. Recursor reduction rules are retained as structural CI. The reflected attributes include simp/inverse/unfold, reducibility, protected, instance priority/kind, class, noncomputable, inline and match_pattern. Source attribute commands are separately archived; arbitrary third-party extension state is not claimed.

These totals are **not** the earlier MSG4 integrated result (7,063/5,714/1,349), which used pre-#230 dependencies. The new native MAC4 results are authoritative for this comparison.

The source freeze independently checks all nine owner files. Four are byte-identical. The five changed files preserve all public exports, headers, visibility and executable chunks: source totals remain **1,986 declarations = 349 public + 1,637 private**. There are39 changed common proof chunks (34 private, five public CounterLoop proofs), plus three removed/private replacement pairs. Tautology and SingleTape add Contract.Basic in the original SG1 scope; Hardness adds the newly authorized Prefix import. The exact final SAT and Hardness bytes match `round3-integrated`'s tested archives.

Earlier attempts are preserved: v1 failed with two unqualified Compiler inline-name identifiers; v2 and value-free v3 were stopped as incomplete (exit143) after267.83/523.90seconds. A one-second v3 sample showed active `reportMessages → MessageData.toString → Format.pretty` work. The unrendered message content was not observed, so this is not identified as a particular error or mathematical failure. No successful-data claim uses these attempts. The successful small stages use per-record `logInfo` and retain all requested fields without caps.

No source edits, screen, Git mutation, compiled output or snapshot/cache write occurred. The nine imported baseline artifacts were hashed before/after every attempt and remain unchanged. Matching head stage sources are ready and will only run after root explicitly authorizes the completed MSG5 snapshot.
