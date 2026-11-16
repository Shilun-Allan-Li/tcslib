# tools-agent log (sub-agent of fill bb1-machine)

Role: evidence tooling only (Python, `python3 -I`). I ran no Lean, no `lake`, no
`scripts/lean_check_tree.sh`, and made no commits or branch/ref changes. Inputs were read from the
lead's clone and my detached worktree `/home/user/fill/wt-sub` (HEAD `633dcf999`, clean), with
`git show <rev>:<path>`, `git ls-tree` and `git cat-file`. I wrote only under
`evidence/{headers/insertion,headers/frozen,clash,overlap,subagents/tools-agent}` and my scratch
directory. Date: 2026-11-16.

## A. Reader-insertion check: `headers/insertion/`

- `insertion_check.py <base-Defs> <head-Defs> <base-BonehBoyen> <head-BonehBoyen> <readers.txt>`.
  Checks C0 (source/base hashes, base anchors at 387/387/551), C1 (each block, a blank line plus
  the approved lines, verbatim after its unique anchor), C2 (each of the 7 readers declared once
  over both files, byte-identical, at its position; a deleted reader does not shift the expected
  positions of its successors), C3 (removing the blocks restores the base byte for byte), C4
  (final hashes and line counts 476/714), C5 (difflib vs base: ADDED 43/37, 0 REMOVED, 0 CHANGED,
  and the inserted hunks are the blocks), C6 (difflib vs base plus verbatim blocks: 0
  differences). It prints `READERS …` and `DIFF_VS_EXPECTED …` summary lines, then `RESULT`.
- `insertion_controls.py …` has 12 controls, M0 to M6 (two variants for several of them).
- `run_insertion.sh <repo> <outdir> [<readers.txt>]` runs both against base 7c0a55e0.
- Real run (base 7c0a55e0, head = worktree 633dcf99): **RESULT PASS, 24/24 checks**
  (`insertion-check.out`). Controls: **ALL_CONTROLS_OK True** (`insertion-controls.out`):
  - one character in a reader: FAIL, 1 CHANGED line, `textdiff=[that reader]`, `TEXT DIFFERS (1 line)`;
  - a reader deleted: FAIL, `missing=[that reader]` only, REMOVED 14 (Defs) / 12 (BonehBoyen);
  - an extra line in Defs or BonehBoyen: FAIL, readers intact, ADDED 1;
  - `ofFn_bb1SimCt` moved after the simps block: FAIL, `moved=[ofFn_bb1SimCt]`;
  - the Defs readers zero and one swapped: FAIL, both moved;
  - a docstring edit (BonehBoyen and Defs): FAIL, 1 CHANGED line;
  - a duplicated reader: FAIL, `duplicate=[…]`.
- The mutated files are in `controls/<control>/{Defs,BonehBoyen}.lean` plus `check.out`. The base
  copies are in `base/`.

## B. Frozen-header check: `headers/frozen/`

- `frozen_check_bb1m.py` and `frozen_controls_bb1m.py` are adapted from
  `outbox/…/checkpoint/tools/` (the originals are untouched). Each change is listed in the files'
  `ADAPTED (tools-agent, fill bb1-machine)` header:
  - `Oracles` is permitted as a helper;
  - the import block is pinned to the issue base's, with the Oracles import allowed only directly
    after `.Handler`;
  - `## Contents` is required and pinned to the issue base's, plus `ORACLES_BULLET` after the
    Reduction bullet if and only if the Oracles import is present;
  - T4's sketch and body logic is unchanged;
  - lines are at most 100 characters.
- **Where the lead adjusts the wording:** the constants `ORACLES_BULLET`, `ORACLES_IMPORT` and
  `ORACLES_AFTER_IMPORT` near the top of `frozen_check_bb1m.py`. Alternatively, pass
  `--bullet-file <path>` (or `BULLET_FILE=<path>` to `run_frozen.sh`), which reaches the check
  and every control run.
- Controls:
  - C1–C8 are kept. C3's anchor was lengthened (same edit) so it stays unique if the new sketch
    reuses "negligible `σ` with".
  - New C9a/C9b: the sketch spills into the prose (a deleted blank line; `distributions.` ->
    `distribution.`).
  - New C10a/C10b: a reworded bullet; an extra bullet after Reduction.
  - New C10b2/C10c/C10d (only on a head with the Oracles import): a second new bullet; the
    bullet dropped; the import dropped.
  - New C11a/C11b: the Oracles import after `.Reduction`; the import last.
  - A control whose anchor is not unique reports `ANCHOR-NOT-UNIQUE` and fails the run.
- `run_frozen.sh <head-file> <outdir> [<repo>]` runs the check and the controls against #331
  `9e7a9648` (`<repo>` defaults to `/home/user/fill/tcslib`; I used `/home/user/fill/wt-sub`).
- MOCK (clearly labelled; `mock/make_mock.py` builds it from the 7c0a55e0 file):
  `mock/BonehBoyenMachine.MOCK.lean` → `PASS: 5 helper import(s) added (incl. Oracles, after
  .Handler); Contents section = issue base + Oracles bullet; …; T4 sketch replaced; T4 body
  replaced`. Controls: 17 FAIL(expected), **ALL_CONTROLS_OK True** (`mock/out/`).
- Issue base 7c0a55e0 file: `PASS: 4 helper import(s) added; Contents section = issue base; T4
  header and statement prose byte-identical; T4 sketch unchanged; T4 body unchanged (sorry)`.
  Controls: 12 FAIL(expected), 5 SKIP (Oracles-only), ALL_CONTROLS_OK True (`issue-base/out/`).
  This also shows that the embedded `ISSUE_CONTENTS` equals the issue base's section byte for
  byte.

## C. Name-clash scan: `clash/`

- `clash_scan.py <repo> <base-rev> <head-rev> <out>`:
  - New declarations are the added header lines in `TCSlib/**/*.lean` (git diff `-U0`; all of a
    new file).
  - Full names come from `namespace`/`section`/`mutual`/`end` (dotted and partial `end`), dotted
    declaration names and `_root_`; comments and strings are blanked first.
  - The base index covers every `.lean` file of `TCSlib/` and `audits/` at base-rev, via
    `git ls-tree` and `git cat-file --batch`.
  - Statuses: CLASH, OK, DUP-NEW, MODIFIED (a changed header of an existing declaration); INFO
    lists same short names elsewhere.
  - Not covered: auto-generated names (structure fields, constructors, `simps`).
- Validation:
  - 7c0a55e0..633dcf99: **RESULT: 7 new names, 0 clashes**, with full names
    `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.oracleImpl_{zero,one,two}_onSpec`
    and `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.{ofFn_bb1Scheme_encPP,
    ofFn_bb1Scheme_encSK, bb1Scheme_msgSpace_iff, ofFn_bb1SimCt}`.
  - Sanity run 9e7a9648..7c0a55e0: **239 new names = 166 public + 73 private, 0 clashes**. This
    matches the brief's 166 public; 20 rows carry INFO (e.g. `rU`, `rZ`, `handler` in other
    namespaces).
- Controls (`clash_controls.py`, output `clash-controls.out`): **ALL_CONTROLS_OK True**.
  - K1, a synthetic new file: 11 declarations with the expected CLASH/OK, covering private,
    dotted, `_root_`, sections, `mutual`, partial `end`, anonymous instances, comments and
    strings.
  - K2, a synthetic added line duplicating `IBEScheme.oracleImpl_one` in Defs.lean: CLASH.
  - K3, a changed header line of `oracleImpl_two`: MODIFIED.
- **Pre-scan of the planned names** (`planned-prescan.tsv`, namespace `…IdentityBased.BB1Machine`):
  **7 new names, 0 clashes, no same-short-name declarations.** `overlap/alt_ns.py` also checks the
  outer and `IBEScheme` namespaces, the probe's `abs_inner_le` and unprimed `sidSpec_rng_one/two`:
  all free.
- On the final head: `python3 -I clash/clash_scan.py /home/user/fill/tcslib 7c0a55e0 HEAD <outdir>`.
  Expect 14 new names (7 readers and 7 glue), 0 clashes. Optionally also run 9e7a9648..HEAD and
  expect 166 + 73 + 14.

## D. Overlap searches: `overlap/`

- `search.log` holds every command, verbatim, with its output and exit status (TCSlib at
  633dcf99, Mathlib read-only, Lean core v4.25.0 `Init`).
- `overlap.md` gives the nearest relatives with `path:line`, the relation and notes for all 14
  declarations.
- Findings the lead should look at (all unverified in Lean):
  - `cast_eq_padFin`: its nearest public relative is `ofFn_cast` (`Asymptotic/Adversary.lean:225`).
    The same fact was proved inline as `have hm'` in `OracleFromPRF/Transfer.lean:73` and
    `EncryptThenTag/Transfer.lean:88`.
  - `ofFn_padFin_ofFn` specializes the public `ofFn_padFin_of_length`
    (`Asymptotic/Adversary.lean:216`). The private `ofFn_padFin_msg`
    (`EncryptThenTag/CPAHandler.lean:645`) is an instance with the same proof. It could be
    inlined.
  - `ofFn_decAnswer_some` is `decAnswer_some` plus Mathlib `List.ofFn_cons`
    (`Data/List/OfFn.lean:138`). Inline copies of the step are in the private
    `ofFn_prf_decAnswer` and `ofFn_cca_decAnswer`.
  - `sidSpec_rng_one'`/`_two'` are the exact IBE analogues of
    `FixedLengthScheme.indSpec_decRng`/`indSpec_challengeRng` (`PrivateKey/OracleSecurity.lean:285`,
    `:295`). No `IBEScheme` lemma exists, so they are promotion-request candidates for
    `Defs.lean`.
  - `expect_bb1SimImpl` is the per-call hypothesis of `ProbComp.expect_simulate_congr`
    (`Games/Hopping.lean:384`). The `expect_indImpl_fImpl`/`_ettImpl` analogues exist for other
    schemes.
  - The probe's inline `hq` restates `BB1Machine.qLen_eval` pointwise. The left side of the
    probe's inline `hzero` is the public `padFin_ofFn_zeroBits` (`Games/BitCodec.lean:139`).
  - The probe uses neither private `expect_sample_eq_uprob` nor `ite_ofFn_one` (checked by grep).

## Concerns / notes for the lead

1. No name clash, now or for the planned names.
2. The `simps` lemmas `bb1Scheme_encPP`/`_encSK`/`_MsgSpace`/`_encCT` are generated, so their
   exact statements could not be shown without Lean. The relation claimed for them in
   `overlap.md` is marked unverified.
3. The insertion controls write `.lean` files under `evidence/headers/insertion/controls/`, and
   the frozen mock/controls write `.lean` files under `evidence/headers/frozen/`. They are outside
   the repository; make sure no lint or sweep globs `evidence/`.
4. `run_frozen.sh` reads the #331 base with `git -C <repo> show 9e7a9648…`. It needs a repository
   containing that commit (both clones do).

## Files created (sha256)

See `files.sha256` in this directory: 97 files under `headers/insertion`, `headers/frozen`,
`clash` and `overlap`, generated with
`cd evidence && find headers/insertion headers/frozen clash overlap -type f | sort | xargs sha256sum`.
The main ones:

```
ffa6c14c77cd053ce1db16428ed61094e4caf25a14a2a3ab8e4709a724741b53  headers/insertion/insertion_check.py
9c401946d10380de4b06204237fb3477d7daa7399933654c99024067d8c01225  headers/insertion/insertion_controls.py
14b9e220cb44df2c3f4f5dc25ee0d894d535455a57877c1a4522fd40f0487350  headers/insertion/run_insertion.sh
fe651d2e178229433fc2f4332aeae0d2b468de544c463198454098f4a139bfa1  headers/insertion/insertion-check.out
9c12887b28e1e81681c5aa60bb4250483b73843d9fe3286cca3ff2e867848df0  headers/insertion/insertion-controls.out
1bf18fdfe7ba71460744f5338002e992290bd2c44b6300d2091f03bcd8564c81  headers/frozen/frozen_check_bb1m.py
84e73efc1359280661a1a8cfdda376959b1a52d16a2403e778b762a5ebcfd257  headers/frozen/frozen_controls_bb1m.py
e289e3c86c63ffe1931030ac57553f54e32f3de791050603ae06a9a3e8505447  headers/frozen/run_frozen.sh
b4fde47238c5c7d6264a00b12202f86cd82533791cb35507c9217e671a98d252  headers/frozen/mock/make_mock.py
6c710a39770927ab4d1cbf2ac0a911b6ee2c14b59ef4702e47f547f65da0be31  headers/frozen/mock/BonehBoyenMachine.MOCK.lean
5e4cd3f45769c2ed03e0ad1a6e1ec8d4f6f49008f63f74c0c1115807fa0f77de  clash/clash_scan.py
a1dccaa42012e803f471e8bc7978d23ea067a9bd635bb170d681372f412c5e73  clash/clash_controls.py
7d41e5b0be389a9fa81c90706ee2f74d19f14ba05f96d1c272bf57fa43c06b36  clash/clash-controls.out
11c7fc841066fd96c5c47aa8c0f4c01bbb52f4731f4fadac40ff5159f9ec3ffe  clash/planned-prescan.tsv
09e7db377097a498f17cfabdaf0ffa8afa2b6e78f2aea5089349477c1f77e6bb  overlap/alt_ns.py
2db9ad3ff7c04e765d5cef8dba4882f485abe35672dc7876cf0611189bd7967a  overlap/overlap.md
c46928a4a535e7f6129b954af03b080c2b6c18327abe250224ba490229f13777  overlap/search.log
```
