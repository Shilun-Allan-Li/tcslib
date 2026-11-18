# Gate 46 · landing edit LE-g46b on #377: docs minors G46-01 and G46-02

**Verdict: PASS, pushed.** `land/gsw-6b-statements` (PR #377) is now
**`e8553378636dc896f36fc2a5ab23c8336dbfcecb`** (tree `129bbf9d2e3023f31f18f38becde4b3c56b85c99`), a fast-forward of
`7563734a8badba842223e0687c719b3b4692e9d2` (LE-g46, tree `c56db4c4`).

- **Ruling** (Seyoon, 2026-11-18; `LatticeCryptographyPlan.md`, "Gate 46 dispositions"): G46-01 and G46-02 are fixed
  now by a docs-only landing edit; G46-03 is known, and its merge condition is met by the efficiency remediation plan.
- **The edit:** 2 files, +11/−6, comments and docstrings only (`le-g46b.diff.txt`, SHA-256
  `a9fb61937cf5615a0d832dc63f907ab2064d00c2301a378a29f34c4778bd6c59`). No statement, proof or declaration changes.
  The comment-stripped texts of both files are byte-identical to `7563734a`.
- **Replay:** 6 modules rebuilt on a `cp -al` copy of the LE-g46 tree. All have rc 0 and 0 errors. The `sorry`
  warnings are exactly the 24 targets. State check 1456/1456 OK. Rebuilt oleans have link count 1. Snapshot #10 and
  the LE-g46 tree rehash 0/0/0.
- **Checks:** decls2 `7563734a` → head 0/0/0; `style_lint` 0 findings; `campaign_style_lint --check8b` FAIL/WARN
  unchanged, only the 2 INFO line counts change.
- **New replay tree:** `$SP/olean-replay-6b-stmt-g46b`, kept for snapshot adoption (output map, Mathlib excluded, 1487
  entries, SHA-256 **`e7bb03b4ba71a4d8f280b2fc62400b4d7cbda2b7a46c18ba9fe1cb6a488867d0`**).
- **The #377 description** records LE-g46b and Gate 46 CLEAR, and ends with the standard two attribution lines. The
  REST read-back equals the text sent (15,515 characters).

Run on 2026-11-18, about 08:54–09:05 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`; the job's directory is
`$SP/le-g46b-work`.
- **Evidence:** `le-g46b-evidence.zip`, beside this file, under `le-g46b/`. Its SHA-256 is
  `54512ea8b87423f088b4fa855e88ab6b9043496722464d283c51cf8ccb7e72bb`. Its inner `SHA256SUMS` lists 134 files and does
  not list itself (verified 134/134 by re-reading the archive). `PROVENANCE.txt` and `tools/TOOLS.txt` describe the
  layout.
- **Builds:** no `lake build` and no cache get. Modules ran through the recipe's `runner.py`
  (`scripts/lean_check_tree.sh`), one module per call, behind a slot gate (`pgrep -c -x lean`; wait while 3 or more
  run). This job ran one Lean process at a time; at most one other job's `lean` was seen running. No process was
  signalled.
- **Records:** nothing was committed to the records branch by this job. This file, `le-g46b.diff.txt`, the zip and
  `resolutions-r1.md` are left uncommitted for the maintainer.

## The edit

### G46-01 (`GSW/Circular.lean`, `WeakCircularSecure` docstring, `:101–106` at the head)
- **Before:** "It is stated per distinguisher because, quantified over **every** function `FheView P → ρ → Bool`, it
  would hold only for `ε` near `1`: an unbounded distinguisher recovers `s` from `pk` and decrypts the challenge."
- **After:** "It is stated per distinguisher because, for parameters under which decryption is correct, quantified over
  **every** function `FheView P → ρ → Bool` it would hold only for `ε` near `1`: an unbounded test can enumerate the
  key-generation seeds, take any seed whose public key is `pk`, and decrypt the challenge with that seed's secret.
  Recovering the original `s` uniquely is unnecessary. The definition also admits parameters that do not decrypt
  correctly, to which this argument does not apply."
- The finding's counterexample (`n=0`, `q=2`, `ℓ=N=1`, uniform Boolean noise, `m` samples, maximal advantage `2^(−m)`)
  is not quoted in the docstring. This job did not re-verify it; the docstring states only the qualification.

### G46-02 (`GSW/Asymptotic.lean`, `encodeCiphertext` docstring, `:77–81`, and the module References)
- **Before:** "… `encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C` [Pei16, Def 4.2.3, p024-b001, the
  binary representation convention]."
- **After:** "… `encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C`. Glue: a local encoding choice, which
  the cited sources do not fix. Each entry is written as the `ℓ`-bit binary numeral of its canonical residue in
  `{0, …, q − 1}`, the base-two representation of the canonical representative in [Pei16, §5.4.3, p052-b001]."
- **References:** the `[Pei16]` entry of the module docstring named "Definition 4.2.3", which was used only by this
  docstring. It now names "§5.4.3".
- **Anchor verified** in `blueprint/src/references/peikert2016-lattice-survey.md` (tag `Pei16` in `sources.json`):
  block `pdf-1a9802b66031-p052-b001` is "Section 5.4.3, gadget trapdoors: gadgets (printed p. 50)". It contains "let
  $\mathbf x$ correspond to the base-two representation of $u$'s canonical representative in $\{0,\dots,q-1\}$". The
  file header marks the DW-7 extension (§5.4.3) as "awaiting Codex source review". `p024-b001` is Definitions
  4.2.1–4.2.3 (LWE distribution, decision-LWE).
- **Code read for the docstring:** `Encoding.Modular.encodeMatrix` (`TCSlib/Cryptography/Encoding/Modular.lean`)
  concatenates `encodeVector` over rows, and `encodeVector` writes `Candidates.natToList width (v i).val` per
  coordinate. That is a `width`-bit numeral of the canonical residue `.val ∈ {0, …, q − 1}`, with no truncation by
  `Parameters.modulus_le`. The docstring does not state a bit order.
- **Line widths:** every line is at most 99 characters. Sizes: Circular 146 → 149 and Asymptotic 338 → 340 lines.

### Code identity (LE-g50d/e's method, `commentstrip50.py` unchanged)
- `7563734a` against the worktree before the commit, and against `e8553378` after it: **both RESULT EQUAL**, overall
  **RESULT OK** (`run/commentstrip/commentstrip-worktree.txt`, `commentstrip.txt`).

  | File | Stripped SHA-256 (both revisions) | Comment chars | Code chars |
  |---|---|---|---|
  | `Circular.lean` | `6b3c29c6e101a2f54ade4af0c77450d2c0e760ff5619745324b8a51258e34f33` | 5703 → 5984 | 2417 = 2417 |
  | `Asymptotic.lean` | `581b1a206f5971c33b575909cf5160d03e4332db870ff9a1db2e26e9bb91a059` | 11398 → 11575 | 8533 = 8533 |

- **Controls** (`controls-g46b.json`, `tools/mkctl46b.py`; each string occurs once in the edited file): M1 (a space
  after the first code `:=`), M2 (`def WeakCircularSecure` → `WeakCircularSecure'`; `def encodeCiphertext` →
  `encodeCiphertext'`) and M3 (the definition body line commented out) are caught (DIFFER) in both files. The negative
  control N1 changes one word inside the new text of each file ("uniquely" → "exactly"; "do not fix" → "do not
  specify") and stays EQUAL.

## Commit and push
- **Worktree:** the existing `$SP/g6b-p2/land` (sparse checkout), on `land/gsw-6b-statements` at `7563734a`
  (= `origin`), clean.
- **Commit:** `git add` of the 2 paths, then `git commit -S -F <msg> -- <2 paths>`. Subject "LE-g46b: Gate 46 docs
  minors G46-01, G46-02 (docs-only)". The message ends with exactly the two required trailers (raw object checked).
  Author and committer `Claude <noreply@anthropic.com>`. SSHSIG key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`,
  the same as `7563734a` (key identity only, `sigkey.py`; `git log %G?` cannot verify here because no allowed-signers
  file is configured).
- **Push** after the replay and checks passed: `ls-remote` gave `7563734a`; `git push origin
  HEAD:refs/heads/land/gsw-6b-statements` gave `7563734a8..e85533786` (no force); `ls-remote` then gave `e8553378`.
  GitHub's REST head for #377 is `e8553378`.
- **Merge trees** (`run/log/merge-tree.txt`): `git merge-tree --write-tree 38123ccb e8553378` = `129bbf9d` = the head's
  tree. The records tip at the job's end, `f968f6b2` ("Records: #376 merged"), contains #376's head `04ba2446`.
  `git merge-tree --write-tree f968f6b2 e8553378` = `1b637f9b`, whose Lean paths (`TCSlib`, `TCSlib.lean`, `audits`,
  `scripts`, the manifests) equal `129bbf9d` (0 paths differ).

## Replay (snapshot recipe, on the LE-g46 tree)
- **Pre-check:** snapshot #10 `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv` (`84d88738…`): 1478, 0/0/0,
  RESULT OK. The LE-g46 tree (`$SP/olean-replay-6b-stmt-g46`) against its map
  `olean-replay-6b-stmt-g46.map-7563734a.noMathlib.tsv` (`65ca0263…`): equal 1487, changed 0, added 0, removed 0. Its
  `state.json` (`ffd4d6bf…`) checks 1456/1456 OK at `7563734a`.
- **Copy:** `cp -al $SP/olean-replay-6b-stmt-g46 $SP/olean-replay-6b-stmt-g46b` (1488 files, 3346 Mathlib symlinks).
- **Export:** `git archive e8553378` of the recipe paths into `$SP/le-g46b-work/wtx`: 1608 files, 0/0/0 against the
  commit (`exportcheck.py`). The export was removed after the checks.
- **Plan:** `downorder.py e8553378 7563734a`: changed 2, **down 6**. `fullorder.py`: 1456, equal to LE-g46's. `stateplan
  plan`: **6 to build, 1450 reused**; the queue equals `down.txt` as a set.
- **Build** (08:56:36–08:56:49, max RSS 4.6 GB, `tools/run-build-g46b.sh`, the recipe's `runner.py` unmodified, one
  module per call): `Circular`, `Asymptotic`, `GSW`, `Homomorphic`, `AdvancedEncryption`, `TCSlib`. **6/6 rc 0**.
  `permod.py`: `error:` 0, `error(` 0, substring 0, 3 warnings, all `declaration uses 'sorry'` (Circular 1, Asymptotic
  2), no log/record mismatch. `warncmp6b` against the merged R2 + LE-g46 logs: 2 SAME-TEXT (the edited files; line
  numbers shift only) and 4 SAME (the facades and root, 0 warnings).
- **The 24 targets:** `admmap6b.py` over LE-g46's merged 14 module logs with these 6 on top: 24 targets, 24 admitted, 24
  matched, none extra, none twice, none missing: **RESULT EXACT**. The admitted (file, name, kind) set equals LE-g46's
  (0 diff lines ignoring line numbers).
- **Accept:** `stateplan update` took 6 modules; `check` at `e8553378`: **1456/1456 RESULT OK** (again at the end;
  `state.json` `5313731b…`). `linkcheck.py` against the LE-g46 tree: rebuilt 6 with link count 1; 1450 reused
  hard-linked to the LE-g46 tree's inodes; 0 `.ilean`; no stray symlinks; `Mathlib/` = 3346 symlinks + NthRootLemmas
  `c0a9cff0…`.
- **Output map:** `olean-replay-6b-stmt-g46b.map-e8553378.noMathlib.tsv`, 1487 entries, `e7bb03b4…`. Against the LE-g46
  tree: 1485 equal, **2 changed** (`Circular`, `Asymptotic`; oleans store docstrings), 0 added, 0 removed. The facades
  and the root rebuild byte-identical. Re-verified at the end: equal.
- **Rehashes:** snapshot #10 0/0/0 at the start, after the build and at the end; the LE-g46 tree equal 1487 / 0 / 0 / 0
  at the same three points, and its state check at `7563734a` 1456/1456 OK after the build.

## Checks
- **decls2** (`decls2.py` over the 12 series files): **`7563734a` → `e8553378`: 0 ADDED, 0 CHANGED, 0 REMOVED**, empty
  `.err`. Positive control: tip `38123ccb` → head gives 136 ADDED / 0 / 0, identical to LE-g46's ignoring line numbers
  (0 diff lines).
- **Lint** (from the export): `campaign_style_lint TCSlib/Cryptography --check8b`: 92 FAIL / 103 WARN over 540 files
  (exit 1, as at LE-g46); the FAIL/WARN line set equals LE-g46's (0 diff lines); only the 2 INFO line-count lines change
  (Asymptotic 338 → 340, Circular 146 → 149). `style_lint` on the 12 series files: "0 findings in 12 files",
  byte-identical to LE-g46's output; on the 2 edited files: 0 findings.
- **Not re-run** (docs only, comment-strip identical): axiom probes, Rule 10 seals and the admissions census. The
  `sorry`-warning map above confirms the 24 targets.

## PR description (#377)
- Read first with `pull_request_read` and over REST (12,541 characters, equal to LE-g46's read-back), then edited by
  exact-once replacements (`tools/prbody46b.py`), sent with `update_pull_request`, and read back over REST: the stored
  body equals the text sent (15,515 characters) and ends with exactly the two standard attribution lines.
- **Added:** the LE-g46b commit and tree in *Commits* (the LE-g46 entry no longer says "head"); an LE-g46b entry under
  *Landing edits and rulings*; an *LE-g46b recheck* section; a *Gate 46 round 1: CLEAR* line under *Review* (G46-01/02
  fixed by LE-g46b; G46-03 known, merge condition met by `briefs/efficiency-gaps/audit-r1.md` §5 and `rulings-r1.md`,
  EF-R1).
- **Changed:** the size line (+2207/−1 from the tip; at most 362 lines). The merge-order line now names
  `olean-replay-6b-stmt-g46b` and tree `129bbf9d`; `olean-replay-6b-stmt-g46` is superseded.

## Notes for the maintainer
- **#376 merged during this job** (09:00:21 UTC, merge `d6dee3d0`; records `f968f6b2` "Records: #376 merged"). GitHub
  retargeted #377 to `cryptography/pass-shelat-ch2-4` (REST: base `f968f6b2`, mergeable state `clean`). The body's
  opening sentence ("It is stacked on PR O2 … retargeted … once O2 merges") and the "O2 first" merge-order line are
  therefore now historical. This job did not edit them, because they were outside the LE-g46b scope and the records
  were moving concurrently.
- **Adoption:** on #377's merge, adopt `$SP/olean-replay-6b-stmt-g46b` (map `e7bb03b4…` after removing `Mathlib/`) if
  the merge's Lean paths equal `129bbf9d`. They do for a merge into `f968f6b2` (above). Do not delete
  `$SP/olean-replay-6b-stmt-g46` before adoption: the new tree's 1450 reused oleans are its hard links. It is no longer
  adoptable for #377.
- `CLAUDE.md` asks agents to use the LeanInfoView rather than build commands for proof state. This job ran the snapshot
  recipe's checker (no `lake build`), as the campaign's build rule requires.
- **Cleanup:** the export `$SP/le-g46b-work/wtx` and `$SP/le-g46b-work/tmp` were removed. Kept are
  `$SP/olean-replay-6b-stmt-g46b` and `$SP/le-g46b-work/{run,tools,PROVENANCE.txt}` (the run as zipped).
