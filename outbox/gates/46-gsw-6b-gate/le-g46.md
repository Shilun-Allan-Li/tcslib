# Gate 46 · landing edit LE-g46 on #377: S1 fixed (DL-61) and the [Gen09] citations

**Verdict: PASS, pushed.** `land/gsw-6b-statements` (PR #377) is now
**`7563734a8badba842223e0687c719b3b4692e9d2`** (tree `c56db4c403ccab179a994143c5f989d4f3718910`), a fast-forward of
`680be9fa45a9cf5deeb7a59820e8e86aaaa4f068` (tree `956fc086`). The base is unchanged: `land/gsw-6b-o2` at `04ba2446` (#376).

- **Rulings** (Seyoon, 2026-11-18; `LatticeCryptographyPlan.md`, last row): S1 is fixed now, proof-only (DL-61, question
  Q-G46-S1, option A); the stale "[Gen09] not ingested" docstrings are fixed in the same commit, docs only.
- **The edit:** 4 files, +63/−27 (`le-g46.diff.txt`, SHA-256
  `13267e45ba16bc23d8a47e2c2c2176bc7f4a0fdaa33f7733707c98af0d6c24f4`).
  - **S1, proof only** (`GSW/Asymptotic.lean`): `encodeFheView_length` and `encodeLeveledView_length` apply the public
    `TCSlib.Cryptography.length_flatten_map_const` (`Foundations/BitLists.lean:175`) after Mathlib's `List.ofFn_eq_map`
    and core's `List.length_finRange`. Their statements and docstrings are byte-identical.
  - **[Gen09], docs only:** `GSW/Leveled.lean` (module docstring and `levelKey`), `LeveledSecurity.lean`,
    `PolyRatio.lean` and `Asymptotic.lean`.
- **Replay:** 8 modules rebuilt on a `cp -al` copy of R2, all rc 0 with 0 errors; the `sorry` warnings are exactly the
  same 24 targets. State check 1456/1456 OK. Rebuilt oleans have link count 1. Snapshot #10 and R2 rehash 0/0/0.
- **Checks:** admissions 216, equal per module to R2. Axioms of the two lemmas unchanged, only their closure sizes
  change. Canonical coe-A on the 4 edited owners: 0 errors, request sets equal to R2's. decls2 `680be9fa` → head
  0/0/0. Lint unchanged.
- **New replay tree:** `$SP/olean-replay-6b-stmt-g46`, kept for snapshot adoption (output map, Mathlib excluded, 1487
  entries, SHA-256 **`65ca02637e05f1f781c13fcbabcc69f9fcd59d511cfca63d11820d6a7fc07f18`**).
- **The #377 description** records LE-g46 and ends with the standard two attribution lines; the REST read-back equals
  the text sent.

Run on 2026-11-18, about 07:15–07:45 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`; the job's directory is
`$SP/le-g46-work`.
- **Evidence:** `le-g46-evidence.zip`, beside this file, under `le-g46/`. Its SHA-256 is
  `313c8f4d8a841b3c53849cfd5ec238caf6f3ac5c80c4ecf048f91b753c886ae1`. Its inner `SHA256SUMS` lists 224 files and does not
  list itself; `PROVENANCE.txt` and `tools/TOOLS.txt` describe the layout.
- **Builds:** no `lake build` and no cache get. Modules ran through the recipe's `runner.py`
  (`scripts/lean_check_tree.sh`), probes and seals through `runner_full.py` (`lean -DmaxErrors=0`, no `-o`). Every
  call went through a slot gate (`pgrep -c -x lean`, wait while 3 or more run). This job ran one Lean process at a
  time; at most one other job's `lean` was running. No process was signalled.
- **Records:** nothing was committed by this job. This file, `le-g46.diff.txt`, the zip, the DL-61 update and the
  Gate 46 re-staging are left for the maintainer.

## The edit

### S1 (proof only)
- **Before** (`680be9fa`, `Asymptotic.lean:128–130`, `:157–160`): `List.length_flatten`, `← List.ofFn_comp'`,
  `List.ofFn_const` and `List.sum_replicate_nat` for each `(List.ofFn fun i => encodeCiphertext P (…)).flatten` block.
- **After:**
  - `encodeFheView_length`: `rw [encodeFheView_eq, List.length_append, List.length_append,
    LWE.encodeChallenge_length, encodeCiphertext_length, List.ofFn_eq_map, length_flatten_map_const (List.finRange
    P.columns) _ _ fun i => encodeCiphertext_length P (v.2.1 i), List.length_finRange]`.
  - `encodeLeveledView_length`: a local `hcts` (the length of `(List.ofFn fun j => encodeCiphertext P (f j)).flatten`
    for any `f : Fin n → Ciphertext P`, by the same three lemmas), then one `rw` applying `length_flatten_map_const`
    to the public-key blocks (with `LWE.encodeChallenge_length`) and to the level-key blocks (with `hcts`).
- **Code identity:** the comment-stripped diff of `Asymptotic.lean` (`stripdiff.py`, `run/commentstrip/
  stripdiff-Asymptotic.txt`) is exactly these two proofs. The raw diff touches only the module docstring and the two
  proofs; the `_length` statements and docstrings are byte-identical.
- **Direct constants** (`AxiomsG46` probe, `run/axioms/axdirect.txt`): both proofs drop `List.length_flatten`,
  `List.ofFn_comp'`, `List.ofFn_const`, `List.sum_replicate_nat` (and `encodeLeveledView_length._simp_1_1`), and now
  use `TCSlib.Cryptography.length_flatten_map_const`, `List.ofFn_eq_map` and `List.length_finRange`.

### [Gen09] citations (docs only)
- **The ingest:** `blueprint/src/references/gentry-2009-fhe-thesis.md` (DW-8, records `bdcadd85`, 2026-11-16); tag
  `Gen09` in `blueprint/src/references/sources.json`. Anchors use the physical PDF page (printed page = p − 10). No Lean
  file used the tag before this edit.
- **Passages verified in the ingest and cited:**

  | Anchor | Passage (printed page) | Cited for |
  |---|---|---|
  | `p056-b002` | §4.1, construction of `E^(d)`: "we encrypt the secret keys in reverse order" (p. 46) | the index reversal |
  | `p056-b003` | §4.1, `KeyGen` of `E^(d)`: `(sk_i, pk_i)` for `i ∈ [0, d]`, `sk̄_ij ← Encrypt(pk_{i−1}, sk_ij)` for `i ∈ [1, d]` (pp. 46–47) | the key chain |
  | `p057-b001` | §4.1, `Evaluate`: "each wire in `C_δ` connects gates at consecutive levels; if not, add trivial gates" (p. 47) | layered circuits |
  | `p059-b001` | §4.2, Thm 4.2.1, correctness (statement only ingested) (p. 49) | PolyRatio's leveled correctness |
  | `p060-b001`, `p061-b001` | §4.2, Thm 4.2.3 with its proof: Games `0..d+1`, the reduction planting `pk_k` (pp. 50–51) | the hybrid order |

- **The correspondence stated:** Gentry's level `i` is level `L − i` here. His `Enc(pk_{i−1}, sk_i)` is
  `levelKey (L − i)` (`s_{L−i}` under `pk_{L−i+1}`); his Game `k` (keys `i ≤ k` replaced) is `H_{L−k}`; his step `k → k+1`
  plants `pk_k` (here `pk_{e+1}`, `e = L − k − 1`), whose secret occurs only in encryptions already replaced. So the
  top-down order of L4/L5 is Gentry's order under the renumbering.
- **The remaining deviations, stated in `LeveledSecurity`:** a replaced level key encrypts `0`, not the bits of an
  unrelated fresh key; each level step is a hybrid over the `N` positions, not one challenge of Gentry's `ℓ`-fold
  scheme; each step reduces to DLWE (phase 5), not to the base scheme's semantic security; and the middle step between
  the two chains is phase 5's challenge step, not Gentry's Game `d + 1`.
- **Per file:**
  - `Leveled.lean`: the module's *Sources and reconstruction* paragraph (chain, reverse order, layering, the hybrid
    pointer; "Besides [Gen09] for the chain, the statements … cite …"); `levelKey`'s docstring (the chain with the
    renumbering); `## References` gains [Gen09].
  - `LeveledSecurity.lean`: the paragraph (chain, Thm 4.2.3's game order and its renumbering, the deviations);
    References.
  - `PolyRatio.lean`: the paragraph (chain, Thm 4.2.1, a pointer to Thm 4.2.3); References.
  - `Asymptotic.lean`: the paragraph (chain, Thm 4.2.3, whose loss `ℓ(d + 1)` is linear in the depth, with `L(κ)` a
    polynomial); References.
- **Kept:** the declaration-level "Reconstruction disclosed (module docstring)" pointers (L4, L5, A3, G17-leveled,
  `levelReduction` and others). They point at the updated module paragraphs. No target docstring gains a [Gen09] tag;
  that is a possible follow-up if Gate 46 asks for it (policy §2, declaration level).
- **Line widths:** every new line is at most 99 characters. Sizes: Leveled 284 → 291, LeveledSecurity 351 → 362,
  PolyRatio 175 → 179, Asymptotic 324 → 338 lines (all under 400).

### Code identity of the docs-only files (LE-g50d/e's method)
- `commentstrip50.py` (unchanged from phase 2) on `680be9fa` against the worktree before the commit and against
  `7563734a` after it: **Leveled, LeveledSecurity and PolyRatio RESULT EQUAL**, overall **RESULT OK**
  (`run/commentstrip/`).

  | File | Stripped SHA-256 (both revisions) | Comment chars | Code chars |
  |---|---|---|---|
  | `Leveled.lean` | `5f1fc80c250fac03de88f41e85eaba466107b5bf66e8fb33ed6db72d751a5929` | 11390 → 12110 | 6023 = 6023 |
  | `LeveledSecurity.lean` | `a7afe34246a05e3b42d10be0f314c8269b3273bd7dde0637eba87b0ee22908d8` | 12238 → 13205 | 9197 = 9197 |
  | `PolyRatio.lean` | `6887b3ddb681b5fd697ad355f125dd2d7737c155d3ed24f3fdc2028d10d7a058` | 6157 → 6495 | 3657 = 3657 |

- **Controls** (`controls-g46.json`, `tools/mkctl46.py`): M1 (a space after the first code `:=`), M2 (one code token)
  and M3 (one code line commented out) are caught (DIFFER) in all three files; M2/M3 are phase 2's. The negative control
  N1 changes one word inside the new [Gen09] text of each file and stays EQUAL.
- `Asymptotic.lean` is not docs-only; its stripped diff is the two proofs (above).

## Commit and push
- **Worktree:** the existing `$SP/g6b-p2/land`, on `land/gsw-6b-statements` at `680be9fa` (= `origin`), clean.
- **Commit:** `git commit -S -F <msg> -- <4 paths>` after `git add` of the same 4 paths. Subject "GSW 6b landing edit
  LE-g46 (Gate 46 sweep S1; [Gen09] citations)"; the message ends with exactly the two required trailers (raw object
  checked). Author and committer `Claude <noreply@anthropic.com>`. SSHSIG key
  `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the same as `680be9fa` and the records tip (key identity only,
  `sigkey.py`).
- **Push** after the replay passed: `ls-remote` gave `680be9fa`; `git push origin HEAD:land/gsw-6b-statements` gave
  `680be9fa4..7563734a8` (no force); `ls-remote` then gave `7563734a`. GitHub's REST head for #377 is `7563734a`.
- `git merge-tree --write-tree 38123ccb 7563734a` = `c56db4c4` = the head's tree. The records tip at the job
  (`e48a576c`, and `9ae6b909` at the end) is Lean-equal to `38123ccb` (0 paths under `TCSlib`, `TCSlib.lean`,
  `audits`, `scripts`, the manifests).

## Replay (snapshot recipe, on R2)
- **Pre-check:** snapshot #10 `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv` (`84d88738…`): 1478, 0/0/0,
  RESULT OK. R2 (`$SP/olean-replay-6b-stmt`) against its map `olean-replay-6b-stmt.map-680be9fa.noMathlib.tsv`
  (`52ed7825…`): equal 1487, changed 0, added 0, removed 0. R2's `state.json` (`d76b49a7…`) checks 1456/1456 OK at
  `680be9fa` on R2 and on the copy.
- **Copy:** `cp -al $SP/olean-replay-6b-stmt $SP/olean-replay-6b-stmt-g46` (1488 files, 3346 Mathlib symlinks).
- **Export:** `git archive 7563734a` of the recipe paths into `$SP/le-g46-work/wtx`: 1608 files, 0/0/0 against the
  commit (`exportcheck.py`).
- **Plan:** `downorder.py 7563734a 680be9fa`: changed 4, **down 8**. `fullorder.py`: 1456, equal to R2's. `stateplan
  plan`: **8 to build, 1448 reused**; the queue equals `down.txt`.
- **Build** (07:24:22–07:24:37, max RSS 4.6 GB, `tools/run-build-g46.sh`, the recipe's `runner.py` unmodified, one
  module per call): `Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic`, `GSW`, `Homomorphic`,
  `AdvancedEncryption`, `TCSlib`. **8/8 rc 0**; `permod.py`: `error:` 0, `error(` 0, substring 0, 9 warnings, all
  `declaration uses 'sorry'` (Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2), no log/record mismatch.
  `warncmp` against R2's logs: 4 SAME (the facades and root, 0 warnings) and 4 SAME-TEXT (the edited files; line
  numbers shift only).
- **The 24 targets:** `admmap6b.py` over R2's 14 module logs with these 8 on top: 24 targets, 24 admitted, 24 matched,
  none extra, none twice, none missing: **RESULT EXACT**. The admitted (file, name) set equals R2's (0 diff lines
  ignoring line numbers).
- **Accept:** `stateplan update` took 8 modules; `check` at `7563734a`: **1456/1456 RESULT OK** (again at the end;
  `state.json` `ffd4d6bf…`). `linkcheck.py` against R2: rebuilt 8 with link count 1; 1448 reused hard-linked to R2's
  inodes; 0 `.ilean`; no stray symlinks; `Mathlib/` = 3346 symlinks + NthRootLemmas `c0a9cff0…`.
- **Output map:** `olean-replay-6b-stmt-g46.map-7563734a.noMathlib.tsv`, 1487 entries, `65ca0263…`. Against R2: 1483
  equal, **4 changed** (`Asymptotic`, `Leveled`, `LeveledSecurity`, `PolyRatio`; the docs files change because oleans
  store docstrings), 0 added, 0 removed. The facades and the root rebuild byte-identical. Re-verified at the end: equal.
- **Rehashes:** snapshot #10 0/0/0 at the start, after the build and at the end; R2 equal 1487 / 0 / 0 / 0 at the same
  three points, and its state check at `680be9fa` 1456/1456 OK at the end.

## Checks
- **Admissions:** `sorryscan.py` over the full order at `7563734a`: **216 in 52 modules**, byte-equal to R2's
  `lib-r2.txt` (0 diff lines).
- **decls2** (`decls2.py` over the 12 series files): **`680be9fa` → `7563734a`: 0 ADDED, 0 CHANGED, 0 REMOVED**, empty
  `.err`. Tip `38123ccb` → head: 136 ADDED / 0 / 0, identical to phase 2's ignoring line numbers.
- **Axioms:**
  - `AxiomsG46.lean` (new; `#print axioms` plus closure size and direct constants), run unchanged on R2 and on the new
    tree: `encodeFheView_length`, `encodeLeveledView_length` and `length_flatten_map_const` all use
    **`[propext, Quot.sound]`, unchanged**. Closure sizes: `encodeFheView_length` 913 → 1009,
    `encodeLeveledView_length` 914 → 1009, `length_flatten_map_const` 297 = 297.
  - **Consumers:** no declaration in `TCSlib/` or `audits/` at the head uses either lemma (`git grep`), so there are no
    consumers to re-probe.
  - The delivery's census probe (`AxiomsStmt.lean`, unchanged) on the new tree: 174 constants (153 DECL, 21 AUX); no
    non-standard axiom besides `sorryAx`; `sorryAx` in exactly the 24 targets, each tracing only itself; the named
    checks as in phase 2. Against R2's log: 198 lines equal, 0 only here, 1 only in R2: the auxiliary
    `encodeLeveledView_length._simp_1_1` (`[Quot.sound, propext]`), generated by the old `simp only` and gone with it.
- **Rule 10, canonical coe-A** (`tools/rule10_g46.sh`: phase 2's harness, collector `NmCollect` and `mkseals_coe.py`
  unchanged, `touched.json` against `38123ccb`, `SEAL_CHUNK=1000`; owners the 4 edited modules):

  | Owner | Requests (LE-g46 / R2) | Errors | Request set | Install / EOF |
  |---|---|---|---|---|
  | `GSW/Leveled` | 479 / 479 | 0 | equal | 1 / 1 |
  | `GSW/LeveledSecurity` | 1561 / 1561 | 0 | equal | 1 / 1 |
  | `GSW/PolyRatio` | 1394 / 1394 | 0 | equal | 1 / 1 |
  | `GSW/Asymptotic` | 1653 / 1653 | 0 | equal | 1 / 1 |

  Term names, term exclusions and closure modules are equal. The sealsum rows are equal. The only record difference:
  `Asymptotic` stores 25 constants instead of 26 (the dropped `_simp_1_1`), so `sealcmp46.py` prints FAIL on that field
  alone (`run/rule10/sealcmp.txt`).
- **Lint** (from the export): `campaign_style_lint TCSlib/Cryptography --check8b`: 92 FAIL / 103 WARN over 540 files;
  the FAIL/WARN line set equals R2's (0 diff lines); only the 4 INFO line-count lines change. `style_lint` on the 12
  series files: "0 findings in 12 files", byte-identical to R2's output; on the 4 edited files: 0 findings.

## PR description (#377)
- Read first with `pull_request_read` (its text matched the gate copy `pr377-description.md`, which the edits were
  applied to by exact-once replacements, `tools/prbody46.py`), then updated with
  `update_pull_request`, and read back over REST: the stored body equals the text sent (12,541 characters).
- **Added:** the LE-g46 commit and tree in *Commits*; an LE-g46 entry under *Landing edits and rulings*; an *LE-g46
  recheck* section; the merge-order line now names `olean-replay-6b-stmt-g46` and tree `c56db4c4`.
- **Changed:** size line (+2202/−1 from the tip; at most 362 lines); the P6-Q19 B disclosure line; Gate 46's line
  notes S1 fixed by LE-g46.
- **Fixed slip** (Gate 46 staging): the footer "_Generated by [Claude Code](…)_" is replaced; the body now ends with
  exactly the two standard attribution lines.

## Notes for the maintainer
- **Adoption:** on #377's merge (after #376), adopt `$SP/olean-replay-6b-stmt-g46` (map `65ca0263…` after removing
  `Mathlib/`) if the merge's Lean paths equal `c56db4c4`. `$SP/olean-replay-6b-stmt` (R2) is no longer adoptable for
  #377; it is kept because the new tree's 1448 reused oleans are its hard links (deleting it frees nothing but its 4
  superseded oleans, and R1 `olean-replay-6b-o2` stays the #376 adoption tree).
- `CLAUDE.md` asks agents to use the LeanInfoView rather than build commands for proof state. This job ran the
  snapshot recipe's checker and probes (no `lake build`) because the maintainer's phase-2 recipe requires them.
- **Cleanup:** the export `$SP/le-g46-work/wtx`, the evidence staging tree and the other scratch were removed; kept are
  `$SP/olean-replay-6b-stmt-g46` and `$SP/le-g46-work/{run,tools,probe-src}` (the run as zipped).
