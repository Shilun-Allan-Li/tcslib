# cleanup-stage1 · maintainer review of checkpoint 1

**Verdict: PROCEED WITH NOTES.** The checkpoint meets its contract: every one of the 69 target
statements elaborates at the check tree, and decls2, the StmtDump, the shadow scan and the reuse
table are delivered.
- The patch series reproduces hash for hash at the issue base. Its merged tree equals the check head.
- decls2 gives exactly the brief's 69 declarations, with 0 CHANGED and 0 REMOVED.
- All 69 headers equal the brief token for token. All 7 pinned definition bodies are equal too.
- `protected` is right on all 69 names.
- The change is pure insertion, inside the Scope table, at the stated anchors. No frozen or
  other-campaign file is touched.
- All 69 proofs are complete already: there is no `sorry`.

Findings: **0 blockers, 0 majors, 3 minors, 8 infos.**
- All three minors are in the reuse/evidence layer and are fixed in the final, with no code change:
  - **F01:** an undisclosed overlap of the S1-27 `padTo` family with the public `padL`/`padStr`
    families;
  - **F02:** two copies missing from the Stage 2 table;
  - **F03:** search evidence the table cites but the delivery does not carry.
- One question goes to Seyoon. It merges the worker's CS1-W1 with F01.

## Delivery and integrity
- **Delivery:** exchange commit `bc2bf64a0c8449adb61234d957acb0e737fb66d5` ("fill cleanup-stage1:
  checkpoint 1"), an ancestor of the exchange tip `30ef1257…`.
  - It touches only `inbox/fills/cleanup-stage1/` (49 files). No later commit changes that path.
  - It is unsigned (no `gpgsig`), as `workflow.md` §4.1 asks.
  - I extracted it with `git archive` into a fresh empty directory.
- **Manifests:** top-level `SHA256SUMS` 48/48 OK and `checkpoint-1/SHA256SUMS` 47/47 OK. The path
  sets equal the delivered files exactly: nothing missing, nothing extra, no `./`.
  - At a checkpoint there is no `src/`, `REPORT.md` or `evidence/` tree. Those are for the final.
- **Issued package:** `shasum -a 256 -c` gives 8/8 OK. `brief.md` hashes to `56368c13…`, the
  dispatch pin.
- **Reproduction:** I made a scratch repository on alternates at the issue base
  `daa6e173cdd94cad1475b9a96eca613bce53ba61` and ran `git -c commit.gpgsign=false am
  --committer-date-is-author-date` of the five patches.
  - All five hashes equal `COMMITS.tsv` (`4881cf98`, `01f6b7e9`, `7b8a4d97`, `85797b50`, `c8021348…`).
  - The head is `c8021348f9bc2d16cfa52ca5e8ff489dc9543592`, with tree `508f9154…`.
  - The signing column says `none`, and the reproduction confirms the commits are unsigned. (My
    first `am` inherited this host's commit signing and produced other hashes; with signing off they
    match.)
- **Trees:**
  - `git merge-tree --write-tree f99901fd… daa6e173…` gives **`01cc6259480ccc9372181cd4d18d4511c87aa048`**,
    the check base.
  - `git merge-tree --write-tree f99901fd… c8021348…` gives **`985dd3125d8fd588cf2c8faa31ced8dee88407ab`**,
    the check-head tree the worker reports. They are equal.
  - All 19 home files are blob-identical at the issue base and the check base. Their base SHA-256s
    equal the Scope table's pins.
- **Records tip:** the worker fetched `8b5435eb…`, which had no Lean change since `f99901fd`. I
  verified that. The tip has since moved (F09).

## Scope, additivity and frozen files
- **Files:** `git diff daa6e173..c8021348` changes exactly the brief's 21 files: the 19 homes and the
  2 new modules. It has 1,079 insertions and **0 deletions**.
  - Every hunk is a pure `+` hunk (`@@ -n,0 +m,k`).
  - Removing the blocks gives back the issue base byte for byte.
- **Anchors:** every hunk sits at its Scope anchor:
  - `IterateFindHost` after 389, between `host_halt` and `end`;
  - `PPT` after `Coins` (222/223);
  - `BitLists` after 65 (`headD_drop_ofFn`), 99 (`zipWith_xor_cancel_left`) and 191 (a new section
    before `end`);
  - `Adversary` after `FunFamily.ofFn_blocks` (294);
  - `Sampling` after `StatClose.mono` (165), inside `section StatClose` (127–273);
  - `Encoding` after the `simps` attribute (39);
  - `EnsembleSecurity` after `encodeList_nil` (141/142);
  - `Trapdoor` after `pkPredictor` (283/284);
  - `Strings` after `length_encodeLog_le`;
  - `Experiments` after `prob_sample_eq_uprob`;
  - `Defs` after `toOracleAdversary_boundedBy` (339/340);
  - `Interaction` after `pairFstD_encodeMsgs`;
  - `EncodingMachines` before `end` (694);
  - `Games.lean` after 11 and 47;
  - `ZeroKnowledge.lean` after 7 and 41;
  - plus one docstring bullet hunk per existing non-facade file (17 files).
- **Frozen files are untouched:**
  - `Games/Probability.lean`, `Games/Relational.lean`, `Pairing/Group.lean`;
  - `Complexity/CircuitComplexity/**`, `Complexity/BranchingPrograms/**`;
  - `ComputationalModels.lean`, `machine-library-design.md`, `AdvancedEncryption/**` (GSW, IBE);
  - `Games/Hopping.lean` (CS1-Q9), `ModuleHost.lean`, `IterateFind.lean`;
  - every copy file, `TCSlib.lean` and `blueprint/`.
- **Imports:** the only import lines added are the two facade imports. `Games/Tapes.lean` imports
  exactly `Games.Hopping`. `InteractionWords.lean` imports exactly `ZeroKnowledge.Interaction` and
  `BinaryArith.Words`; at the check base neither imports the other, so there is no cycle. Both new
  modules reach the root through the facades.
- The new code has **no** `@[simp]` and **no** `sorry`.

## Statements (check 3)
- **decls2:** I ran the records' `decls2.py` (`fa81981a…`) on the reproduced head against the issue
  base, over the 21 files.
  - Result: **69 ADDED, 0 CHANGED, 0 REMOVED**, with an empty `.err`.
  - The output equals the delivered `statements/decls2.tsv` row for row.
- **Header check against the brief:** my own `stmtcmp.py` parses every `lean` block of `brief.md` and
  compares each declaration with the head source, normalizing only whitespace.
  - All **69/69** brief declarations match an ADDED name, and no ADDED name is left over.
  - Every header is token-identical, including the `protected`, `noncomputable` and `_root_.`
    prefixes.
  - The 7 definitions with a body pinned in the brief are identical including their bodies: `freshImpl`,
    `extTape`, `tapeImpl`, `ovr`, `recordBits`, `padTo`, and `zipWith_xor_cancel_right`'s header.
  - `FinDist.mixture`'s body is not pinned. It equals the Rejection copy (`Rejection.lean:395`) byte
    for byte.
  - Line-exact: 64/69. The other 5 differ only in line breaks, because the brief's single lines
    exceed 100 characters.
- **Homes and namespaces** all equal the brief:
  - `Complexity.IterateFind`, `TCSlib.Cryptography.Games`, `Games.EffFill`, `Games.Bridge`,
    `Games.OracleComp`;
  - `TCSlib.Cryptography` (incl. `FunFamily`, `StatClose`), `Authentication`, `PrivateKeyScheme`;
  - `Complexity.NUPPT` (incl. the `_root_` form in `Defs`), `Strategy`, `EncodingMachines`,
    `TCSlib.InformationTheory.FinDist`.
  - Kinds: 7 `def`, 62 `theorem`.
- **Elaboration evidence:**
  - The `StmtDump` probe ran with rc 0, 0 errors and 0 warnings. It prints `STMT-COUNT 69` with the
    full types. `probe-results.jsonl` binds its source (`bacc13db…`) and log (`cc91de2a…`); I
    rehashed both.
  - Sweep part 1 (129 modules: the homes, both new modules, both facades and their in-closure
    downstream) is 129/129 rc 0 with 0 errors. It covers every changed module. Its module times
    match the bootstrap's, so these were real compiles.
  - The bootstrap is 847/847 rc 0 with 0 errors. Its module list equals `order.txt`, and all 847
    source hashes equal the issued `SOURCE-SHA256SUMS`. Its 26 `sorry` warnings in 12 modules
    equal `base-sorries.txt` module by module.
  - This evidence settles elaboration, so **I ran no Lean** and did not use the olean snapshot.
- **Axioms** (`Axioms.log`): 69 prints and 0 `sorryAx`. The axioms used are a subset of {`propext`,
  `Classical.choice`, `Quot.sound`}. Two lists wrap across lines, which accounts for the worker's
  "34 all three".
- **Instances:**
  - Every S1-04 statement is the ETT `Tools.lean` statement with `Games.` qualification. `extTape`
    and its readers differ from `AdaptiveCPA`'s only in where `{C} [Nonempty C]` are bound.
  - I spot-checked these copies; each is an instance or an identical statement:
    - S1-12 `HashSignFill.eq_pure_of_cost_zero` and Lamport `exists_pure_of_cost_zero`;
    - S1-14 `BlockEncryptor.lean:60`;
    - S1-10 `FromDiscreteLog/Probability.lean:40`;
    - S1-22 `DDH.lean:146`;
    - S1-27 against both machine files: `flatMap_range_ite`, `polyTimeComputable_flatMap_range`,
      `iterSnd_poly`, `padTo`/`_eq`/`_poly`/`length_`/`getD_`, and `Assembly.lean:98`.
  - No statement looks false; all are proved. No listed copy fails to be an instance.

## `protected`, clashes and shadowing (check 11)
- **Short names:** I indexed all 31,425 declaration lines at the check base (`TCSlib/`, `audits/`,
  any modifier, private included).
  - Every one of the 54 `protected` names has a same-short-name declaration, except
    `Games.extTape_of_not_lt`. The brief makes every S1-04 name `P`, so that is as the brief says.
  - All 15 unprotected names are fresh in TCSlib. They are also absent from Mathlib (`029db123`,
    the manifest pin), Batteries, Aesop, Plausible, Qq and core 4.25.0 (no `List.getD_ofFn`).
  - Result: **0 unprotected names with an existing short name.**
- **Exact full names:** 0 clashes. I resolved namespaces in the 30 files that declare one of the new
  short names (79 declarations).
- **Shadowing:**
  - The delivered scan (361 hits, 0 needing attention) covers unqualified short names.
  - I extended it to the two forms that `protected` does not hide:
    - **partially qualified** uses (`FinDist.map_map`, `Games.ovr`, `Strategy.…`; 198 suffix
      forms): **0** occurrences at the check base;
    - **dot notation** on a value: **0**. Every `.x` hit is a fully qualified other name, such as
      `List.map_map`, `AdaptiveCPA.extTape`, `Rejection.uniform_prod` or `ColMachines.iterSnd_poly`.
  - So no existing name changes its resolution.

## Docstrings, tags, facades, sizes
- **Docstrings:**
  - All 69 open with a statement in words and give the formula.
  - 68 carry the glue note ("Framework glue, no textbook counterpart", with the first consumer where
    useful).
  - `pkPredictor_apply` carries `[PS10, Theorem 104.4, proof]`, as the brief says. No other tag was
    invented.
  - Every proof of 15 lines or more has a `**Proof sketch.**`:
    `ofFn_blocks_symm_eq_flatMap`, `of_uprob_ne`, `expect_simulate_abs`/`_inv`,
    `expect_simulate_tapeImpl`, `polyTimeComputable_flatMap_range` and `iterSnd_poly`.
    `map_uniform_equiv`'s proof has 14 lines, so it needs none.
  - Every changed module docstring has a bullet. The new modules have the full header, with
    References in the verbatim [PS10] entry plus the brief's locator ("Theorem 170.4 (book p. 170):
    the first consumer"; "§4.4"). Nit: F10.
- **Facades:**
  - `Games.lean` imports `Games.Tapes` after line 11, and its `## Contents` entry after line 47 is
    the brief's text.
  - `ZeroKnowledge.lean` imports `InteractionWords` after line 7, and its entry after line 41 is the
    brief's text.
  - Both entries add the facade's backtick style; the worker disclosed this.
  - bb1-sim's anchors (after 9 and 42) are untouched.
- **Sizes and width:**
  - The largest files are `Asymptotic/Sampling.lean` at 965 lines and
    `ZeroKnowledge/EncodingMachines.lean` at 867 (the brief estimated ~830). `Games/Tapes.lean` has
    346 lines and `InteractionWords.lean` 44. Every file is under 1,000.
  - The maximum width of an **added** line is 100 characters. No tab, trailing space or micro sign
    is added.
  - The over-100 lines in `PPT`, `Adversary`, `Sampling`, `EnsembleSecurity`, `Trapdoor`, `Defs`,
    `EncodingMachines` and `Interaction` are all base lines, with the same maxima at the base.
- **Lint** (`style_lint`, campaign lint) is check 8 of the final. I did not re-run it here; the tool
  resolves paths against the repository root, not a scratch tree.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| CS1-C1-F01 | **minor**, undisclosed overlap (check 12) | The S1-27 `padTo` family overlaps two public padding families. The reuse table does not mention them, and neither does the ledger.<br>• `EnsembleLemmas.padL` with `padL_eq : padL k a = (a ++ 0^k).take k`, `length_padL` and `polyTimeComputable_padL` (`Asymptotic/EnsemblesLemmas.lean:191–230`). At `p = .var` and `u = 1^{L x}` it gives `padTo_poly` through `padL_eq`. Conversely, `padTo_poly` gives it through `StateLoop.unaryPoly_comp`.<br>• `CollectionsLemmas.padStr`/`padStr_eq`/`polyTimeComputable_padStr`/`padStr_of_length_le` (`Asymptotic/CollectionsLemmas.lean:75–114`).<br>• Instances: `GI.padSq`/`GIZK.padSq` (`L = n·n`) and `HardCoreGLColl.padToLen`.<br>Neither family is in `EncodingMachines`' closure. Both are in the closure of **both** consumers (`ThreeColoring/Machines` and `ComposeSecurity/Machines` import `EnsemblesLemmas` and `CollectionsLemmas`).<br>This is the same kind of overlap as the worker's CS1-W1 `zeros_poly`, which was disclosed; this one was not. It is not a restatement, since the constants differ, so per BS-F01's precedent it is a minor. | Disclose it in the final's *Overlap and reuse* and Stage 2 table. Seyoon rules with CS1-W1 (**Q1** below). No code change unless Seyoon chooses (c). |
| CS1-C1-F02 | **minor**, missing copies | The reuse table reports "none" further for these two rows, but the check base holds:<br>• **S1-27 `polyTimeComputable_flatMap_range`:** the public `emitLoop_poly` (`ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:180`). It is an instance, with an extra hypothesis `L z ≤ |z| + 1`, and has the same proof. Its companion `flatMap_range_ite` at `:160` *is* listed.<br>• **S1-21 `encodeMsgs_eq_encWords`:** an inline copy, `henc` in `decodeMsgs_encodeMsgs` (`SecureComputation/Yao.lean:355`, in the declaration at `:353`). | Add both to the Stage 2 table in the final. |
| CS1-C1-F03 | **minor**, evidence | The reuse table cites sub-agent search evidence that the delivery does not contain: `subagents/A/NOTES.md`, `reuse-grep-1.txt`, `copylist-check.txt`, `subagents/B/NOTES.md`, and the raw `exact-lead/` and `exact-ab/` directories. Only the lead's two greps, the two `exact?` probes and their logs are delivered, so the search record for sub-agents A and B's 50-odd declarations cannot be audited. Sweep part 1 is delivered as a progress file only, without per-module source hashes or raw logs. | The final delivers all of it under `evidence/`, with a manifest, including `evidence/build/summary.txt` bound to `git show HEAD`, as the brief's *Evidence completeness* requires. |
| CS1-C1-F04 | info, CS1-W1 checked | I confirmed the worker's facts: `Games.EffFill.zeros_poly` (`Strings.lean:152`) and `EnsembleLemmas.polyTimeComputable_zeros` (`EnsemblesLemmas.lean:212`) are public, inter-derivable with S1-27 `zeros_poly`, and outside `EncodingMachines`' closure.<br>But option (b)'s claim that "the ThreeColoring copy would then have no Stage 2 target" is inaccurate:<br>• `ThreeColoring/Machines` imports `EnsemblesLemmas`, so its `zeros_poly` re-derives as `(EnsembleLemmas.polyTimeComputable_zeros .var hL).congr …`;<br>• `ComposeSecurity`'s `padTo_poly` already derives the same zero word from `GI.zeros_poly` composed with `hL`.<br>The table calls `GI.zeros_poly`/`GIZK.zeros_poly` "homonyms, other statements"; they are relatives (`0^{|w|}`). | Folded into **Q1**. |
| CS1-C1-F05 | info, binder order | `FinDist.map_uniform_equiv`, `sum_map` and `uniform_prod` (`FinDist.lean`) bind `{α} [Fintype α] {β} [Fintype β]`, using the file's own `α` variable. The brief's variable line and the Rejection copies bind `{α β} [Fintype α] [Fintype β]`. The header text is equal; only the order of implicit and instance binders differs. No `@` use of any copy exists at the check base, and the proof-only re-points of Stage 2 are unaffected. | None. Optionally, the final notes it under *Statement changes* as "binder order only". |
| CS1-C1-F06 | info, near relatives | The table does not name two relatives:<br>• `ProbComp.expect_simulate_congr` (`Games/Hopping.lean:384`): the same-state, unbudgeted relative of S1-04 `expect_simulate_abs`;<br>• `EncodingMachines.flatMap_range_ite_eq` (`EncodingMachines.lean:368`): the singleton-chunk special case of S1-27 `flatMap_range_ite`. The new docstring cites it.<br>Neither is a more general form, so neither is an E-DUP. | List both in the final's table. `flatMap_range_ite_eq` is an optional Stage 2 re-derivation in its own file. |
| CS1-C1-F07 | info, near relative after the check base | bb1-sim's `Games/Relational.expect_simulate_rel` landed after the check base (a statement with `sorry`; the fill is pending). It is a relational coupling form, but it does not subsume `Games.expect_simulate_abs`: abs's hypothesis holds only while `cnt s < κ`, and `rel` needs it from every related state. | Gate 47 note: the two forms are distinct; the final may cite `expect_simulate_rel` as a relative. |
| CS1-C1-F08 | info, counts | `CHECKPOINT-1.md` says "+1,075 lines"; the series has +1,079 (21 files, 0 deletions). `EncodingMachines` ends at 867 lines, not the brief's ~830; it is still under 1,000. | Correct the count in the final. |
| CS1-C1-F09 | info, landing | The records tip moved after the worker's fetch. It is now `62df03f97f9259f4f5668260448ad9385e64541d`: the bb1-sim Games statements (`02000ad4`, `dfacac35`) and the group PR #352 (`2cca41bc`, `92dea4f8`, merge `463f2244`) have merged. These change `Games.lean`, `Games/Probability.lean`, `Games/Relational.lean` and `Pairing/Group.lean`. `git merge-tree --write-tree 62df03f9… c8021348…` is clean, with tree `11695b1f8619f7cec575923298063faf145bb7c7`. `Games.lean` merges as a union (70 lines: `Relational` and `Tapes` imports and both Contents entries). No new Stage 1 name meets a name bb1-sim added. | The final states the tip it used. Landing re-replays at the tip (`workflow.md` §6.1), on snapshot #4's successor. |
| CS1-C1-F10 | info, docstring nit | The `Games/Tapes.lean` module docstring lists the definitions and 13 lemmas, but omits the readers `freshImpl_apply` and `tapeImpl_apply` from `## Main results`. | Optional one-line fix in the final. It is a pure insertion either way. |
| CS1-C1-F11 | info, for the final's seals | I read the new proofs for Rule 10. There is no `unfold`, `delta` or `change`. Steps to watch in the seals:<br>• the trailing `rfl` of `ofFn_splitBits_fst`;<br>• `FinDist.mixture_apply := rfl` (through `FinDist`'s `CoeFun`; notation per DW-10 Q3, so it may fail only in the strict variant);<br>• unrestricted `simp`/`simpa` in `host_branch_view`, `flatMap_range_ite` (`zero`), `FinDist.sum_map` and `map_apply_expect`;<br>• the `show` steps in `Games.expect_sample_ovr` (its own definition, in its own file: allowed);<br>• `cases b <;> rfl` and `split_ifs <;> rfl` (core `ite`). | Final, check 6. No action now. |

## Questions for Seyoon

**CS1-C1-Q1 (with CS1-W1; F01, F04).** The S1-27 zero word and padding duplicate existing public
forms. Those forms live outside `EncodingMachines`' closure, but inside both consumers' closures:
- the zero word: `EffFill.zeros_poly`, `EnsembleLemmas.polyTimeComputable_zeros`, `GI.zeros_poly`;
- the padding: `EnsembleLemmas.padL`/`polyTimeComputable_padL`, `CollectionsLemmas.padStr`.

CS1-Q8 put "the `padTo` family" in the shared toolkit without considering these forms. The choices:
- **(a) Recommended. Keep S1-27 as CS1-Q8 ruled (69 declarations).** The unary-length forms belong
  in the shared unary toolkit, beside `truncate_poly` and `unaryLength_poly`, which both consumers
  already import directly. The final discloses every overlap. A new ledger row puts the
  `padL`/`padStr`/`padSq`/zero-word families into one consolidation after the campaign merges.
- **(b) Drop `zeros_poly` only (68 declarations).** Inline the zero word in `padTo_poly`. Stage 2
  re-derives the ThreeColoring copy from `EnsembleLemmas.polyTimeComputable_zeros .var`.
- **(c) Withdraw `zeros_poly` and the `padTo` family (62 declarations; partly reverses CS1-Q8).**
  Stage 2 re-points both consumers to `EnsembleLemmas.padL` and `polyTimeComputable_padL`.
  `getD_padTo` and `padTo_of_length` have no `padL` counterpart, so Stage 2 would add two `padL`
  readers to `EnsemblesLemmas` instead.

## What the final must add (beyond the brief's list)
- F01–F03: disclose the `padL`/`padStr` overlaps, add `emitLoop_poly` and `Yao.lean:355` to the
  Stage 2 table, and deliver the sub-agent and raw search evidence and the sweep binding.
- F05, F06, F08 and F10 as noted.
- State the records tip used and the merge-tree against the current tip (F09).

## Evidence
- `checkpoint1-review-evidence.zip` (SHA-256 in `evidence-SHA256SUMS`), under `cs1-c1/`:
  - `PROVENANCE.txt`;
  - `tools/`:
    - `stmtcmp.py`, `linecmp.py`: brief against head;
    - `shortclash.py`, `fullclash.py`: the protected rule and full-name clashes;
    - `closure.py`: import closures from `git grep '^import'` at the check base;
    - `doccheck.py`, `width.py`;
    - an unmodified copy of `decls2.py`;
  - outputs:
    - `decls2.mine.tsv`, `stmtcmp.out`, `shortclash.out`, `doccheck.out`, `sizes_head.txt`;
    - `full.diff` (`-U0`) and `am_hashes.txt`;
    - `mt_tip.txt`: the merge-tree at the current tip;
    - `partial_re.txt` and `partial_hits.txt` (empty), `dot_hits.txt`;
    - `ett_cmp.txt`: the S1-04 statements against the ETT and AdaptiveCPA copies;
    - `changed.txt`.
- Scratch repository, clone and extraction directories were deleted after the review. Nothing was
  committed or pushed. No Lean process was run, and the olean snapshot was not touched.

**Not yet clear to merge — checkpoint 1 only: the final (checks 1–12, seals, controls, full sweep) and CS1-C1-Q1 are pending; the worker may proceed to the final.**
