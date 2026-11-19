# EF-H1 `ef-h1-arith` · landing (P2-8)

**Branch `land/ef-h1-arith`, pushed; head `ff0e93cec755e087ecac59a5449c74d9d8eaf658`, tree
`d5c7826c55db2cf65e9deef2ea24ac6913ca5d76`.** The re-check passed on the landing head. The draft PR
is for Seyoon to open; its body is below.

- **Base.** The branch is cut from `origin/cryptography/pass-shelat-ch2-4` =
  `1a59b01321f310d82fb94f640a953c15906d3962`, the records tip. It is Lean-equal to snapshot #11's T
  `bff0567b`: `git diff --name-only bff0567b 1a59b013 -- TCSlib TCSlib.lean audits lakefile.lean
  lake-manifest.json lean-toolchain` is empty.
- **Rulings applied** (decision log, 2026-11-18):
  - EF-W1-R (A): readers go in their owner files;
  - EF-H1-R2 (B): the bounded bridge for the two Complexity readers, ledger DL-69;
  - W2 (A): closed;
  - W3 (A): anchors.
  - The `PrimesBridge.` namespace of the two bridge readers was confirmed by Seyoon on 2026-11-19.
- **Diff against `bff0567b`:** 6 Lean files, +1,070, 0 deletions. They are the 4 series files,
  `Candidates/Arithmetic.lean` and the new `Candidates/PrimesBridge.lean`.
  **`TCSlib/Complexity/**` is byte-identical to the base**, so `Randomized/Primality{,Math}.lean` are
  untouched.
- **Work location.** Worktree `$SP/land-efh1/wt`; replay tree `$SP/olean-replay-efh1-land`; evidence
  in `$SP/land-efh1/` (`logs/`, `build/`, `plan/`, `rule10/`). `$SP` is
  `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## Commits (8, all signed: one `gpgsig` each)

| # | Commit | Subject | Author / form |
|---|---|---|---|
| 1 | `602544fa7f9ef6780fb7ed46aaab89abfe377413` | EF-H1: the cheap ArithmeticFP fields from the BinArith machines | worker; `git am -3 -S`, message verbatim (I7) |
| 2 | `21736279ed10a608b22f2e955282308c81706f87` | EF-H1: the extended Euclidean algorithm as a polynomial-time loop | worker |
| 3 | `8fc6fd8e7a492a077f7eb7c383c32da58b775c8f` | EF-H1: PrimesInP, the one remaining arithmetic hypothesis | worker |
| 4 | `0edf71f8899ab537918ebf656afdab4906ebe33f` | EF-H1: Candidates facade imports the three new modules | worker |
| 5 | `5aa162508b89053dfea17eceeef7a8144d89ef82` | EF-H1: readers of the extended Euclidean loop's definitions | worker |
| 6 | `0825c5bed4a8cb79bbfd1d3fd6aad815fafb5050` | LE-h1-readers | maintainer landing edit |
| 7 | `b0a62d37d4d7a5e743f578f355807159e07ed992` | LE-h1-bridge | maintainer landing edit |
| 8 | `ff0e93cec755e087ecac59a5449c74d9d8eaf658` | LE-h1-doc | maintainer landing edit |

- **Series (1–5).** These are the delivery's patches from exchange
  `0e18bf6df1ef27feba575bbb1e910cc2a8c36aa2`, identical to the extracted copy reviewed in phase 1.
  - Author, author date and message are kept.
  - After commit 5, the 4 files are byte-identical to the delivered `src/`.
- **Landing edits (6–8).** Paths were staged explicitly, and each message ends with this session's
  `Co-Authored-By` and `Claude-Session` lines.

## The landing edits

- **LE-h1-readers** (EF-W1-R (A)).
  - **S1–S7** are `mulStr_eq`, `addStr_eq`, `subStr_eq`, `divModStr_eq`, `xgcdStr_eq`,
    `modExpStr_eq` and `leStr_eq`, each `rfl`, in the worker's overlay text.
    - They sit in `Candidates/Arithmetic.lean`, after the existing unfolding lemmas, under the header
      `### Every-input equations`. F06: the "(scope request …)" process note is dropped.
    - The module's `## Main results` lists them.
  - **The seven field theorems** `polyTimeComputable_{mul,add,sub,divMod,modExp,le}Str`
    (`ArithmeticDischarge.lean`) and `polyTimeComputable_xgcdStr` (`ExtendedEuclidMachine.lean`).
    - These are R2's statements, proofs and module-docstring updates.
    - F06: the double blank lines are removed.
- **LE-h1-bridge** (EF-H1-R2 (B), DL-69).
  - **The new file `Candidates/PrimesBridge.lean`** holds exactly the two readers. Each has the
    overlay's statement and its `Iff.rfl` proof:
    - `PrimesBridge.mem_PRIMES (N) : N ∈ Randomized.PRIMES ↔ N.Prime`;
    - `PrimesBridge.mem_PRIMESBin (x) : x ∈ Randomized.PRIMESBin ↔ bitsVal x ∈ Randomized.PRIMES`.
  - **Its module docstring** records three things:
    - it is a bounded Rule-10 exception, to be deleted when the Complexity owner PR merges;
    - the readers sit in their own namespace, as in EF-H12's `LevinHardness/Bridge.lean`, so the
      owner's names cannot clash with them;
    - **the re-point is a rename:** `PrimesBridge.mem_PRIMES` becomes `Randomized.mem_PRIMES` and
      `PrimesBridge.mem_PRIMESBin` becomes `Randomized.mem_PRIMESBin`, with the statements unchanged.
  - **`PrimesInP.lean`** gets R2's six declarations, re-pointed to the bridge names:
    - `primeBit_eq_indicator`;
    - `primesInP_iff_polyTimeComputable_primeBit`;
    - `polyTimeComputable_primeStr_of_primesInP` and `primesInP_of_polyTimeComputable_primeStr`;
    - `ArithmeticFP.ofPrimesInP`;
    - `arithmeticFP_iff_primesInP`.

    It imports `PrimesBridge` instead of `Complexity.Randomized.Primality`, and its docstring names
    the bridge.
  - **The facade** imports and lists `PrimesBridge`. `campaign_style_lint` requires every child
    module to be imported.
- **LE-h1-doc** (docstrings only; no statement or proof changes).
  - **F03:**
    - `fromLEPoly_var_bits` is disclosed as a one-line specialization of `fromLEPoly_pairEncode`;
    - the `ZMod 0` branch of `xgcdInvWord_spec` is disclosed as derived inline. The reason:
      `val_inv_natCast_zmod_zero_le` states only `≤ 1`, and Mathlib has no equality lemma.
    - The ledger note F03 asks for, with I4, is records work and is not done here.
  - **F04(b):** the five Glue `polyTimeComputable_{mul,add,sub,divMod,le}Str_pairEncode` lose their
    `[AB09, §7.2]` tag (COMMON §4.6: Glue carries no tag).
  - **F05:** labelled `**Proof sketch.**` paragraphs for `xgcd_coef_residue` and
    `polyTimeComputable_xgcdLoopStep`. The optional `xgcdLoopMeasure_eq` was not added, because it
    would be a new declaration.
  - **F06:** the facade's `## Contents` names the field theorems, `ArithmeticFP.ofPrimesInP` and
    `arithmeticFP_iff_primesInP`.
  - **The bridge's rename note**, added after Seyoon confirmed the namespace.
  - **W3:** the chapter-notes anchor `pdf-26d95080dbde-p017-b002` is a records-only correction. The
    Lean cites no block id, so nothing changes there.

## Re-check on the landing head `ff0e93ce`

The recipe was `snapshots.md`'s job recipe on a fresh `cp -al` copy of snapshot #11, not a copy of
`olean-replay-efh1`, which holds run B's overlay builds of the Complexity files.
- **Copy:** `$SP/olean-replay-efh1-land`, 1,487 hard links.
  - `mloverlay.sh` made 3,346 links.
  - `NthRootLemmas` was built with rc 0; its olean is `c0a9cff0…`.
- **Lean processes:** one at a time, through `runq.sh`, which checks before every start that the
  host has at most 2 other Lean processes. The host maximum observed was 2 others, so 3 in all.

| Check | Result |
|---|---|
| **Snapshot #11** | `snapmap.py verify`: **0/0/0**, `RESULT OK`, before the copy, after the container restart, and at the end. Map `e7bb03b4…867d0`. |
| **Plan** | `stateplan init` at `bff0567b` (1,456 modules). `downorder`: 6 changed, 70 downstream. `fullorder`: 1,460, with roots `TCSlib` and both `audits/*/Checks`. **70 to build, 1,390 reused.** |
| **Build** | **70/70 rc 0.** `error:` 0, `error(` 0, the substring "error" 0 (`permod.py`, no log/record mismatch). 511 s; peak maxrss 4.56 GB. Includes the root `TCSlib`, `audits/garg-ch1-3/Checks`, `audits/pass-shelat/Checks` and every importer of `Candidates/Arithmetic.lean`. |
| **`sorry` and warnings** | 5 `sorry` and 13 warnings, **all pre-existing** in untouched files (the same set as phase 2 run B): `GSW/PolyRatio` 3 + 3, `GSW/Asymptotic` 2 + 2, `Candidates/DDH` 3, LWE `Flat` 5. **None in a changed module.** |
| **Accept** | `stateplan update`: 70 modules, none left out. `check`: **1,460/1,460, RESULT OK.** Each of the 70 has source SHA-256 equal to the head's file, object SHA-256 equal to its record, and link count 1. Exactly 70 non-Mathlib oleans in the tree have link count 1. |
| **Axioms** | (`AxiomProbe.r2` form, through `runner_full.py`.) The owners `ArithmeticDischarge`, `ExtendedEuclidMachine`, `PrimesInP` and `PrimesBridge`, plus the 7 `Arithmetic.lean` readers by name: **84 constants.** That is 67 declarations (the 65 new public ones plus `xgcdInvWord.eq_1` and `xgcdLoopMeasure.eq_1`), 10 `_proof_N` auxiliaries and 7 readers.<br>Axiom sets: `[Classical.choice, Quot.sound, propext]` 46; `[Quot.sound, propext]` 28; `[propext]` 7; `[]` 3. **0 non-standard.**<br>All **72** decls2-ADDED names are present. The `sorry` control reports `[sorryAx]`. |
| **Smoke test H1-P2** (delivered `H1P2.lean`, unchanged) | **rc 0, 0 errors.** The output is **identical to the delivered `scope-request/H1P2.log`**: `ofPrimesInP h` is accepted as `H` by the factoring, RSA and DL collections and by `polyTimeComputable_expEval`, and the 13 targets are `[propext, Classical.choice, Quot.sound]`. |
| **H1-P1** (delivered, unchanged) | rc 0; output **byte-identical** to the delivered `probes/H1P1.log`. |
| **Paired controls for the new readers** (`Ctl_sealed` / `Ctl_unsealed`) | `modExpModulus`, `xgcdState`, `PrimesInP`, the seven `*Str` and `Randomized.PRIMESBin`/`PRIMES` made locally irreducible.<br>Sealed: **exactly 12 errors, one at each NEG line**: NEG1–3 (the owners' definitions), NEG4–10 (`rfl` body reads of `mulStr` … `leStr`), NEG11–12 (`Iff.rfl` on `PRIMESBin` and `PRIMES`).<br>**All 12 POS pass**: the owner readers, S1–S7, and `PrimesBridge.mem_PRIMESBin` / `mem_PRIMES`.<br>Unsealed: 0 errors. |
| **Canonical coe-A seal** (`mkcollect`, `mkseals_coe` with `SEAL_CHUNK=1000`, `sealsum`) | `Arithmetic` 913 requests: **0 errors.** `ArithmeticDischarge` 1,021: **0.** `ExtendedEuclidMachine` 1,028: **0.** `PrimesInP` 2,912: **0.** Every probe has install and EOF records.<br>**`PrimesBridge`** (2,648 requests, the sanctioned exception): rc 1 with **exactly 2 errors**, at src 56 (`mem_PRIMES`) and src 61 (`mem_PRIMESBin`). These are its only reads: the bodies of `Randomized.PRIMES` and `Randomized.PRIMESBin`.<br>The facade `Candidates.lean` has no declarations, so it was not sealed. |
| **decls2 against `bff0567b`** (pinned `decls2.py`, `0ba6f6a1`) | **72 ADDED, 0 CHANGED, 0 REMOVED.** Names and normalized statements equal the delivered series plus overlay rows (phase 1 C3: 50 + 22). The only difference is the two bridge readers' names, `TCSlib.Cryptography.Candidates.PrimesBridge.mem_PRIMES{,Bin}` instead of `Randomized.mem_PRIMES{,Bin}`. Their statements are the same, with `Randomized.` written out. |
| **Lint** | `style_lint.py` on the 6 changed files: **0 findings.** `campaign_style_lint.py TCSlib/Cryptography --check8b`: 92 FAIL / 103 WARN over 544 files, and the FAIL/WARN line set equals `bff0567b`'s, so **no delta.** No line wider than 100 characters in the new or edited text. |
| **Complexity owner files** | `git diff bff0567b ff0e93ce -- TCSlib/Complexity` is empty. |

**Other trees.**
- `$SP/olean-replay-efh1` (run B) is unchanged: 76 rebuilt oleans match
  `runB/rebuilt-oleans.sha256`, and the rest are snapshot hard links (0 bad, 0 missing).
- `$SP/olean-replay-efh1-land` is kept for the gate.

**Process notes.**
- A container restart killed the first replay (head `b460116d`) at `Pairing`.
  - Its olean had been unlinked and not rewritten.
  - The 53 modules built before it checked clean, and the rest were still snapshot links.
- On resuming, the disk guard stopped the driver at 1,960 MB free, below the 2,000 MB floor, because
  other jobs were growing.
- After the disk was freed, the bridge docstring got the rename note. That changed the head to
  `ff0e93ce`, and **all 70 modules were rebuilt from that head's export**. The numbers above are
  only from that run.
- `build-old-b460116d/` and `plan-old-b460116d/` are kept for reference only.

## Draft PR body

Base: `cryptography/pass-shelat-ch2-4` · head: `land/ef-h1-arith` (`ff0e93ce`)

```markdown
EF-H1 (`ef-h1-arith`): the cheap `ArithmeticFP` fields, extended Euclid, and `PrimesInP`

Efficiency wave 1, job EF-H1. This discharges eight of the nine fields of the arithmetic hypothesis
bundle `ArithmeticFP` with no hypothesis, and reduces the ninth to `PrimesInP := PRIMESBin ∈ P`.
That is a named, true `Prop` (Agrawal–Kayal–Saxena), never an axiom (ruling Q5 A).

**What lands**
- `ArithmeticDischarge.lean`: `polyTimeComputable_{mul,add,sub,divMod,modExp,le,size}Str`, from the
  `Complexity.BinArith` machines and the `Encoding.BinaryArith` adapters. Modular exponentiation is
  [PS10, Algorithm 45.5, Theorem 45.6]; the modulus 0 runs at `2^{|N|}`.
- `ExtendedEuclidMachine.lean`: `polyTimeComputable_xgcdStr`, extended Euclid
  [PS10, Algorithm 43.2, Claim 43.3]. It is polynomial-time for every modulus and agrees with
  Mathlib's `Nat.gcdA` and `ZMod.inv`.
- `PrimesInP.lean`: `PrimesInP`, the bridge `PrimesInP ↔ PolyTimeComputable primeStr`,
  `ArithmeticFP.ofPrimesInP` and `arithmeticFP_iff_primesInP`.
- `Arithmetic.lean`: every-input readers `mulStr_eq` … `leStr_eq` (`rfl`), a maintainer landing edit
  under EF-W1-R (A).
- `PrimesBridge.lean`: a **bounded reader bridge**, a recorded Rule-10 exception (EF-H1-R2 (B),
  ledger DL-69). It holds only `PrimesBridge.mem_PRIMES` and `PrimesBridge.mem_PRIMESBin`
  (`Iff.rfl`), because `Complexity/Randomized/Primality{,Math}.lean` are Arora–Barak-owned and are
  not edited here. **A Complexity owner PR adding `Randomized.mem_PRIMES{,Bin}` is to follow.** When
  it merges, this file is deleted and the three consumers are re-pointed by a rename.

**Commits:** 5 worker commits (messages verbatim), then 3 signed maintainer landing edits:
LE-h1-readers, LE-h1-bridge and LE-h1-doc (review findings F03–F06; docstrings only).

**Checks** (merged-tree replay on olean snapshot #11, `bff0567b`, which is Lean-equal to the base):
- 70/70 changed and downstream modules rc 0, including the root `TCSlib` and both `audits/*/Checks`.
  0 errors; no `sorry` in any changed module (the 5 pre-existing GSW statement `sorry`s are
  untouched).
- State check 1,460/1,460 OK.
- `#print axioms`: all 72 new public declarations use only `propext`, `Classical.choice` and
  `Quot.sound`.
- The consumer smoke test passes: `ofPrimesInP h` is accepted as `H` by the factoring, RSA and DL
  collections.
- Canonical coe-A seals: 0 errors on `Arithmetic`, `ArithmeticDischarge`, `ExtendedEuclidMachine`
  and `PrimesInP`. `PrimesBridge` fails exactly at its two sanctioned reads.
- Paired controls: the 9 new readers pass sealed, and the matching body reads fail.
- decls2: 72 ADDED, 0 CHANGED, 0 REMOVED.
- `style_lint` 0 findings; campaign lint has no delta.
- `TCSlib/Complexity/**` is unchanged.

**Gate:** the Codex gate is to be staged.

Review: `briefs/efficiency-gaps/wave1/EF-H1/final-r1/{review,phase2,landing}.md`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
```
