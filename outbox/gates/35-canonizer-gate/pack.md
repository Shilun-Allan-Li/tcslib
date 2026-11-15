# Gate 35 · Some effective machine code has an exponential canonizer (`canonizer`, `exists_canonizerExp`)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #319](https://github.com/Shilun-Allan-Li/tcslib/pull/319) at
  `6421ac1631ef08feed297c810f0839b178d2a2bb` (branch `land/pass-shelat-canonizer`, tree
  `3e16398e47f1c57b1d26c85ed731650dd094940b`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `a334ec2e1d87dbde7eac40812286ba60e85c9078` (the merge base: the records tip after #315 merged).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The three pre-existing files have the same
    blobs at the issue base and at `a334ec2e` (`pack-checks/headers.txt`). Between them #307, #311, #312, #314 and #315
    merged; the review's builds cover them (`build-r3`: the downstream of every module changed since `eff2dcd0`).
  - The records tip is now `1321b9cb358867f5b51974b8c5d0781519a9cfdb`. Since `a334ec2e` it has merged **#317**
    (prf-mac, `1d9b2ac3`) and **#316** (headD promotion, `1c09448c`). Their 8 Lean files are not in the PR, and the
    PR is **not** rebased onto them (below, *Pending merge condition*).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...6421ac16`, which equals `a334ec2e..6421ac16`
    byte for byte (4 paths, 133 insertions, 28 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313 (`94b31964`), #316
    (`c18afbe6`), #317 (`590d1a56`) and #318 (`f62a25b3`, sc-ot) is clean in each case, and no path is shared
    (`pack-checks/mergetrees.txt`). The owned module `Universal` is downstream of #316's `Foundations/BitLists` (now
    on the tip). **Pending merge condition** (not an audit item): #319 needs an integration rebuild on the merged tip
    before it merges, and whichever of #318 and #319 merges second needs one too; the maintainer runs these builds
    (question 7).
- **Commits:** 3, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 2 commits (job `canonizer`), applied with `git am` with the delivered committer data. The
    worker hashes `7064488b`, `ba7096e8` reproduce only with the environment's signing on (review C-F04). They were
    then rebased twice without conflict, author kept: `523d98ccc275697eceb377662977156b7514cf0c` (checkpoint 1: the
    two `rfl` readers, pre-approved) and `11b24a7ec53d0a3fe0960c177da8bffcd17eb69b` (`exists_canonizerExp` proved).
    At `11b24a7e` the 4 files are byte-identical to the worker's `src/` (exchange `27ae588d`;
    `pack-checks/rebase.txt`).
  - Landing edit **LE-doc** `6421ac1631ef08feed297c810f0839b178d2a2bb` (the head): one formula docstring, docstrings
    only.
- **Scope:** a **proof audit**. The job proves the admitted `TCSlib.Cryptography.exists_canonizerExp` [PS10, §2.13;
  run-3 audit P3-4; DESIGN D11]: some `c : EffectiveMachineCode` has `CanonizerExp c`, that is
  `∃ A B, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)`. The statement is frozen (the ch. 2–4 run-3 audit, Gate 03h) and
  quoted in the brief. The headlines of `Universal.lean` (`fUniversal_easy`, `fUniversal_hard`,
  `fUniversal_weakOneWay`, `theorem_63_1`) take `CanonizerExp c` as a hypothesis and stay conditional; no declaration
  consumes the target.
- **Brief:** `fills/canonizer/issued-r1/brief.md` on the records branch (SHA-256 `505b3eb6…`). Two checkpoints: the
  readers (a scope request was expected) and the scheme with the bound.
  - The owned file plus the helper directory `Asymptotic/Universal/` only; every other file frozen.
  - The superseded `Build/` sketch is to be replaced: use the existing `exists_polyCanonizer` rather than rebuild it.
  - The binding duplication rule with an `## Overlap and reuse` section, with nearest relatives
    `Turing.exists_uniformMachineCode` (`Diagonalization/EXPCOM.lean:156`) and `Turing.exists_effectiveMachineCode`.
  - Rule 10 with the projection-coercion ruling, and seals with `PolyExpr.eval` both excluded and sealed.
  - The formula-docstring and sketch rules, the G26-N1 error count and the evidence-completeness rule.
- **Ruling:** `fills/canonizer/rulings/2026-11-14-readers.md`. Seyoon pre-approved exactly the two `rfl` readers of
  checkpoint 1 (ruling 1 below).

## What changed

The PR touches 4 Lean files: 2 frozen machine-library files (one pre-approved reader each), the owned file, and 1 new
helper (133 insertions, 28 deletions). Line counts are base → readers `523d98cc` → proof `11b24a7e` → PR head.

| File | Status | Lines |
|---|---|---:|
| `Cryptography/Asymptotic/Universal.lean` | owned, modified | 945 → 945 → 955 → 955 |
| `Cryptography/Asymptotic/Universal/Canonizer.lean` | helper, new | — → 82 → 83 |
| `Complexity/TuringMachine/CodeFormat.lean` | frozen, reader added | 595 → 600 → 600 → 600 |
| `Complexity/TuringMachine/CodeSimulator.lean` | frozen, reader added | 9126 → 9133 → 9133 → 9133 |

The owned file imports the helper, so after #305 no facade edit is needed, and none was made. The helper imports
`Complexity/TuringMachine/CodeSimulator`, as the brief permits.

**The readers** (checkpoint 1; `pack-checks/readers.txt`). Each is a pure addition of one hunk, with no removed line.
Cutting the added lines out of the head file gives the base file byte for byte.
- In `CodeFormat.lean`, after `codeDecode_serialize_pad`:
  `Turing.oneTapeFormat_serialize_decode (xs : List Bool) : oneTapeFormat.serialize (oneTapeFormat.decode xs) =
  (codeDecode xs).serialize := rfl`.
- In `CodeSimulator.lean`, after `oneTapeMachineFormat`: `Turing.oneTapeMachineFormat_serialize_decode
  (α : List Bool) : oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) = oneTapeFormat.serialize
  (oneTapeFormat.decode α) := rfl`.

**The proof** follows the brief and the rewritten target sketch (REPORT § 1, review *Content*):
1. **The polynomial canonizer, read through the readers** (`Canonizer.exists_codeCanonizer`).
   `Turing.MachineFormat.exists_polyCanonizer` at `oneTapeMachineFormat` gives `C, d` with `C` computing
   `α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)` in time `n ↦ d · (n + 1)^d`, on every input.
   The two readers turn the function into `α ↦ (codeDecode α).serialize` (`hf ▸ hC`).
2. **The scheme and the bound** (`Canonizer.exists_effectiveMachineCode_canonizerTime_le`). The code is
   `⟨⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩, C, fun n => d * (n + 1) ^ d, hC⟩`. This is the effective
   part of `Turing.exists_uniformMachineCode`, with its time bound visible. Then **`d · (k+1)^d ≤ d · 2^{dk}`**:
   `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`), `(k + 1)^d ≤ (2^k)^d = 2^{dk}` (`Nat.pow_le_pow_left`, `pow_mul` after
   `mul_comm`), and `Nat.mul_le_mul_left d`.
3. **The target** (owned file): `obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le; exact
   ⟨c, d, d, h⟩`. `CanonizerExp` is the owned file's own definition, with `A = B = d`.

The edge cases: `k = 0` gives `d · 1^d ≤ d · 2^0`. With `d = 0` both sides are `0`. Malformed codes are covered
because `exists_polyCanonizer`'s time bound holds on every input, and `codeDecode` sends a malformed string to the
fallback machine. The axioms of `exists_polyCanonizer` are standard (its chain uses `computesFunInTime_appendBit`, not
the admitted `appendBitTM_computes`).

**Owned-file edits besides the proof.**
- The target's docstring is no longer "Open problem": it states `∃ c, CanonizerExp c` with its formula and a
  `[PS10, §2.13]` tag, and the superseded `Build/` sketch is replaced by the delivered proof. The brief requires this.
- The module docstring's status paragraph, `## Main results`, a new `## Contents` naming the helper, and one import.
- **C-F01:** six pre-existing lines over 100 characters were re-wrapped, whitespace only (ruling 4).

**Statements.** decls2 (public declarations, whitespace-normalized) from the issue base to the head gives **4 ADDED, 0
CHANGED, 0 REMOVED**: the two readers and the two helper theorems (review `statements/head-le/decls2-vs-base.tsv`;
`decls2-vs-worker.tsv`, empty).
- The frozen check (`frozencheck.py`; `landing/frozen-check.txt`) compares every declaration of the three
  pre-existing files: headers, statement prose and definition bodies.
  - `CodeFormat` 50 → 51 and `CodeSimulator` 208 → 209 have **0 differences**.
  - `Universal` 43 → 43 has **3**: the PROSE of `exists_canonizerExp`, which the brief requires; and the HEADER of
    `length_univArg` and of the private `exists_preimage_of_fUniversal_eq`, the C-F01 re-wrap.
  - The controls bite: `Universal` 3 → 4, `oneTapeFormat` body 0 → 1, `exists_polyCanonizer` header 0 → 1
    (`statements/frozen/control-*`).
- `statements/frozen/whitespace-check.txt`: outside the target, the module docstring and the import, the owned file
  is identical after collapsing whitespace (18 changed lines, all re-wraps).
- `touched`: 5 CHANGED. These are `exists_canonizerExp` (prose, sketch, proof) and four declarations changed in
  whitespace only: `length_univArg`, `exists_preimage_of_fUniversal_eq`, `invProbAt_reduction_ge` and
  `fUniversal_hard`.
- Re-checked for this pack from git objects (`pack-checks/headers.txt`, `whitespace.txt`, `readers.txt`, `decls2-*`):
  - decls2: 4 ADDED and 98 unchanged against both the issue base and `a334ec2e`; 0 rows for LE-doc `11b24a7e..6421ac16`.
  - The 50 `CodeFormat` and 208 `CodeSimulator` base declarations: header and docstring byte-identical, in order.
  - `Universal`: the 43 base declarations are in order. Exactly 2 headers differ in bytes, both equal after collapsing
    whitespace. The full text of exactly 4 declarations other than the target differs, each equal after collapsing
    whitespace. The owned file's lines over 100 go from 6 to 0.
  - `CanonizerExp`'s block, and the blocks of `oneTapeFormat`, `codeDecode` and `oneTapeMachineFormat`, are
    byte-identical.

## Rulings and records in force

1. **The pre-approved readers (Seyoon, 2026-11-14; `fills/canonizer/rulings/2026-11-14-readers.md`).** Exactly two
   `rfl` readers, with the statements quoted above. Each is proved by `rfl` in its own file and placed beside the
   definitions, with a formula docstring and no attribute, stated between `List Bool` values. The worker must still
   include the seal probe that shows each reader is needed.
   - **Anything else in a frozen file needed a scope request:** a different statement, a third reader, or a change to
     an existing declaration. None was sent (REPORT § 5).
   - Re-checked for this pack (`pack-checks/readers.txt`): each added declaration, whitespace-collapsed, is exactly
     `theorem <name> <binder> : <ruling statement> := rfl`. Each docstring contains the statement, there is no
     attribute, and each sits after the named definition. Nothing else in either file changed.
2. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`, present only in `Universal`'s closure. The coe-variant seals are canonical, and the
   strict variant is run and its differences attributed. **For this unit strict and coe agree in every seal row.** The
   strict *controls* differ only in `ctlCoeReader` (attributed, as sc-ot F-09).
3. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A**, which exempts it, is **canonical**; seal B
   is run and reported because the brief asks for both. `PolyExpr` is not in the readers' or the helper's closure, so
   for them A = B.
4. **C-F01, accepted as an LE-width-class change** (the review's disposition). The worker re-wrapped six pre-existing
   over-100 lines of the owned file, at base lines 192, 657, 720, 755, 895 and 896 (Python `len`; REPORT § 2 gives 200,
   661, 724, 759, 899 and 900, which are not the base line numbers). This changes the header bytes of
   `length_univArg` (`@[simp]`, public) and of the private `exists_preimage_of_fUniversal_eq`, and the proof bytes of
   `invProbAt_reduction_ge` and `fUniversal_hard`. The change is whitespace only, and it was disclosed (REPORT § 2).
   It is the class of the maintainer's LE-width landing edits.
5. **C-F02, closed by full-file seals.** Every whole-file `CodeSimulator` seal probe, head and base, and the worker's,
   stopped at Lean's default `maxErrors` of 100. That is probe line 3929 of 9311, with 101 errors in 48 declarations
   and no EOF record. The review reran with **`-DmaxErrors=0`** (`seal-full/`): the base has 177 errors in 58
   declarations and the head 177 in the same 58, with equal per-declaration counts. Both reach the EOF record
   (`G06-SEAL-END … requested=1232 verified=1232`). The reader is not among them, and the four variants' request sets
   are identical (`seal-full/request-sets.txt`). Future seal runners pass `-DmaxErrors=0` and check the EOF record.
6. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14).** The baseline is **92 FAIL / 101 WARN**
   for Cryptography; the final head has line sets identical to the tip (`lint/linediff-crypto.txt`). On Complexity
   (25 / 391) the head differs by exactly the three disclosed changes (`lint/linediff-complexity.txt`):
   - two check-8 WARN lines shortened, since `oneTapeFormat` and `oneTapeMachineFormat` now have a lemma beside them;
   - `CodeSimulator`'s pre-existing size WARN reads 9133 for 9126.
7. **LE-doc (the maintainer's landing edit): docstrings only.** `exists_codeCanonizer` gets its formula
   `∃ C d, C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d` (C-F03). Re-checked for
   this pack from git objects: `11b24a7e..6421ac16` touches `Canonizer.lean` only, identical with doc comments deleted,
   1 docstring changed, maximum width 97 (`pack-checks/lecheck.txt`).
8. **The landing edit is the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign, lamport, learning, prf-mac
   and sc-ot precedents).

## What is frozen

- **The target's statement** (quoted in the brief) and `CanonizerExp`. The other 42 pre-existing declarations of
  `Universal.lean` keep their statements and statement prose, in particular the conditional headlines. Only the C-F01
  whitespace changed in four of them (ruling 4).
- **`CodeFormat.lean` and `CodeSimulator.lean`:** every pre-existing declaration, and nothing beyond the two readers
  (ruling 1).
- **Every other file**, in particular `TuringMachine/Encoding.lean` (`EffectiveMachineCode`, `MachineCode`,
  `CodeTM.serialize`), `Diagonalization/EXPCOM.lean`, `MathlibBridge.lean`, `Games/Efficiency.lean` and the global
  simp attributes.
- **The landing edit:** LE-doc, one docstring.

## Questions for the audit

**1. Correctness against the frozen statement [PS10, §2.13]**
- Does `exists_canonizerExp` hold as stated, with `A = B = d`?
- Is **`d · (k+1)^d ≤ d · 2^{dk}`** proved correctly for every `k` and `d`, including **`k = 0`** and **`d = 0`**?
  Is `Nat.lt_two_pow_self` used at the right type (`k < 2^k` as `k + 1 ≤ 2^k`)? Is the `pow_mul` direction after
  `mul_comm` right?
- Is the constructed `EffectiveMachineCode` well formed: `decode_encode_pad` by `codeDecode_serialize_pad`, and
  `canonizer_computes` by the transported `hC`? Does its `canonizerTime` cover **malformed codes**, since
  `exists_polyCanonizer`'s bound holds on every input and `codeDecode` sends a malformed string to the fallback
  machine?
- Is `exists_codeCanonizer`'s transport `hf ▸ hC` along the two readers sound, and is `exists_polyCanonizer`'s
  specification `F.serialize (F.decode α)` at `F = oneTapeMachineFormat` the function `EffectiveMachineCode` requires
  (`(decode α).serialize` with `decode = codeDecode`, `serialize = CodeTM.serialize`)?
- Does the rewritten target docstring state the formula and describe the delivered proof? Are the module docstring's
  status lines and `## Main results` accurate? Are the conditional headlines unchanged and still conditional?

**2. The readers: exactly the pre-approved ones, nothing else in a frozen file**
- Are the two added declarations exactly the ruling's statements, each `rfl` beside its definition, with a formula
  docstring, no attribute and `List Bool` on both sides?
- Is everything else in `CodeFormat.lean` and `CodeSimulator.lean` unchanged: frozencheck 0 with biting controls,
  `pack-checks/readers.txt` (pure additions, the base file recovered byte for byte), and `pack-checks/headers.txt`?
- Is any other frozen file touched? The PR's 4 paths are the owned file, the helper and the two reader files
  (`pr.diff.txt`).

**3. The axiom closure**
- Does `exists_canonizerExp` avoid the admitted `Turing.FinTM.appendBitTM_computes`? The review's `DepTrace.lean`
  walks `getUsedConstantsAsSet` over values and types from the target: 8151 constants, containing
  `computesFunInTime_appendBit`, `exists_polyCanonizer` and both readers, and neither `appendBitTM_computes` nor
  `sorryAx` (`landing/deptrace-head.log`, `pack-checks/deptrace.txt`).
  - The target, `exists_polyCanonizer`, `computesFunInTime_appendBit` and the helper theorems print `[propext,
    Classical.choice, Quot.sound]`; `appendBitTM_computes` prints `sorryAx`.
  - Is that trace method sound for this purpose? Is there any path, for example through an instance or an auxiliary
    `_proof_` or matcher constant, by which the admitted lemma could enter without appearing in the closure?
- Census: 1077 stored constants in the 4 files (Universal 67, Canonizer 2, CodeFormat 122, CodeSimulator 886), axiom
  union the standard three, no `sorryAx`. Against the base: 1073 → 1077, 0 removed, 0 type or attribute changes, 1
  axiom change (the target; `logs/census-base-vs-head.tsv`).

**4. C-F01 as an LE-width-class acceptance (ruling 4)**
- Is the re-wrap whitespace only: the two header changes (`length_univArg`, `exists_preimage_of_fUniversal_eq`) and the
  four proof-line changes (`invProbAt_reduction_ge`, `fUniversal_hard`)? See `pack-checks/whitespace.txt`, which shows
  both header diffs in full, and `statements/frozen/whitespace-check.txt`.
- Could a whitespace change alter elaboration? Consider a line break inside `rw [...]`, an `exact_mod_cast (show …)`
  split onto its own line, and the `∃ x', …` split in a statement.
- Is accepting it as a width edit, rather than requiring the base bytes back, consistent with the frozen-statement rule
  as the campaign has applied it (LE-width)? If you disagree, the proposed fix is a revert of those lines, not a
  change of the proof.

**5. Rule 10**
- **Each reader needed and sufficient.**
  - Under the `Canonizer` helper's seal, the `rfl` forms of both reader statements (`ctlOneTapeFormat`,
    `ctlOneTapeMachineFormat`) each fail exactly once, while the same statements through the readers pass
    (`logs/ctlcheck.log`, `logs/controls-attribution.txt`).
  - Independently, the worker's checkpoint-1 probe (`worker/evidence/probes/ReaderNeed.lean`, `probe-cp1/*.out`) fails
    with exactly three errors per variant at the base, one per theorem: `need_codeFormat`, `need_codeSimulator`,
    `need_transport`.
  - Does this show that neither reader can be replaced by a published lemma, and that together they suffice?
- **The seals** (`logs/seal-table-seals{,-coe}.txt`, `logs/seal-attribution.txt`; requests coe A: `Universal` 2061,
  `Canonizer` 1340, `CodeFormat` 234, `CodeSimulator` 1232):
  - The new helper passes A and B, strict and coe.
  - `Universal` head = base in every variant: A has 10 errors in 4 declarations and B 12 in 6, all pre-existing;
    `exists_canonizerExp` is not among them.
  - `CodeFormat`: base 14 errors in 5 declarations, head 16 in 6. The only new failing declaration is the reader,
    attributed (C-F06) as a cascade of `oneTapeFormat`'s own base failure under the seal: its `rfl` fields unfold
    sealed `Encoding.lean` definitions, so `oneTapeFormat.Code` no longer reduces to `CodeTM`. Its siblings `codeDecode`
    and `codeDecode_serialize_pad` fail the same way at the base. Is that attribution right? Does the reader unfold
    only its own file's definitions, as the ruling prescribes?
  - `CodeSimulator`: the full-file `-DmaxErrors=0` seals (ruling 5), base = head with 177 errors in the same 58
    pre-existing declarations, both with the EOF record. Are they complete, and is the reader
    `oneTapeMachineFormat_serialize_decode` free of failure?
- **Controls** (coe, canonical): 14 probes and 16 sealed negatives, ALL_OK. The rows are `PolyExpr.eval` (B), the
  `FinDist` CoeFun instance, `Turing.unaryFin`, `Turing.oneTapeFormat` and `Turing.oneTapeMachineFormat`; the
  positives are published readers, and for the last two the pre-approved readers.
  - Strict: 16 probes and 21 negatives. Every negative fails exactly once; `ctlCoeReader` fails in the two strict
    sealed `Universal` probes, attributed.
- **Explicit-unfold scan** at r1 (`da08374d`; the 110-module closure is byte-identical at the head): 3256 items. There
  are 224 foreign items, all in untouched, byte-identical pre-existing declarations of `CodeFormat` (10) and
  `CodeSimulator` (214), and **0 in any touched declaration**: the readers, the target, the helper and the re-wrapped
  declarations (`logs/scan2-head.log`).
  - Does any touched proof read a foreign definition other than through a published reader? Consider `CanonizerExp`
    from the helper (it is not: the helper states its own bound), `EffectiveMachineCode`/`MachineCode` fields,
    `CodeTM.serialize`, `codeDecode`, and the formats.
  - Is the helper's `show d * (k + 1) ^ d ≤ d * 2 ^ (d * k)`, which reduces the projection `canonizerTime` of the
    helper's own structure literal, a permitted reduction (it passes every seal)?
- Were the seals, controls and scan, run at r1 `da08374d` (on `59c2c1fb`), rightly carried to the head?
  `pack-checks/rebase.txt`: range-diff 3/3 `=`, and all 110 modules of the unit's closure are byte-identical at
  `da08374d` and `6421ac16`.

**6. Duplication, and the docstring and sketch rules**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse` table? Recent gates graded undisclosed re-proofs of public lemmas as
  majors (G23-01, G24-01, G29-01, G29-02, prf-mac F-01, sc-ot F-01).
  - The disclosed relatives are `exists_uniformMachineCode` (the same scheme hidden behind `Nonempty`, whose proof
    unfolds the formats), `exists_effectiveMachineCode` and `exists_effectiveMachineCode2` (no time bound), and
    `codeCanonical_eq` (a different left-hand side). Are the "why not reused" reasons valid?
  - The review's C-F05 (note) lists two undisclosed near-relatives of the inline bound, neither a restatement:
    `Complexity.expPoly_poly` (`ClassNP/ExpPoly.lean:65`) and `succ_pow_le` (`ClassP/P.lean:88`). Also the private
    `expcom_decider_budget` and `codeCanonical_machine`/`CodeFormat.exists_canonizer`
    (`MathlibBridge.lean:1114,1123`). Is there a published `(k + 1)^d ≤ 2^{dk}`, `n + 1 ≤ 2^n`-power or
    `A · 2^{Bk}` bound lemma that the four-line inline proof re-proves?
  - Search in particular `pow_le_pow_left`, `lt_two_pow`, `two_pow`, `succ_pow`, `ExpPoly`, `canonizer`,
    `canonizerTime`, `ComputesFunInTime`, `codeDecode`, `serialize_decode`. The review's search is
    `evidence/logs/duplication-review.txt`; the worker's are `worker/evidence/logs/{checkpoint1,final}-searches.log`.
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a `[PS10, …]`
  tag where it comes from the source? After LE-doc the review's docaudit has 6 OK and 1 NO-FORMULA, which is
  `length_univArg`'s unchanged base prose.
- Does every proof of 15 lines or more carry a `**Proof sketch.**`? `statements/head-le/sketchaudit.txt` has 3
  theorems, 0 without. Is nothing new `@[simp]`, a `def`, an `abbrev` or an instance? The census has none. A misstated
  formula or sketch is a minor.

**7. The merge interaction**
- `git merge-tree --write-tree 6421ac16 <x>` is clean (`pack-checks/mergetrees.txt`). No path is shared with any of
  them, and the changed path sets of #319, #318 and (tip delta ∪ #313) are pairwise disjoint.

  | `<x>` | head | merged tree |
  |---|---|---|
  | the tip | `1321b9cb` | `8314d450` |
  | #313 | `94b31964` | `2b2cdcfa` |
  | #316 (merged) | `c18afbe6` | `246b0954` |
  | #317 (merged) | `590d1a56` | `da5c405e` |
  | #318 | `f62a25b3` | `e59d63a7` |
- **Downstream** (`pack-checks/downstream.txt`):
  - **The tip.** `Universal` has #316's `Foundations/BitLists` in its closure; the helper and the two machine-library
    files do not. In the merged tree, 6 modules are downstream of both: `Asymptotic/Universal`, `Asymptotic`,
    `Randomness/Derandomization`, `Randomness`, root `TCSlib` and `audits/pass-shelat/Checks`.
  - **#313.** It changes no module of the unit's 110-module closure; `Randomness` and `TCSlib` are downstream of
    both.
  - **#318.** It changes no module of the closure; only root `TCSlib` is downstream of both.
  - **The build.** Of the review's 191 built modules (`build-r3`, at this head, the full downstream of `CodeFormat`
    and `CodeSimulator`), 189 have the tip-merged source. The other two are #317's `MAC/FromPRF` and #316's
    `Lamport/MachineSpec`. `BitLists` itself was not rebuilt, since it is unchanged from `a334ec2e` to this head. All
    191 have #318's merged source, and 190 have #313's (`pack-checks/srcequality.txt`).
- **No name interaction:** none of the 4 new names is declared in a file the tip, #313, #316, #317 or #318 changed
  (`pack-checks/namecheck.txt`). The review's own check (`logs/open-pr-overlap.txt`, #313, #315 and sc-ot) predates
  #316 and #317.
- **Pending merge condition (not an audit item).** The combined trees are **not** built.
  - Because #316 and #317 merged after this branch's base, #319 needs an integration rebuild on the merged tip before
    it merges: the downstream of `BitLists`, `MachineSpec` and `MAC/FromPRF` together with the unit's downstream,
    which includes the full downstream of `CodeFormat` and `CodeSimulator`.
  - Whichever of #318 and #319 merges second needs the same.
  - The maintainer runs those builds. Treat them as conditions on the merge, not as something for this audit to
    establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **C-F03** (info): `exists_codeCanonizer` had no formula, fixed by LE-doc. **C-F04** (info): `COMMITS.tsv` hashes
  reproduce only with the environment's deterministic SSH signing (`logs/git-am-integrity*.log`), as sc-ot F-05.
  **C-F05** (note): the near-relatives of the inline bound (question 6). **C-F06** (info): the `CodeFormat` reader's
  seal failure, attributed (question 5). **C-F07** (info): the worker removed another fill's worktree and scratch on
  its own host, an environment matter on the worker's host.
- **Pre-existing seal failures** in `Universal` (A 10 in 4, B 12 in 6), `CodeFormat` (14 in 5) and `CodeSimulator`
  (177 in 58), and the 224 pre-existing foreign explicit unfolds in the two machine-library files, are base state,
  unchanged by this PR.
- **Pre-existing widths and sizes in the frozen files:** `CodeFormat` keeps 10 lines over 100 and `CodeSimulator` 1,
  and `CodeSimulator` is over 1000 lines at the base. The readers add no long line (`statements/base-widths.txt`,
  `statements/head-le/sizes-widths.txt`).
- **The probes ran at r1.** The seals, controls, scan, census and dependency trace ran at `da08374d` (on `59c2c1fb`,
  after #314). The rebase onto `a334ec2e` (#315) and the final build `build-r3` with the whole-tree check (1245
  modules, RESULT OK) came after. The unit's closure is unchanged (question 5).
- **Admissions:** the issued 19 in 9 modules become 18; only `Asymptotic/Universal` changes (1 → 0;
  `logs/sorry-census-r3.txt`). The build's sorry warnings are all in admitted base or base-delta modules.
- **The unit's one warning** is the base's `unused variable hc` in `fUniversal_hard`, in an untouched proof (base line
  797, now 805).
- **No promotion or reader requests** beyond the two readers (REPORT § 5).

## Also check

**Axioms:** see question 3. `oneTapeFormat_serialize_decode` prints `[propext, Quot.sound]` and
`oneTapeMachineFormat_serialize_decode` the standard three (worker `checkpoint1-axioms.log`, review census).

**Sizes and widths:** the owned file has 955 lines (at most 1000) and the helper 83; every line of both is at most 100
characters (`source-head.json`; review `statements/head-le/sizes-widths.txt`). The frozen files: see the dispositions.

**Build:** at the head `6421ac16`, the 191 modules have rc 0 and 0 errors in both diagnostic forms (G26-N1; substring
"error" 0). They are the downstream of every module changed since `eff2dcd0` (the base delta #303–#312, #314, #315 and
the unit), through root `TCSlib` and both `audits/*/Checks` (`landing/root-checks.jsonl`, whose last line is the
runner's `done` record; `landing/build-summary.txt`). The whole-tree check is at the head, 1245 modules, RESULT OK
(`landing/tree-check-head.txt`). The olean tree was restored to the base snapshot afterwards
(`restore/r3/snapshot-post.txt` = `tree/snapshot-pre.txt`, `457ba704…`; `restore/r3/tree-check-post.txt` RESULT OK).
Every built module's `source_sha256` equals the blob at `6421ac16` (`pack-checks/srcequality.txt`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (C-F01–C-F07).
- **`verification.zip`** (125 entries): every file the review cites and the pack uses, as byte-identical
  originals. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/canonizer/final-r1/`, SHA-256 `2b52982f…`) and `review-evidence-SHA256SUMS`, its
    manifest: 839 entries, all files, under `canonizer-r1/` exactly the 838 manifest paths plus that folder's
    `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers integrity, the readers against the
    ruling, the landing and LE-doc, the rebases, the builds (r1 and r3) and the whole-tree checks with the restore,
    decls2, the frozen check with its controls and the whitespace check, `touched`, the docstring and sketch audits,
    the census, axioms and the dependency trace, the strict and coe seals at the base and the head, the full-file
    `CodeSimulator` seals, the paired controls with the reader-need rows, the scan, the lint, sizes and the
    duplication review;
  - `landing/` (10): the review's extracts (`final-r1/landing/`), each a byte copy of a ZIP entry: `PROVENANCE.txt`,
    the commits, the series log, the LE-doc diff, message and doc-only check, the rebase log and the origin delta;
  - `records/` (14): the issue package `fills/canonizer/issued-r1/`, the readers ruling, the duplication ledger, the
    decision log and the #305 record (README and patch), at records `1321b9cb358867f5b51974b8c5d0781519a9cfdb`;
  - `evidence/` (60): byte copies of the ZIP entries this pack cites;
  - `worker/` (19): byte copies from exchange `27ae588db3952fb508f02184f9ea2adbb726cf6c` (`inbox/fills/canonizer/`).
    They are `patches/COMMITS.tsv`, the pre-approval record, the reader-need probe with its four sealed runs, both axiom
    prints, both searches, the census and both lint diffs, and the width, repro, seal-compare and scan-compare logs;
  - `pack-checks/` (18): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `27ae588db3952fb508f02184f9ea2adbb726cf6c`, under
  `inbox/fills/canonizer/`. Its top `SHA256SUMS` lists 169 files and `evidence/SHA256SUMS` 160, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `build-r3/results.jsonl`): the 191 modules, rc 0.
  - `build-summary.txt` (= `build-r3/summary.txt`).
  - `deptrace-head.log` (= `probe-runs/mods/PlProbe_DepTrace.log`): the axiom prints and the dependency trace.
  - `frozen-check.txt` (= `statements/frozen/frozen-check.txt`): the frozen check of the three pre-existing files.
  - `tree-check-head.txt` (= `tree/r3/tree-check-head.txt`): the whole-tree check at the head.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `27ae588d`.
- **`pr-description.md`:** the PR #319 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (4 paths, 133 insertions, 28 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 4 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 110 files.
- **The bundle** adds, as context at the head:
  - `TuringMachine/Encoding.lean` (`MachineCode`, `EffectiveMachineCode`, `CodeTM.serialize`);
  - `Diagonalization/EXPCOM.lean` (`exists_uniformMachineCode`, the nearest relative).

  `CodeSimulator.lean` (474 KB) is not bundled. Its one hunk is in `pr.diff.txt`, the whole file is in `sources.zip`,
  and `exists_polyCanonizer` is at its line 8371.

## Findings delivery

Return `gate35-canonizer-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation (including any frozen-file change beyond the two pre-approved readers).
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one, an axiom closure that reaches an admitted
  lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
