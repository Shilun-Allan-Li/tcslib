## ===== briefs/pass-shelat-ch5-8/gates/35-canonizer/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/35-canonizer/review.md =====

# canonizer · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edit is LE-doc, one formula docstring. Draft [PR #319](https://github.com/Shilun-Allan-Li/tcslib/pull/319).

## Delivery and landing branch
- **Delivery.** A Claude worker proved `exists_canonizerExp` (`Asymptotic/Universal.lean`), using the two `rfl` readers that Seyoon pre-approved on 2026-11-14. The exchange is at `27ae588d` and the issue base is `107f1e8c`.
- **Landing.** `land/pass-shelat-canonizer`, head `6421ac1631ef08feed297c810f0839b178d2a2bb`, tree `3e16398e`. It was rebased r1 → r3 onto `a334ec2e`; the range-diffs are identical.
  - **Commits.** `523d98cc` (the readers), `11b24a7e` (the proof) and `6421ac16` (LE-doc). All are signed.
- **Files.** 4 files, +133/−28: `CodeFormat.lean` and `CodeSimulator.lean`, one reader each; `Universal.lean`; and the new `Universal/Canonizer.lean`.
- **Evidence.** `review-evidence.zip`, SHA-256 `2b52982fd2699afa5ad38ff4ee1eb4172bbd16396619df2674f6e2c1348c00ea`. It has 839 entries.

## Checks
- **Integrity.** The manifests verify 169/169 and 160/160. The package verifies 7/7 and its sources 183/183. `git am` reproduces both hashes, but only with signing on.
- **Readers.** There are exactly the two approved ones. Each is a pure addition with the approved statement, proved by `rfl` and placed beside its definition. Each has a formula docstring, no attribute, and `List Bool` on both sides. The frozen check finds 0 other differences in `CodeFormat` and `CodeSimulator`.
- **Build.** The final r3 build covers 191 modules, rc 0 and 0 errors: the full downstream of `CodeFormat` and `CodeSimulator`, through `TCSlib` and both `audits/*/Checks`. The whole-tree check covers 1245 modules: OK.
- **Statements.** decls2 gives 4 ADDED and 0 CHANGED. The frozen check finds only the target's prose, which the brief requires, and the C-F01 whitespace. `Universal.lean` has 955 lines.
- **Axioms.** `exists_canonizerExp` uses only the standard three, and so do all 1077 stored constants. Its dependency closure (8151 constants) contains `computesFunInTime_appendBit`, `exists_polyCanonizer` and both readers. It contains neither the admitted `appendBitTM_computes` nor `sorryAx`.
- **Rule 10.**
  - The new helper passes every seal variant. `Universal` fails exactly as it does at the base. `CodeFormat`'s only new failure is the reader (C-F06), and `CodeSimulator`'s full file equals the base (C-F02).
  - Under the helper's seal, the `rfl` forms of both reader statements fail exactly once while the readers pass. So each reader is needed and sufficient.
  - The scan finds 0 foreign definitions in the touched declarations.
- **Admissions.** 19 → 18.
- **Lint.** Cryptography 92/101, unchanged. Complexity 25/391, which differs by exactly the three disclosed changes.
- **Content.** The target is `⟨c, d, d, h⟩`. The helper transports `exists_polyCanonizer` along the readers and proves `d(k+1)^d ≤ d·2^{dk}`. The edge cases `k = 0`, `d = 0` and malformed codes are covered.
- **Overlap.** No open PR touches a unit file. The trial merges with #313 and with sc-ot are clean.
- **Restore.** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| C-F01 | minor, disclosed | Six pre-existing lines over 100 characters were re-wrapped. This changes the header bytes of `length_univArg` and of the private `exists_preimage_of_fUniversal_eq`. The change is whitespace only. | Accepted as an LE-width-class change. |
| C-F02 | info | The whole-file `CodeSimulator` seals stopped at Lean's default `maxErrors` of 100. | Closed: full runs with `-DmaxErrors=0` give 177 errors in the same 58 pre-existing declarations at both the base and the head. Future seal runners pass `-DmaxErrors=0` and check the EOF record. |
| C-F03 | info | `exists_codeCanonizer` had no formula docstring. | **Fixed** by LE-doc. |
| C-F04 | info | Signing is not recorded in `COMMITS.tsv`. | As sc-ot F-05. |
| C-F05 | info | The inline bound has near-relatives that were not disclosed, `expPoly_poly` and `succ_pow_le`; neither is a restatement. | Note. |
| C-F06 | info | When sealed, the new `CodeFormat` reader fails as a cascade of `oneTapeFormat`'s `rfl` fields. Its siblings fail the same way at the base. | Attributed. |
| C-F07 | info | The worker removed another fill's worktree on its own host. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/35-canonizer/worker-report.md =====

# Fill canonizer — final

**Unit** `canonizer` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/canonizer` (local), head `ba7096e8e` ·
**Lean** 4.25.0, Mathlib at the base's manifest.

## 0. Status

| Target | Status |
|---|---|
| `TCSlib.Cryptography.exists_canonizerExp` | **proved**; statement unchanged; axioms `[propext, Classical.choice, Quot.sound]` |

Commits (the series in `patches/`, with `patches/COMMITS.tsv`):
1. `7064488ba` checkpoint 1 — the two `rfl` readers (pre-approved scope; exchange `3d65c2466`);
2. `ba7096e8e` `exists_canonizerExp` proved.

The headlines of `Universal.lean` (`fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay`,
`theorem_63_1`) are unchanged and still take `CanonizerExp c` as a hypothesis; now the hypothesis
is known to be satisfiable. The final sweep of the supplied order with the helper inserted before
the owned module has 0 errors, and the sorry census is `base-sorries.txt` minus
`exists_canonizerExp` (§6).

## 1. The proof

- **The readers (checkpoint 1).** `Turing.MachineFormat.exists_polyCanonizer` at
  `Turing.oneTapeMachineFormat` gives `C, d` with `C` computing
  `α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)` in time `n ↦ d · (n + 1)^d`
  on every input. The two pre-approved readers turn that function into
  `α ↦ (codeDecode α).serialize` (`oneTapeMachineFormat_serialize_decode`, then
  `oneTapeFormat_serialize_decode`); without them this step needs unfolding `oneTapeMachineFormat`,
  `oneTapeFormat` and `codeDecode` (the seal probe, §8.2).
- **The helper** (`TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean`, 82 lines):
  `exists_codeCanonizer` (the transported canonizer) and
  `exists_effectiveMachineCode_canonizerTime_le`: the effective machine code
  `⟨⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩, C, fun n => d · (n + 1)^d, hC⟩` (the
  scheme of `Turing.exists_uniformMachineCode`, with its time bound visible), and
  `d · (k + 1)^d ≤ d · 2^{d k}` from `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`), `pow_mul` and
  `Nat.pow_le_pow_left`.
- **The target** (owned file): `obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le;
  exact ⟨c, d, d, h⟩` (`CanonizerExp` is the owned file's own definition, `A = B = d`).

**Edge cases.** `k = 0`: `d · 1^d ≤ d · 1`. `d = 0`: both sides are `0`. Malformed codes: the time
bound of `exists_polyCanonizer` holds on every input, and `codeDecode` sends a malformed string to
the fallback machine, whose serialization is the canonizer's output. The axioms of
`exists_polyCanonizer` are standard (`[propext, Classical.choice, Quot.sound]`; the chain uses
`FinTM.computesFunInTime_appendBit`, not the admitted `appendBitTM_computes`, as the brief's text
trace expected — confirmed by the print, `logs/checkpoint1-axioms.log`, `logs/final-axioms.log`).

## 2. Changed and new files

| File | Lines (base) | Change |
|---|---|---|
| `TCSlib/Cryptography/Asymptotic/Universal.lean` (owned) | 955 (945) | the proof; docstrings; import; six pre-existing long lines wrapped |
| `TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean` (new) | 82 | the helper |
| `TCSlib/Complexity/TuringMachine/CodeFormat.lean` (frozen, pre-approved) | 600 (595) | reader `oneTapeFormat_serialize_decode` |
| `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` (frozen, pre-approved) | 9133 (9126) | reader `oneTapeMachineFormat_serialize_decode` |

**Owned-file edits.** The module title has no "(statement phase)" at the base (unchanged). The
encoding-deviation paragraph now ends: some scheme satisfies the hypothesis
(`exists_canonizerExp`, proved from `exists_polyCanonizer`), so the conditional headlines apply to
it. `## Main results`: `exists_canonizerExp` — some scheme satisfies `CanonizerExp` (proved,
run-3 audit P3-4 closed). New `## Contents` naming the helper. The target's docstring is no longer
"Open problem": it states `∃ c, CanonizerExp c` with its formula and a `[PS10, §2.13]` tag, and the
superseded `Build/` sketch is replaced by the delivered proof (the brief: "The docstring's sketch is
superseded"). One import (`Universal.Canonizer`). Six pre-existing lines over 100 characters
(lines 200, 661, 724, 759, 899, 900 of the base) were wrapped, whitespace only, so that every line
of the owned file is within 100 characters (`logs/final-width.log`); no declaration, statement or
proof step changed. The conditional headlines, every other declaration, the statement prose and
the simp attributes are unchanged.

## 3. New declarations

- `TCSlib.Cryptography.exists_codeCanonizer` (helper): `∃ (C : FinTM Bool) (d : ℕ),
  C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`.
- `TCSlib.Cryptography.exists_effectiveMachineCode_canonizerTime_le` (helper):
  `∃ (c : EffectiveMachineCode) (d : ℕ), ∀ k, c.canonizerTime k ≤ d * 2 ^ (d * k)`.
- `Turing.oneTapeFormat_serialize_decode` (`CodeFormat.lean`) and
  `Turing.oneTapeMachineFormat_serialize_decode` (`CodeSimulator.lean`): the two readers.

Each has a formula docstring; no `@[simp]`, no new `def` or `abbrev`.

## 4. Overlap and reuse

| New declaration | Nearest relative (`path:line`) | Relation | Why not reused |
|---|---|---|---|
| `exists_effectiveMachineCode_canonizerTime_le` | `Turing.exists_uniformMachineCode` (`Complexity/Diagonalization/EXPCOM.lean:156`) | the same effective part (`CodeTM.serialize`, `codeDecode`, `codeDecode_serialize_pad`, the polynomial canonizer, `canonizerTime n = d (n+1)^d`) | it is stated as `Nonempty UniformMachineCode`, which hides the time bound; and its proof matches the canonizer's type by unfolding `oneTapeMachineFormat`/`oneTapeFormat`/`codeDecode` (Rule 10). The construction is repeated through the readers, with the bound exported |
| same | `Turing.exists_effectiveMachineCode` (`Complexity/TuringMachine/MathlibBridge.lean:1162`), `exists_effectiveMachineCode2` (`Codes2Tape.lean`) | other effective codes | no time bound on their canonizers |
| `exists_codeCanonizer` | `Turing.MachineFormat.exists_polyCanonizer` (`CodeSimulator.lean:8364` at the base) | its specialization at `oneTapeMachineFormat`, read through the readers | reused, not re-proved |
| `oneTapeFormat_serialize_decode` | `Turing.codeCanonical_eq` (`CodeFormat.lean:592`) | `codeCanonical xs = (codeDecode xs).serialize`; another reading of the same canonical serialization | relates `codeCanonical`, not `oneTapeFormat.serialize ∘ oneTapeFormat.decode` |
| `oneTapeMachineFormat_serialize_decode` | none | the `MachineFormat` view of `oneTapeFormat` | no lemma relates the two structures' projections |
| (inline) `(k + 1)^d ≤ 2^{d k}` | Mathlib `Nat.lt_two_pow_self`, `Nat.pow_le_pow_left`, `pow_mul` | a three-step consequence | no stated lemma found; kept inline |

Searches: `logs/checkpoint1-searches.log` (the readers' statement shapes and names,
`exists_polyCanonizer`, `canonizerTime :=`, `CanonizerExp`) and `logs/final-searches.log` (the
helper's statement shapes, the scheme literal, `(k + 1)^d ≤ 2^…`, Mathlib's power lemmas).

## 5. Scope requests, promotion and reader requests

**Scope requests:** none sent. The two readers are Seyoon's pre-approval of 2026-11-14 (verbatim in
`evidence/scope-request/pre-approval.md`), delivered exactly as approved: `rfl`, beside their
definitions, formula docstrings, no attribute. No other frozen file was touched.

**Promotion requests:** none (the helper's two theorems are specific to this file's hypothesis).

**Reader requests:** none beyond the two pre-approved readers.

## 6. Checks (final)

All Lean runs one process at a time, one module per `scripts/lean_check_tree.sh` call (via
`tools/check.sh`); post-sweep runs by `tools/final_pipeline.sh` (step log
`logs/final-pipeline.log`). No host restart during the runs.

- **Recheck and sweep** (`logs/final-sweep.log`, 03:09–03:25 UTC): the 184 modules of
  `logs/order-with-helpers.txt` (`order.txt` with the helper inserted before the owned module),
  each checked from scratch, in order: **184/184 status 0, no `error:`/`error(…)` line**. The only
  warning in the changed files is the base's `unused variable hc` in `fUniversal_hard` (line 797 at
  the base, 805 now).
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 18 declarations in
  8 modules; the diff against `base-sorries.txt` is exactly
  `TCSlib/Cryptography/Asymptotic/Universal: 1: exists_canonizerExp` and the total (19 → 18).
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `exists_canonizerExp` depends on
  `[propext, Classical.choice, Quot.sound]`. All **1077 stored constants** of the four changed and
  new modules (Universal 67, Universal.Canonizer 2, CodeFormat 122, CodeSimulator 886; auxiliary
  constants included) use only `{Classical.choice, Quot.sound, propext}`; no `sorryAx`.
- **Whole-file seals** (`seals/`; `tools/seal_gen.py`, `seal_run.py`, `seal_all.sh`; variants
  **A**/**B** = `PolyExpr.eval` excluded/sealed, each **strict**/**coe** = projection coercions
  sealed/notation; the runner counts `error:` and `error(…)` and keeps every raw `.out`):
  - **the helper** `Universal/Canonizer.lean`: 0 errors in all four variants;
  - **the owned file** `Universal.lean`: final = base in every variant (A: 10 errors in
    `clockedAnswer_eq_cons_of_computesInTime`, `clockedAnswer_eq_false_of_not_computesInTime`,
    `invProbAt_reduction_ge`, `ofFn_getD_eq_take`; B adds `eval_univOutLen`, `fUniversal_hard`:
    12). All are pre-existing; **the new proof of `exists_canonizerExp` does not fail**;
  - **CodeSimulator.lean**: final = base in every variant (101 errors in 48 pre-existing
    declarations, listed in `seals/seals-compare.log`); the reader
    `oneTapeMachineFormat_serialize_decode` is not among them;
  - **CodeFormat.lean**: base 14 errors in `codeActionK_length`, `codeCanonical_eq`, `codeDecode`,
    `codeDecode_serialize_pad`, `oneTapeFormat`; final 16, the two new errors in the reader
    `oneTapeFormat_serialize_decode`. **Attribution:** a cascade of the pre-existing failure of
    `oneTapeFormat` itself under the seal (its field `serialize_assemble := … rfl` unfolds the
    foreign `CodeTM.serialize`, `Encoding.lean`); with `oneTapeFormat` broken, its own readers
    `codeDecode` and `codeDecode_serialize_pad` fail at the base exactly as the new reader does
    (`Type mismatch: oneTapeFormat.decode xs has type oneTapeFormat.Code but is expected to have
    type CodeTM`). The reader unfolds only its own file's definitions (`oneTapeFormat`,
    `CodeFormat.decode`, `codeDecode`), as Rule 10 allows beside a definition;
  - strict and coe agree in A and in B (`seals-compare.log`, last two sections).
  Base copies of the three files that exist at the base are in `base/` (sha256 equal to
  `SOURCE-SHA256SUMS`); every checked sealed copy is in `seals/sources/<tag>/`.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  `CtlUnfold` (`codeDecode xs = oneTapeFormat.decode xs := rfl`): unsealed 0, **1 error in each
  sealed variant**; `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0, A 0, **B 1**;
  `CtlReader` (the two readers and `PolyExpr.eval_const`): 0 everywhere; `CtlCoe` (an explicit
  application of the projection coercion `FinDist.instCoeFunForallReal` by `rfl`): 0 everywhere, a
  documented probe, not a negative control: Lean reduces a projection of an instance even when the
  strict seal makes the instance irreducible, so no control can make the strict variant fail on a
  projection coercion. Each sealed negative fails exactly once; the positive passes.
- **Explicit-unfold scan** (`scan/`): Universal 90 rows, 0 foreign definitions (base the same);
  Canonizer 2 rows, both theorems (the readers); CodeFormat 6 and CodeSimulator 35 explicit unfolds
  of foreign definitions, **all pre-existing** (the same sets at the base: `scan/scan-compare.log`,
  "NEW foreign explicit unfolds: 0").
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  `campaign_style_lint.py TCSlib/Cryptography --check8b`: 92 FAIL / 101 WARN at the base and at the
  final, **identical FAIL and WARN line sets**. On `TCSlib/Complexity/TuringMachine` (the frozen
  files' directory; `logs/base-lint-turingmachine.log`, `logs/final-lint-turingmachine.log`,
  `logs/final-lint-turingmachine-vs-base.diff`): the readers remove `oneTapeFormat` and
  `oneTapeMachineFormat` from the check-8 WARN lines, and CodeSimulator's size WARN reads 9133
  instead of 9126 lines (pre-existing, disclosed: the file is over 1000 lines at the base); no new
  FAIL or WARN line.
- **Width and size** (`logs/final-width.log`): the owned file and the helper have every line within
  100 characters and are within 1000 lines; the frozen files' added lines are within 100
  characters (their pre-existing long lines and CodeSimulator's size are reported, not changed).
- **Patch reproduction** (`logs/final-repro.log`): `git am` of each patch at the base in a scratch
  clone, with the committer data of `patches/COMMITS.tsv`, reproduces both hashes.

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/`; the top-level `SHA256SUMS` lists
every delivered file under `inbox/fills/canonizer/` except itself (both verified by
`tools/manifest.sh` before the push).
- `logs/`: environment and bootstrap (`preflight.log`, `source-sha256.log`, `order.txt`,
  `mathlib-roots.txt`, `cache-store.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`,
  `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`, `base-lint.log`,
  `base-lint-turingmachine.log`); checkpoint 1 (`cp1-probe-plain.log`, `checkpoint1-*.log`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-lint-turingmachine.log`,
  `final-lint-turingmachine-vs-base.diff`, `final-width.log`, `final-searches.log`,
  `final-pipeline.log`, `controls-plain.log`, `scan-final.ids.log`, `scan-final.raw.log`,
  `scan-base.ids.log`, `scan-base.raw.log`, `final-repro.log`).
- `probe-cp1/`: the checkpoint-1 seal probe runs and their sealed copies.
- `seals/`: `{final,base,controls}-{A,B}-{strict,coe}.jsonl` and `.out`, `seals-compare.log`,
  `sources/<tag>/`.
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/{final,base}/`.
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlCoe.lean`, `CtlReader.lean`.
- `base/`: `UniversalBase.lean`, `CodeFormatBase.lean`, `CodeSimulatorBase.lean` (the changed files
  at the base).
- `probes/`: `CacheProbe.lean`, `ReaderNeed.lean`, `AxiomsCP1.lean`, `AxiomsFinal.lean`.
- `scope-request/pre-approval.md`.
- `tools/`: every script used.

`patches/`: `git format-patch 107f1e8c..ba7096e8e` (2 patches) and `COMMITS.tsv`; `src/`: the four
changed and new files at `ba7096e8e`.

## 8. From checkpoint 1

### 8.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom
  is `MemAvailable` = 16491368448 B = 15.36 GiB; the clone's filesystem (ext4, `/dev/vda`) has
  16523374592 B = 15.39 GiB free (floor 12 GiB): `PREFLIGHT PASS`. To get there, the git worktree
  of this host's delivered `learning` fill (`/workspace/learn`, branch kept) and that fill's own
  scratch directories (`/tmp/learn-repro`, a patch-reproduction clone; `/tmp/lintbase`) were
  removed. No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/canon` of the local repository, branch `fill/canonizer` at
  the issue base; its sources match `SOURCE-SHA256SUMS` (183 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) held 2402 archives from this host's
  earlier fills. The narrowed `lake exe cache get` for the 80 roots (`mathlib-roots.txt`, the same
  list as `roots.txt`) downloaded 1 file, decompressed 2123 and exited 0 (`cache-get.log`). No
  zero-size olean; the probe importing `Mathlib.Algebra.BigOperators.Field` elaborates
  (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`): the 183 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`), in order: 183/183 status 0, no error, no host restart.
  Sorry census = `base-sorries.txt` (19 declarations in 9 modules; `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`: identical).

### 8.2 The readers and the seal probe

Seyoon's pre-approval (2026-11-14) is recorded verbatim in `evidence/scope-request/pre-approval.md`.
Exactly the two approved readers were added, each `rfl` beside its definition, with a formula
docstring and no attribute, stated between `List Bool` values:

- `TCSlib/Complexity/TuringMachine/CodeFormat.lean` (595 → 600 lines), after
  `codeDecode_serialize_pad`: `Turing.oneTapeFormat_serialize_decode (xs : List Bool) :
  oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl`.
- `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` (9126 → 9133 lines), after
  `oneTapeMachineFormat`: `Turing.oneTapeMachineFormat_serialize_decode (α : List Bool) :
  oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
  oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl`.

**The seal probe** (`probes/ReaderNeed.lean`, run at the base, before the readers existed):
three theorems closed by unfolding, which is how `Turing.exists_uniformMachineCode`
(`Diagonalization/EXPCOM.lean:156`) matches the canonizer's type:
`need_codeFormat` (the first reader's statement, by `rfl`), `need_codeSimulator` (the second's) and
`need_transport` (`exists_polyCanonizer`'s specification read as `α ↦ (codeDecode α).serialize`).
Unsealed the probe elaborates (`logs/cp1-probe-plain.log`, status 0). Under the whole-closure seal
in all four variants (A/B × strict/coe; `probe-cp1/probe-{As,Ac,Bs,Bc}.jsonl` and `.out`, sealed
copies in `probe-cp1/sources/`) it fails with **exactly three errors, one per theorem**
(`need_codeFormat`, `need_codeSimulator`, `need_transport`). So neither reader can be replaced by a
published lemma (none relates the two formats' serializations to `codeDecode`; searches in
`logs/checkpoint1-searches.log`), and each is needed: the first unfolds `oneTapeFormat` (and
`codeDecode`) of `CodeFormat.lean`, the second `oneTapeMachineFormat` of `CodeSimulator.lean`.
(The `PolyExpr.eval` exclusion is vacuous here: `PolyExpr` is not in this closure.)

Checks: `logs/checkpoint1-checks.log` (both files rechecked, status 0, no warning);
`logs/checkpoint1-axioms.log` (`probes/AxiomsCP1.lean`): the readers depend on standard axioms only
(`oneTapeFormat_serialize_decode`: `[propext, Quot.sound]`; `oneTapeMachineFormat_serialize_decode`:
`[propext, Classical.choice, Quot.sound]`), and so does `Turing.MachineFormat.exists_polyCanonizer`
(`[propext, Classical.choice, Quot.sound]`; the chain is standard, as the brief's text trace
expected).

**Width and size** (`logs/checkpoint1-width.log`): the added lines are all within 100 characters.
Both frozen files have pre-existing long lines (CodeFormat: 10 lines over 100 at the base;
CodeSimulator: 1), and CodeSimulator is over 1000 lines at the base (9126); the readers add 5 and
7 lines and no long line.

**Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` at the base: 92 FAIL / 101 WARN
(`logs/base-lint.log`); this checkpoint changes no file under `TCSlib/Cryptography`. On the frozen
files' directory, `TCSlib/Complexity/TuringMachine` (`logs/base-lint-turingmachine.log`,
`logs/checkpoint1-lint-turingmachine.log`): the readers remove `oneTapeFormat` and
`oneTapeMachineFormat` from the check-8 WARN lines ("public def without a lemma beside it"), and
the size WARN of CodeSimulator now reads 9133 lines instead of 9126; no other line changes.


## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/fills/canonizer/issued-r1/brief.md =====

# Claude fill · some effective machine code has an exponential canonizer (`exists_canonizerExp`)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `canonizer`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `exists_canonizerExp` of [PS10, §2.13] (run-3 audit P3-4; DESIGN D11) in
`TCSlib/Cryptography/Asymptotic/Universal.lean`. The statement passed the ch. 2–4 run-3 audit (P3-4, recorded as an open problem) and Gate 03h,
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible and small, but Rule 10 almost certainly needs readers in two frozen machine-library files (`CodeFormat.lean` and `CodeSimulator.lean`, the latter 9,126 lines). Seyoon can approve them at dispatch, or the maintainer can land them by PR first. A text-level trace finds that `exists_polyCanonizer`'s chain uses `FinTM.computesFunInTime_appendBit`, which is proved directly and does not use the admitted `appendBitTM_computes`. The worker's axiom print must confirm that the chain is standard.

**Estimated size:** 40–150 lines in one helper module, plus two one-line readers if Seyoon approves them. `Universal.lean` is at 945 lines and must stay at most 1000.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/canonizer` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/canonizer/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/canonizer/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill canonizer: checkpoint N` and `fill canonizer: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `seq-zk`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem exists_canonizerExp : ∃ c : EffectiveMachineCode, CanonizerExp c := by
  sorry
```

It lives in namespace `TCSlib.Cryptography`. `CanonizerExp c` (owned, a `def`) is `∃ A B : ℕ, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)`. The headlines of
the file (`fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay`, `theorem_63_1`) take it as a hypothesis
and stay conditional; no declaration consumes the target. `EffectiveMachineCode` (`TuringMachine/Encoding.lean`)
extends `MachineCode` (`encode`, `decode`, `decode_encode_pad`) by `canonizer`, `canonizerTime` and
`canonizer_computes : canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime`.

**What the records say.** The target was recorded as an open problem: DESIGN §1 D11 and §7, the ch. 2–4 plan,
Gate 03h ("is it true?"), Gate 11 (out of scope), and the 2026-11-10 proof-prerequisites check ("needs a
quantitative bound for every input, including malformed codes"). Since then the machine library has proved
`Turing.MachineFormat.exists_polyCanonizer` (`TuringMachine/CodeSimulator.lean:8364`, "proved, with no
admission"; time `d · (n + 1)^d` on every input). `Turing.exists_uniformMachineCode`
(`Diagonalization/EXPCOM.lean:156`) already builds the needed scheme from it: `encode := CodeTM.serialize`,
`decode := codeDecode`, `codeDecode_serialize_pad`, `canonizerTime := fun n => dC * (n + 1) ^ dC`. So the target
is true, and the proof is short.

**The docstring's sketch is superseded.** It proposes building a parse-and-reserialize canonizer from the
`Build/` combinators. That machine now exists (`exists_polyCanonizer`); building it again would duplicate it.
Use the existing canonizer and rewrite the sketch to match.

## Published interfaces

| Interface | Provider |
|---|---|
| `CanonizerExp` (own definition), `exists_univCoeff_le` (its consumer pattern) | owned file |
| `EffectiveMachineCode`, `MachineCode`, `CodeTM.serialize` | `Complexity/TuringMachine/Encoding.lean` |
| `codeDecode`, `codeDecode_serialize_pad`, `oneTapeFormat` | `Complexity/TuringMachine/CodeFormat.lean` |
| `MachineFormat.exists_polyCanonizer`, `oneTapeMachineFormat` | `Complexity/TuringMachine/CodeSimulator.lean` |
| `n < 2 ^ n`, monotonicity of `pow`, `pow_mul` (search for the exact names) | Mathlib |

## Proof route and checkpoints

1. **Checkpoint 1 · the readers (expect a scope request).** The EXPCOM proof matches the canonizer's type by unfolding `oneTapeMachineFormat` (CodeSimulator) and `oneTapeFormat` and `codeDecode` (CodeFormat), which Rule 10 forbids a consumer. No published lemma relates `oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)` to `(codeDecode α).serialize`. Confirm this with a seal probe. Then ask Seyoon for the minimal `rfl` readers beside the definitions. The maintainer expects two, each stated between `List Bool` values so that no sealed `Code` type has to reduce: in `CodeFormat.lean` (595 lines), `oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`; in `CodeSimulator.lean`, `oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) = oneTapeFormat.serialize (oneTapeFormat.decode α)`. Each is `rfl` in its own file and needs a formula docstring. Include the probe and the request. Send this checkpoint.
2. **Final · the scheme and the bound.** In a helper module, take `C, d` from `oneTapeMachineFormat.exists_polyCanonizer`, transport its specification along the readers, and build the `EffectiveMachineCode` with `codeDecode`, `CodeTM.serialize`, `codeDecode_serialize_pad`, `C` and `canonizerTime n = d · (n + 1)^d`. Prove `d · (k + 1)^d ≤ d · 2^{d k}` from `k + 1 ≤ 2^k`. The target is then `⟨c, d, d, h⟩` (reading `CanonizerExp`, the owned file's own definition). Update the target's docstring (no longer an open problem), the module docstring's status lines and `## Main results`, without changing the conditional headlines.

Check the edge cases: `k = 0`; `d = 0`; malformed codes (covered by `exists_polyCanonizer`'s bound on every input); the axioms of `exists_polyCanonizer`.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Asymptotic/Universal.lean` (945 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Asymptotic/Universal/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `TCSlib/Complexity/TuringMachine/CodeSimulator`. It is not downstream of the owned file (checked at the issue base); it adds 21 modules to the closure, all in the order below.
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** `Turing.exists_uniformMachineCode` (`Diagonalization/EXPCOM.lean:156`, whose effective part is the same construction but hidden behind `Nonempty`, so it cannot be reused for the bound), `Turing.exists_effectiveMachineCode` (`MathlibBridge.lean:1162`, no time bound) and `exists_effectiveMachineCode2` (`Codes2Tape.lean`).
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (183 modules) and the narrow `roots.txt` (80), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (19 declarations in 9 modules). The only change
    must be the removal of `exists_canonizerExp`.
- **Axioms.**
  - Print the axioms of `exists_canonizerExp`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/fills/canonizer/rulings/2026-11-14-readers.md =====

# canonizer · pre-approved scope exception (Seyoon, 2026-11-14)

Seyoon pre-approved exactly the two `rfl` readers named in the brief's checkpoint 1. The worker does not need to
send a scope request for them.

1. In `TCSlib/Complexity/TuringMachine/CodeFormat.lean`:
   `oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`.
2. In `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`:
   `oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) = oneTapeFormat.serialize (oneTapeFormat.decode α)`.

Requirements for both readers:
- Each is proved by `rfl` in its own file and placed beside the definitions.
- Each carries a formula docstring and no attribute.
- Each is stated between `List Bool` values.

The worker must still include the seal probe that shows each reader is needed.

Any other change to a frozen file still needs a scope request. That includes a different statement, a third
reader, or any change to an existing declaration.

## ===== briefs/pass-shelat-ch5-8/fills/canonizer/final-r1/landing/PROVENANCE.txt =====

canonizer (PS10 §2.13, run-3 audit P3-4: exists_canonizerExp) maintainer delivery review r1, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: as the sc-ot-r1 review (../sc-ot-r1/PROVENANCE.txt), run after it on the same tree; tools copied from sc-ot-r1/tools
  (changes under "tools"). Nothing pushed, no PR opened, the records checkout only read. No lake build, no cache get. python3 -I
  throughout. One Lean process at a time, only on $SP/dl-oleans; dl-oleans-2 never touched.

brief: briefs/pass-shelat-ch5-8/fills/canonizer/issued-r1/brief.md, SHA-256 505b3eb669f9bb31db5841d08bdfa3805951d2252546182825e16c042d146fb7
  (= dispatch.md's "Brief SHA-256"; logs/brief.md). Issue package SHA256SUMS 7/7 OK (logs/issue-package-check.txt);
  SOURCE-SHA256SUMS 183/183 OK at the issue base 107f1e8c218733eac12d6b9bee6fece441271317 (logs/source-sums-check.txt). Issued
  admissions 19 in 9 modules. Ruling: fills/canonizer/rulings/2026-11-14-readers.md (logs/ruling-2026-11-14-readers.md).
delivery: exchange/pass-shelat-ch5-8 27ae588db3952fb508f02184f9ea2adbb726cf6c ("fill canonizer: final"; checkpoint 3d65c246). Both
  commits touch only inbox/fills/canonizer/ (logs/exchange-commits.txt). git archive into a fresh directory (removed after use);
  inventory logs/payload-inventory.sha256 (170 files); extracts logs/delivery-extracts/ (patches/ + COMMITS.tsv, both manifests,
  pre-approval.md, probes/ReaderNeed.lean, probe-cp1/ (the worker's reader-need seal runs), final/checkpoint1 axioms, census and
  lint diffs, repro, searches, seals-compare.log), each byte-equal to a delivered file (logs/delivery-extract-hashes.txt, 26 EQUAL).
  Worker REPORT: logs/worker-REPORT.md.
integrity (logs/payload-check.txt, tools/mancheck.py): top SHA256SUMS 169/169 OK (170 delivered), evidence/SHA256SUMS 160/160 OK,
  exact path sets. git am of the 2 patches at 107f1e8c with COMMITS.tsv committer data (logs/git-am-integrity.log): both hashes
  reproduce (7064488b, ba7096e8e479e480f37bb3b7e7669225ec8d6c51), tree d39eff79d01e05c40facda9286c2724fc8df4ec8, only with the
  environment's SSH signing on; unsigned the tree is identical and the ids differ (logs/git-am-integrity-unsigned.log); COMMITS.tsv
  records no signing (C-F04). The 4 changed paths are byte-identical to src/, which holds exactly them (logs/src-equality.txt).
scope and the readers: changed paths M Universal.lean (owned), A Universal/Canonizer.lean (permitted helper), M CodeFormat.lean,
  M CodeSimulator.lean. The frozen files change by pure additions (git diff: 5 and 7 added lines, nothing removed), exactly the two
  pre-approved readers: Turing.oneTapeFormat_serialize_decode (xs : List Bool) : oneTapeFormat.serialize (oneTapeFormat.decode xs)
  = (codeDecode xs).serialize := rfl, after codeDecode_serialize_pad; Turing.oneTapeMachineFormat_serialize_decode (α : List Bool) :
  oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) = oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl, after
  oneTapeMachineFormat. Each `rfl`, beside its definitions, formula docstring, no attribute, between List Bool values: as the
  ruling. frozencheck on both files: 0 differences (CodeFormat 50 -> 51, CodeSimulator 208 -> 209 declarations). The worker's
  verbatim record of the dispatch-time pre-approval (delivery-extracts/pre-approval.md) agrees with the records ruling.
  Reader need: the worker's probe-cp1 (3 errors per variant, one per theorem) and this review's paired controls (below).
olean tree: $SP/dl-oleans. tree/snapshot-pre.txt: 1230 files, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f
  (= the sc-ot review's verified pre and post snapshots; records tree/base-records.jsonl copied from there).
landing: branch land/pass-shelat-canonizer (local), worktree $SP/wt-land-canonizer (sparse, briefs/ excluded; .lake/packages
  symlinked). Worker head ba7096e8 rebased onto origin 59c2c1fbf8c1bb08f9d191012b7cdd7e15248531 (#314 merged; rc 0, no conflict,
  the 4 paths equal the worker head; landing/landing.log). Origin delta since the issue base: landing/origin-delta-since-issue-base.txt
  (#307, #311, #312, #314), landing/origin-commits-since-issue-base.txt. LE-doc on top.
  r1 head da08374d4e5d1d00bf15aba9716407729e549f82 on 59c2c1fb (series landing/series-r1/); all probes, seals and controls below ran
  at r1. r3: #315 (prf-long) merged at the end of the review (origin a334ec2e1d87dbde7eac40812286ba60e85c9078); rebased onto it
  (landing/rebase-r3.log): rc 0, range-diff 3/3 identical, the 4 unit files and the 110-module closure unchanged.
  FINAL head 6421ac1631ef08feed297c810f0839b178d2a2bb, tree 3e16398e47f1c57b1d26c85ed731650dd094940b on a334ec2e; commits
  landing/commits.txt, series landing/series/0001-0003, author = committer = Claude <noreply@anthropic.com>:
    523d98cc canonizer: checkpoint 1 — the two rfl readers   11b24a7e canonizer: exists_canonizerExp proved
    6421ac16 canonizer landing edit LE-doc
  4 files, +133/-28 vs origin (landing/changed-paths-vs-origin.txt).
LE-doc (da08374d; tools/ledoc_canon.py; landing/le-doc.diff): exists_codeCanonizer gets its formula `∃ C d, C.ComputesFunInTime
  (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`. landing/le-doc-doconly.txt: code-identical True, 1 docstring changed,
  max width 97: RESULT OK. statements/head-le/docaudit.tsv: 6 OK, 1 NO-FORMULA = length_univArg's unchanged base prose.
build (landing head, order/build-queue.txt from tools/downorder.py vs eff2dcd0): build/ 190 modules = the downstream, through root
  TCSlib and audits/pass-shelat/Checks, of the 60 modules changed since eff2dcd0 (56 base delta #303-#312, #314: order/basedelta/;
  4 unit: order/unit-vs-origin/, 64 downstream modules, including the full CodeSimulator/CodeFormat downstream through TCSlib and
  audits/pass-shelat/Checks; audits/garg-ch1-3/Checks is downstream of the base delta only, and is in the 190). build/summary.txt: 190/190 rc 0, 0 errors (G26-N1),
  substring "error" 0, 1143 s (CodeSimulator 46 s). The unit files: warnings 0 except Universal's base `unused variable hc` in
  fUniversal_hard (base line 797, untouched proof). Sorry warnings only in admitted modules (build/summary.txt).
  Backups tree/backed-up.txt (145) and new tree/new-oleans.txt (45). tree/tree-check-head.txt (order/headfull-order.txt, 1244 modules;
  records logs/records-head.jsonl = base records + build): RESULT OK (23 head-probe oleans deleted first, logs/probe-oleans-deleted-head.txt).
  build-r3/ (FINAL head 6421ac16, order/r3-build-queue.txt, from the restored base tree: the downstream of all modules changed since
  eff2dcd0 = base delta #303-#312, #314, #315 + the unit): 191/191 rc 0, 0 errors (G26-N1), substring "error" 0, 1120 s.
  tree/r3/tree-check-head.txt (order/headfull-order-r3.txt, 1245 modules; logs/records-head-r3.jsonl): RESULT OK.
  logs/sorry-census-r3.txt: 19 -> 18, only Universal differs. Backups tree/r3/backed-up.txt (145), new tree/r3/new-oleans.txt (46);
  restore/r3/: 0 hash failures, 145 restored, 46 deleted, snapshot-post.txt byte-equal to tree/snapshot-pre.txt, tree-check-post.txt
  RESULT OK. Lint at the final head: lint/lint-landing-head-r3.txt 92/101, lint-complexity-landing-head-r3.txt 25/391; against the
  tip a334ec2e (lint/lint-records-tip-a334ec2e.txt 92/101, lint-complexity-records-tip-a334ec2e.txt 25/391): Cryptography line sets
  identical, Complexity the same 3 disclosed WARN changes.
statements (base 107f1e8c; the three pre-existing files are identical at eff2dcd0, 107f1e8c and 59c2c1fb):
  - statements/frozen/frozen-check.txt: CodeFormat 0, CodeSimulator 0, Universal 3 differences: PROSE of exists_canonizerExp (the
    brief: "Update the target's docstring (no longer an open problem)"; its header is identical), and HEADER of length_univArg and of
    the private exists_preimage_of_fUniversal_eq: the worker's whitespace-only re-wrap of over-100 lines (C-F01).
    statements/frozen/whitespace-check.txt: outside the target, the module docstring and the import, the owned file is identical
    after collapsing whitespace (18 changed lines, all re-wraps). Controls (one character changed each, statements/frozen/control-*):
    3 -> 4 for the Universal ones, 0 -> 1 for oneTapeFormat (CodeFormat body) and exists_polyCanonizer (CodeSimulator header).
    statements/frozen/topcmds.txt: no top-level command removed.
  - statements/head-le/decls2-vs-base.tsv: 4 ADDED (the two readers, the two helper theorems), 0 CHANGED, 0 REMOVED;
    decls2-vs-worker.tsv empty. touched.tsv: 5 CHANGED (exists_canonizerExp: prose, sketch, proof; length_univArg,
    exists_preimage_of_fUniversal_eq, invProbAt_reduction_ge, fUniversal_hard: whitespace only), 2 ADDED, 2 NEW_FILE, 296 UNCHANGED.
  - sketchaudit: 3 theorems with >= 15 proof lines, all with a sketch. Sizes (statements/head-le/sizes-widths.txt): Universal 955
    (<= 1000), Canonizer 83; both max width <= 100. CodeFormat 600 and CodeSimulator 9133 lines keep their 10 and 1 pre-existing wide
    lines (statements/base-widths.txt) and CodeSimulator its pre-existing size; the added lines are within 100.
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_canon.py) and DepTrace.lean (written here) -> probe-runs/:
  exists_canonizerExp, exists_polyCanonizer, computesFunInTime_appendBit, the helper theorems and the four conditional headlines:
  [propext, Classical.choice, Quot.sound]; oneTapeFormat_serialize_decode [propext, Quot.sound]. appendBitTM_computes itself has
  sorryAx. probe-runs/mods/PlProbe_DepTrace.log: the transitive constant closure of exists_canonizerExp (8151 constants) contains
  Turing.FinTM.computesFunInTime_appendBit, exists_polyCanonizer and both readers, and contains neither
  Turing.FinTM.appendBitTM_computes nor sorryAx: the route uses the proved lemma, not the admitted one.
  logs/census-summary.txt: 1077 stored constants (Universal 67, Canonizer 2, CodeFormat 122, CodeSimulator 886 = the worker's), axiom
  union the standard three, no sorryAx. Base (CensusBase on the restored tree): logs/census-base-vs-head.tsv: 1073 -> 1077, 4 added,
  0 removed, 0 type/attr changes, axioms-changed 1 (the target), no added simp, instance or abbrev.
admissions: logs/sorry-census.txt: issued 19 in 9 modules -> 18; only Asymptotic/Universal differs (1 -> 0). Outside the issued
  order only SeedMajority (#312) and SpecialEncryptionMulti (#311) changed since the issue base (base delta).
Rule 10 (landing head):
  - Collector probe-sources/head/CollectHead.lean -> probe-runs/; seals tools/mkseals_ab.py (strict) -> seals/{A,B},
    tools/mkseals_coe.py -> seals-coe/{A,B} (logs/mkseals-*.log; Universal 2061-2063 requests, Canonizer 1340, CodeFormat 234,
    CodeSimulator 1232; for the last three all four variants have the same request set). 16 head probes seal-runs/; base
    (CollectBase, restored tree) -> base-seals{,-coe}/{A,B}, 12 probes base-seal-runs/.
  - logs/seal-table-seals.txt, seal-table-seals-coe.txt (tools/sealtable.py over the sealsum rows without CodeSimulator, whose rows
    lack the EOF record; see below): Canonizer passes A and B, strict and coe; Universal head = base (A 10 errors in 4 declarations,
    B 12 in 6, all pre-existing; exists_canonizerExp not among them); CodeFormat base 14 in 5, head 16 in 6: the only new failing
    declaration is the reader oneTapeFormat_serialize_decode, attributed in logs/seal-attribution.txt (cascade of the base failure
    of oneTapeFormat under the seal; its siblings codeDecode, codeDecode_serialize_pad fail identically at the base). strict = coe.
  - CodeSimulator: every whole-file probe, head and base, stops at Lean's default maxErrors 100 (probe line 3929 of 9311; 101 errors
    in 48 declarations; no G06-SEAL-END), here and in the worker's delivered seals (C-F02). Full-file reruns with -DmaxErrors=0
    (seal-full/: tools/probefull.sh = tools/probe.sh with -DmaxErrors=0, tools/fullsealmap.py; the head run with the head CodeFormat
    olean rebuilt in the tree for it, seal-full/codeformat-head-build/, then the base olean restored from its backup, hash
    9ada8a3c… checked): base 177 errors in 58 declarations, head 177 in the same 58 with equal per-declaration counts
    (seal-full/{base,head}-full-decls.txt), both reaching the EOF record; the reader is not among them. seal-full/runs-{head,base}/:
    a first attempt with an in-file `set_option maxErrors 0`, which the frontend ignores (still cut at 100): superseded.
  - Paired controls tools/mkctl_canon.py (rows PolyExpr.eval, FinDist CoeFun instance, Turing.unaryFin, Turing.oneTapeFormat,
    Turing.oneTapeMachineFormat) -> controls/ (coe, 14 probes, 16 negatives), controls-strict/ (16, 21), runs control-runs/:
    logs/ctlcheck.log ALL_OK True; logs/ctlcheck-strict.log: all negatives fail exactly once, ctlCoeReader fails in the two strict
    Universal probes (attributed, logs/controls-attribution.txt, as in sc-ot-r1). Under the Canonizer seal the `rfl` forms of both
    reader statements fail exactly once and the readers pass: each reader is needed and sufficient.
  - Explicit-unfold scan (scan/items-head.json, scan/explicit-head.json, logs/scan2-head.log): 3256 items; 224 foreign items, all in
    untouched (byte-identical, pre-existing) declarations of CodeFormat (10) and CodeSimulator (214); 0 in any touched declaration
    (the readers, the target, the helper, the re-wrapped declarations).
lint (#305 script): Cryptography 92 FAIL / 101 WARN at the records tip 59c2c1fb (lint/lint-records-tip-59c2c1fb.txt) and at the
  landing head (lint-landing-head-f15ffa0b.txt; the LE edits only a docstring), identical line sets (lint/linediff-crypto.txt).
  Complexity 25 / 391 at both; lint/linediff-complexity.txt: two check-8 WARN lines shortened by the readers (oneTapeFormat,
  oneTapeMachineFormat now have a lemma beside them) and CodeSimulator's pre-existing size WARN reading 9133 for 9126, as the REPORT
  discloses; no new FAIL or WARN line.
content: the target is `obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le; exact ⟨c, d, d, h⟩` (CanonizerExp is
  the owned file's own definition). The helper takes C, d from exists_polyCanonizer at oneTapeMachineFormat, transports its
  specification along the two readers (`hf ▸ hC`), builds ⟨⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩, C,
  n ↦ d (n+1)^d, hC⟩ and bounds d (k+1)^d ≤ d 2^{dk} by k+1 ≤ 2^k, pow_mul, pow_le_pow_left. Edge cases k = 0, d = 0 and malformed
  codes hold (the polynomial bound is on every input). The conditional headlines are unchanged and stay conditional.
duplication: logs/duplication-review.txt. Info notes only (C-F05, C-F06).
open PRs (logs/open-pr-overlap.txt): #314 merged during the review and #315 at its end (base delta, built at r1 and r3 resp.). #313 and #315 touch no unit file and no
  module of the unit's 110-module closure; merge-tree of the landing head with #313 94b31964 clean (847e7ac3; shared downstream
  Randomness facade, TCSlib) and with #315 fbd37f44 clean (18e75536; shared downstream Asymptotic facade, Randomness, TCSlib,
  audits/pass-shelat/Checks); no name clash. Also sc-ot landing 93c20338 x canonizer landing da08374d: merge-tree clean (712155d1).
restore (restore/restore-log.txt, tools/restore.sh): 145 backups back (0 hash failures), 45 new oleans deleted, 6 emptied directories
  pruned: SNAPSHOT EQUAL; base probes then run, CodeFormat head olean (full-seal step) replaced by its backup, and the 2 base-probe
  oleans deleted (restore/probe-oleans-deleted-base.txt). tree/snapshot-post.txt: 1230 files, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f, byte-identical to tree/snapshot-pre.txt; tree/tree-check-post.txt:
  1199 base modules, RESULT OK.
tools/: sc-ot-r1 tools plus mkcensus_canon.py, mkctl_canon.py, ledoc_canon.py, probefull.sh, fullsealmap.py (and DepTrace.lean in
  probe-sources/head/).
worker environment note (REPORT §8.1): to pass preflight the worker removed its host's learning-fill worktree (/workspace/learn,
  branch kept) and that fill's scratch directories. Environment-only, on the worker's host (info).
cleanup: payload extraction, olean backups (bk-canon, bk-canon3), the integrity worktree removed; PlProbe/ removed from the landing worktree, which is clean.
SHA256SUMS: every file here except itself. ../canonizer-r1-evidence.zip holds exactly the manifest's paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/35-canonizer/pr-description.md =====

This is the landing PR for the Pass–shelat `canonizer` fill. It proves `exists_canonizerExp` in `Asymptotic/Universal.lean`.

**Head:** `6421ac1631ef08feed297c810f0839b178d2a2bb`.
**Base:** `cryptography/pass-shelat-ch2-4` at `a334ec2e1d87dbde7eac40812286ba60e85c9078`.

## What changes
4 Lean files change, +133/−28:
- **Two `rfl` readers**, the frozen-file exceptions Seyoon approved on 2026-11-14. Each sits beside its definition, has a formula docstring and no attribute, and is stated between `List Bool` values:
  - `CodeFormat.lean`: `oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`
  - `CodeSimulator.lean`: `oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) = oneTapeFormat.serialize (oneTapeFormat.decode α)`
- **The owned file `Universal.lean`:** the target proof `⟨c, d, d, h⟩`. The worker also re-wrapped six pre-existing lines that were over 100 characters (C-F01). The change is whitespace only, of the LE-width class.
- **A new helper `Universal/Canonizer.lean`:** it transports `exists_polyCanonizer` along the readers and proves `d(k+1)^d ≤ d·2^{dk}`.

## Commits
- Two worker commits: the readers and the proof.
- **LE-doc** `6421ac16`: a formula docstring for `exists_codeCanonizer`.

## Review
The record is `briefs/pass-shelat-ch5-8/fills/canonizer/final-r1/review.md`. Verdict: **ACCEPT WITH LANDING EDITS**.
- **Statements:** decls2 gives 4 ADDED, 0 CHANGED. The frozen check finds only the target's prose, which the brief requires, and the C-F01 whitespace.
- **Axioms:** standard only, across 1077 constants. The target's closure contains neither the admitted `appendBitTM_computes` nor `sorryAx`.
- **Build:** 191/191 rc 0, 0 errors. The whole-tree check covers 1245 modules: OK.
- **Rule 10:** each reader is needed and sufficient: the `rfl` forms fail once under the seal, and the readers pass. `CodeSimulator`'s full-file seal, run with `-DmaxErrors=0`, equals the base's.
- **Admissions:** 19 → 18.
- **Lint:** unchanged.

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/35-canonizer/pr.diff.txt =====

diff --git a/TCSlib/Complexity/TuringMachine/CodeFormat.lean b/TCSlib/Complexity/TuringMachine/CodeFormat.lean
index 9af1b2401..5b652d014 100644
--- a/TCSlib/Complexity/TuringMachine/CodeFormat.lean
+++ b/TCSlib/Complexity/TuringMachine/CodeFormat.lean
@@ -580,6 +580,11 @@ lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
     codeDecode (M.serialize ++ List.replicate m true) = M :=
   oneTapeFormat.decode_serialize_pad M m
 
+/-- The one-tape format's canonical serialization is that of the decoded machine:
+`oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`. -/
+theorem oneTapeFormat_serialize_decode (xs : List Bool) :
+    oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl
+
 /-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
 def codeScan (xs : List Bool) : Option (List Bool) :=
   oneTapeFormat.scan xs
diff --git a/TCSlib/Complexity/TuringMachine/CodeSimulator.lean b/TCSlib/Complexity/TuringMachine/CodeSimulator.lean
index f71f40023..f7492822e 100644
--- a/TCSlib/Complexity/TuringMachine/CodeSimulator.lean
+++ b/TCSlib/Complexity/TuringMachine/CodeSimulator.lean
@@ -187,6 +187,13 @@ def oneTapeMachineFormat : MachineFormat :=
     serialize_eq := oneTape_serialize_eq
     skipTable_eq := oneTape_skipTable_eq }
 
+/-- The machine format's canonical serialization is the one-tape format's:
+`oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
+oneTapeFormat.serialize (oneTapeFormat.decode α)`. -/
+theorem oneTapeMachineFormat_serialize_decode (α : List Bool) :
+    oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
+      oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl
+
 namespace MachineFormat
 
 variable (F : MachineFormat)
diff --git a/TCSlib/Cryptography/Asymptotic/Universal.lean b/TCSlib/Cryptography/Asymptotic/Universal.lean
index 416f8cab3..b87bc08bc 100644
--- a/TCSlib/Cryptography/Asymptotic/Universal.lean
+++ b/TCSlib/Cryptography/Asymptotic/Universal.lean
@@ -10,6 +10,7 @@ import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
 import TCSlib.Cryptography.Asymptotic.UniversalLemmas
 import TCSlib.Cryptography.Asymptotic.UniversalPadding
 import TCSlib.Cryptography.OneWayFunctions.OutputLength
+import TCSlib.Cryptography.Asymptotic.Universal.Canonizer
 import Mathlib.Data.Nat.Log
 
 set_option maxHeartbeats 0
@@ -44,8 +45,9 @@ length (`CanonizerExp c`), so that the coefficient is polynomial in `n` for code
 so the headlines `fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay` and
 `theorem_63_1` are **conditional** on this hypothesis — ratified by the run-3 audit (P3-4) as
 an explicit hypothesis in the manner of the arithmetic bundle `Candidates.ArithmeticFP`
-(plan D11); the open problem of exhibiting a scheme with such a canonizer is the sorried
-`exists_canonizerExp`.
+(plan D11). Some scheme satisfies the hypothesis (`exists_canonizerExp`, proved from the
+machine library's polynomial canonizer `Turing.MachineFormat.exists_polyCanonizer`), so the
+conditional headlines apply to it.
 
 **Deviation (typed domains, D5):** `fUniversal c` is `FunFamily.ofString` of the string
 function with the output-length polynomial `univOutLen` (outputs padded with `false`, never
@@ -69,8 +71,8 @@ computable by a coded machine on the bare input (`FunFamily.QuadraticCode`).
   `clockedAnswer` (repackaging of `Turing.timed_universal_concrete`); the serialization-length
   facts it needs live in `TCSlib.Cryptography.Asymptotic.UniversalLemmas`;
   `TCSlib.Cryptography.exists_univCoeff_le` — its coefficient is polynomial on codes of
-  length `⌊log₂ n⌋` under `CanonizerExp`; `TCSlib.Cryptography.exists_canonizerExp` — the
-  open problem that some scheme satisfies `CanonizerExp` (sorried, run-3 audit P3-4).
+  length `⌊log₂ n⌋` under `CanonizerExp`; `TCSlib.Cryptography.exists_canonizerExp` — some
+  scheme satisfies `CanonizerExp` (proved, run-3 audit P3-4 closed).
 * `TCSlib.Cryptography.fUniversal_easy` — `f_universal` is polynomial-time computable
   [PS10, Algorithm 64.2, "computable in time `O(|y|³)`"] (proved; the evaluator is assembled
   from `polyTimeComputable_univCode`, `polyTimeComputable_univArg`,
@@ -88,6 +90,12 @@ computable by a coded machine on the bare input (`FunFamily.QuadraticCode`).
   `fUniversal_weakOneWay` are proved from the hypothesis of `lemma_64_3`; `theorem_63_1`
   uses the quadratic-time strong one-way family supplied by `lemma_64_3`).
 
+## Contents
+
+The proof of `exists_canonizerExp` uses the helper module
+`TCSlib.Cryptography.Asymptotic.Universal.Canonizer` (`exists_codeCanonizer`,
+`exists_effectiveMachineCode_canonizerTime_le`).
+
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
@@ -189,7 +197,8 @@ def univArg (y : List Bool) : List Bool := y.drop (Nat.log 2 y.length)
   simp [univCode, Nat.log_le_self]
 
 /-- The argument field has `|y| - ⌊log₂ |y|⌋` bits. -/
-@[simp] theorem length_univArg (y : List Bool) : (univArg y).length = y.length - Nat.log 2 y.length := by
+@[simp] theorem length_univArg (y : List Bool) :
+    (univArg y).length = y.length - Nat.log 2 y.length := by
   simp [univArg]
 
 /-- The code field of `α ++ x` is `α` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
@@ -282,25 +291,21 @@ through this hypothesis (no bound is known for `Turing.exists_effectiveMachineCo
 def CanonizerExp (c : EffectiveMachineCode) : Prop :=
   ∃ A B : ℕ, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)
 
-/-- **Open problem (run-3 audit P3-4): some effective encoding scheme has a canonizer at most
-exponential in the code length.** The standard encodings have polynomial canonizers (parse and
-re-serialize), so the hypothesis `CanonizerExp c` of `theorem_63_1` is mathematically harmless
-and is accepted as an explicit hypothesis (plan D11, like `Candidates.ArithmeticFP`); but the
-only scheme in the library, `Turing.exists_effectiveMachineCode`, carries a `canonizerTime`
-defined as a finite maximum of halting times with no bound, so no instance is available and the
-headlines of this file are conditional. This statement records the gap.
-
-**Proof sketch.** Build a scheme in the `Build/` style: keep the serialization
-`Turing.CodeTM.serialize` and the parser `Turing.codeDecode` of
-`TCSlib.Complexity.TuringMachine.MathlibBridge`, and implement the canonizer as an explicit
-finite machine performing the parse of the `9 · (numStates + 1)` fixed-format records (with the
-up-front minimum-length guard) followed by re-serialization — the superseded composition route
-described in `MathlibBridge` — through the combinators of
-`TCSlib.Complexity.TuringMachine.Composition` and the primitives of
-`TCSlib.Complexity.TuringMachine.Build`; its running time is polynomial in the code length,
-in particular `≤ A · 2^{B k}`. -/
+/-- **Some effective encoding scheme has a canonizer at most exponential in the code length**
+[PS10, §2.13] (run-3 audit P3-4, formerly an open problem): `∃ c, CanonizerExp c`, i.e. some
+`c : EffectiveMachineCode` and `A, B` with `c.canonizerTime k ≤ A · 2^{B k}` for every `k`. So the
+hypothesis `CanonizerExp c` of `theorem_63_1` is satisfiable; the headlines of this file stay
+stated for an arbitrary scheme satisfying it (plan D11).
+
+**Proof sketch.** The scheme is the machine library's one-tape code: serialization
+`Turing.CodeTM.serialize`, parser `Turing.codeDecode`, and the canonizer of
+`Turing.MachineFormat.exists_polyCanonizer` at `Turing.oneTapeMachineFormat`, which runs in time
+`d · (n + 1)^d` on every input, malformed codes included
+(`exists_effectiveMachineCode_canonizerTime_le`, in `Universal/Canonizer`). Since `k + 1 ≤ 2^k`,
+`d · (k + 1)^d ≤ d · 2^{d k}`, so `A = B = d`. -/
 theorem exists_canonizerExp : ∃ c : EffectiveMachineCode, CanonizerExp c := by
-  sorry
+  obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le
+  exact ⟨c, d, d, h⟩
 
 /-- **The coefficient is polynomial on codes of logarithmic length.** If `c` has an
 exponential canonizer, there is a syntactic polynomial `p` with
@@ -654,7 +659,8 @@ private theorem exists_preimage_of_fUniversal_eq (c : EffectiveMachineCode) {L :
     (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool)
     (y y' : Fin ((fUniversal c).inLen.eval n) → Bool)
     (hy : List.ofFn y = code ++ List.ofFn x) (h : (fUniversal c).f n y' = (fUniversal c).f n y) :
-    ∃ x' : Fin (n - Nat.log 2 n) → Bool, List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
+    ∃ x' : Fin (n - Nat.log 2 n) → Bool,
+      List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
   have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
   obtain ⟨x', hx'⟩ := exists_ofFn_eq_of_length (m := n - Nat.log 2 n)
     (w := univArg (List.ofFn y')) (by simp [fUniversal_inLen_eval])
@@ -717,7 +723,8 @@ private theorem invProbAt_reduction_ge (c : EffectiveMachineCode) {L : PolyExpr}
     exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
   obtain ⟨cf, hcf⟩ := exists_ofFn_eq_of_length (m := Nat.log 2 n) hcode
   let Invert : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) → Prop :=
-    fun w => ∃ y', A.runAt n (List.ofFn ((fUniversal c).f n (e (w.1, w.2.1)))) w.2.2 = List.ofFn y' ∧
+    fun w => ∃ y',
+      A.runAt n (List.ofFn ((fUniversal c).f n (e (w.1, w.2.1)))) w.2.2 = List.ofFn y' ∧
       (fUniversal c).f n y' = (fUniversal c).f n (e (w.1, w.2.1))
   have hInv : uprob Invert = (fUniversal c).invProbAt A n := by
     rw [FunFamily.invProbAt_eq_uprob]
@@ -752,7 +759,8 @@ private theorem invProbAt_reduction_ge (c : EffectiveMachineCode) {L : PolyExpr}
     g _ x' = g _ w.1.1
   have hBrun : B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 =
       univArg (List.ofFn y') := by
-    rw [NUPPT.runAt_eq, hB, hcoins, List.take_left' (List.length_ofFn (f := w.1.2)), ← NUPPT.runAt_eq,
+    rw [NUPPT.runAt_eq, hB, hcoins, List.take_left' (List.length_ofFn (f := w.1.2)),
+      ← NUPPT.runAt_eq,
       padStr_eq_ofFn_fUniversal_f c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) hy, hy']
   obtain ⟨x', hx', hgx'⟩ :=
     exists_preimage_of_fUniversal_eq c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) y' hy hfy'
@@ -892,8 +900,10 @@ theorem fUniversal_hard (c : EffectiveMachineCode) (hc : CanonizerExp c)
   rw [hφm] at hkey
   rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
   refine le_trans ?_ hkey
-  have hm2 : (2 : ℝ) ≤ ((n - Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - Nat.log 2 n by omega)
-  have hn2 : (2 : ℝ) ≤ ((φ (n - Nat.log 2 n) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ φ (n - Nat.log 2 n) by omega)
+  have hm2 : (2 : ℝ) ≤ ((n - Nat.log 2 n : ℕ) : ℝ) := by
+    exact_mod_cast (show 2 ≤ n - Nat.log 2 n by omega)
+  have hn2 : (2 : ℝ) ≤ ((φ (n - Nat.log 2 n) : ℕ) : ℝ) := by
+    exact_mod_cast (show 2 ≤ φ (n - Nat.log 2 n) by omega)
   have h1 : 1 / ((n - Nat.log 2 n : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2
   have h2 : 1 / ((φ (n - Nat.log 2 n) : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by
     refine one_div_le_one_div_of_le (by norm_num) ?_
diff --git a/TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean b/TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean
new file mode 100644
index 000000000..4bf78f3cb
--- /dev/null
+++ b/TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean
@@ -0,0 +1,83 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Complexity.TuringMachine.CodeSimulator
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# An effective machine code with a polynomial canonizer
+
+The encoding hypothesis of [PS10, §2.13, Theorem 63.1] as formalized (`CanonizerExp`) asks for an
+effective machine code whose canonizer runs in time at most exponential in the code length. The
+machine library's one-tape code format has a canonizer running in time `d · (n + 1)^d` on every
+input (`Turing.MachineFormat.exists_polyCanonizer`, at `Turing.oneTapeMachineFormat`). This file
+reads its specification as one of `α ↦ (codeDecode α).serialize`
+(`Turing.oneTapeMachineFormat_serialize_decode`, `Turing.oneTapeFormat_serialize_decode`), builds
+the effective machine code with the serialization `CodeTM.serialize`, the decoder `codeDecode`
+and that canonizer (the scheme of `Turing.exists_uniformMachineCode`, here with its time bound
+visible), and bounds the polynomial time by an exponential: `d · (k + 1)^d ≤ d · 2^{d k}`.
+
+## Main results
+
+* `TCSlib.Cryptography.exists_codeCanonizer`: a machine computing `α ↦ (codeDecode α).serialize`
+  in time `d · (n + 1)^d`.
+* `TCSlib.Cryptography.exists_effectiveMachineCode_canonizerTime_le`: an effective machine code
+  with `canonizerTime k ≤ d · 2^{d k}` for every `k`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §2.13, Theorem 63.1 (book p. 63).
+-/
+
+namespace TCSlib.Cryptography
+
+open Turing
+
+/-- **A polynomial canonizer of the one-tape codes:** there are a machine `C` and a degree `d`
+such that `C` computes `α ↦ (codeDecode α).serialize` in time `n ↦ d · (n + 1)^d`, on every input
+(malformed codes included: they decode to the fallback machine):
+`∃ C d, C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`.
+
+**Proof sketch.** `Turing.MachineFormat.exists_polyCanonizer` at `oneTapeMachineFormat` computes
+`α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)`, which is
+`(codeDecode α).serialize` by the readers `oneTapeMachineFormat_serialize_decode` and
+`oneTapeFormat_serialize_decode`. -/
+theorem exists_codeCanonizer :
+    ∃ (C : FinTM Bool) (d : ℕ),
+      C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d := by
+  obtain ⟨C, d, hC⟩ := oneTapeMachineFormat.exists_polyCanonizer
+  have hf : (fun α => oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)) =
+      fun α => (codeDecode α).serialize :=
+    funext fun α =>
+      (oneTapeMachineFormat_serialize_decode α).trans (oneTapeFormat_serialize_decode α)
+  exact ⟨C, d, hf ▸ hC⟩
+
+/-- **An effective machine code with an exponential canonizer** [PS10, §2.13, the encoding
+behind Theorem 63.1]: there are an effective machine code `c` and `d : ℕ` with
+`c.canonizerTime k ≤ d · 2^{d k}` for every `k`.
+
+**Proof sketch.** Take `C, d` from `exists_codeCanonizer` and the code
+`⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩` with canonizer `C` and
+`canonizerTime n = d · (n + 1)^d`. Since `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`),
+`(k + 1)^d ≤ (2^k)^d = 2^{d k}` (`Nat.pow_le_pow_left`, `pow_mul`). The case `d = 0` needs no
+care (both sides are `0`), nor does `k = 0` (`1 ≤ 1`). -/
+theorem exists_effectiveMachineCode_canonizerTime_le :
+    ∃ (c : EffectiveMachineCode) (d : ℕ), ∀ k, c.canonizerTime k ≤ d * 2 ^ (d * k) := by
+  obtain ⟨C, d, hC⟩ := exists_codeCanonizer
+  refine ⟨{ toMachineCode := ⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩
+            canonizer := C
+            canonizerTime := fun n => d * (n + 1) ^ d
+            canonizer_computes := hC }, d, fun k => ?_⟩
+  show d * (k + 1) ^ d ≤ d * 2 ^ (d * k)
+  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
+  have hpow : (k + 1) ^ d ≤ 2 ^ (d * k) := by
+    rw [mul_comm, pow_mul]
+    exact Nat.pow_le_pow_left hk d
+  exact Nat.mul_le_mul_left d hpow
+
+end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Universal.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import TCSlib.Cryptography.Asymptotic.UniversalPadding
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import TCSlib.Cryptography.Asymptotic.Universal.Canonizer
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Levin's universal one-way function

The universal one-way function of [PS10, §2.13]: `f_universal` interprets its input `y` as a
machine–input pair `⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, runs `M` on `x` for a cubic number of
steps through the clocked universal machine `Turing.timed_universal_concrete`, and outputs
`⟨M, M(x)⟩` (or `⟨M, ⊥⟩` on timeout). [PS10, Theorem 63.1] says that `f_universal` is one-way
as soon as *some* one-way function exists; the proof shows weak one-wayness with `q(n) = n³`
through [PS10, Lemma 64.3] (a strong one-way function computable in quadratic time, by
padding) and the two counting claims of [PS10, p. 65] (`PickG`, the union bound), then applies
Yao's amplification [PS10, Theorem 35.1] (`weak_to_strong`).

**Deviation (source error, DESIGN §7, error 1):** [PS10, Algorithm 64.2] outputs `M(x)` only;
an inverter may then answer `⟨M', x'⟩` with `M' ≠ M_g`, which yields no preimage under `M_g`,
and the proof of Theorem 63.1 is invalid. The corrected function outputs `⟨M, M(x)⟩` (Levin's
definition). The budget `|y|³` becomes `(|y| + 1)³` (error 19); the timeout symbol `⊥` is
`[false]`, distinct from every successful answer `true :: M(x)` (`Turing.timed_universal`).

**Deviation (encoding of machines):** the text "assumes a standard way to encode Turing
machines with appropriate padding"; here the encoding is an arbitrary effective scheme
`c : Turing.EffectiveMachineCode` ([AB09, §1.4], `decode_encode_pad`), and the clocked
simulation costs the code-dependent coefficient of `Turing.timed_universal_concrete`, which
includes `c.canonizerTime |M|`. The theorems assume a canonizer at most exponential in the code
length (`CanonizerExp c`), so that the coefficient is polynomial in `n` for codes of length
`⌊log₂ n⌋`; no bound on the canonizer of `Turing.exists_effectiveMachineCode` is available,
so the headlines `fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay` and
`theorem_63_1` are **conditional** on this hypothesis — ratified by the run-3 audit (P3-4) as
an explicit hypothesis in the manner of the arithmetic bundle `Candidates.ArithmeticFP`
(plan D11). Some scheme satisfies the hypothesis (`exists_canonizerExp`, proved from the
machine library's polynomial canonizer `Turing.MachineFormat.exists_polyCanonizer`), so the
conditional headlines apply to it.

**Deviation (typed domains, D5):** `fUniversal c` is `FunFamily.ofString` of the string
function with the output-length polynomial `univOutLen` (outputs padded with `false`, never
truncated by `length_fUniversalStr_le`); the `g'` of Lemma 64.3 is a family with `inLen = var`
computable by a coded machine on the bare input (`FunFamily.QuadraticCode`).

## Main definitions

* `TCSlib.Cryptography.clockedAnswer`, `TCSlib.Cryptography.univCoeff` — the answer and the
  coefficient of the clocked universal simulation.
* `TCSlib.Cryptography.univCode`, `TCSlib.Cryptography.univArg`,
  `TCSlib.Cryptography.fUniversalStr`, `TCSlib.Cryptography.univOutLen`,
  `TCSlib.Cryptography.fUniversal` — `f_universal` [PS10, Algorithm 64.2], corrected.
* `TCSlib.Cryptography.CanonizerExp` — the hypothesis on the encoding scheme;
  `TCSlib.Cryptography.FunFamily.QuadraticCode` — computable by a coded machine in time
  `c₀ (|x| + 1)²` [PS10, Lemma 64.3].

## Main results

* `TCSlib.Cryptography.exists_univ_computes` — the clocked universal machine computes
  `clockedAnswer` (repackaging of `Turing.timed_universal_concrete`); the serialization-length
  facts it needs live in `TCSlib.Cryptography.Asymptotic.UniversalLemmas`;
  `TCSlib.Cryptography.exists_univCoeff_le` — its coefficient is polynomial on codes of
  length `⌊log₂ n⌋` under `CanonizerExp`; `TCSlib.Cryptography.exists_canonizerExp` — some
  scheme satisfies `CanonizerExp` (proved, run-3 audit P3-4 closed).
* `TCSlib.Cryptography.fUniversal_easy` — `f_universal` is polynomial-time computable
  [PS10, Algorithm 64.2, "computable in time `O(|y|³)`"] (proved; the evaluator is assembled
  from `polyTimeComputable_univCode`, `polyTimeComputable_univArg`,
  `polyTimeComputable_clockedAnswer` and `polyTimeComputable_fUniversalStr`, with the generic
  padding and splitting lemmas of `TCSlib.Cryptography.Asymptotic.CollectionsLemmas` and
  `TCSlib.Cryptography.Asymptotic.UniversalLemmas`).
* `TCSlib.Cryptography.lemma_64_3` — a strong one-way function computable in quadratic time
  [PS10, Lemma 64.3] (from `PadQuad.exists_family` of
  `TCSlib.Cryptography.Asymptotic.UniversalPadding`, with its linear-time evaluator).
* `TCSlib.Cryptography.claim_65_1`, `claim_65_2`, `claim_65_2_cond` — `PickG` and the union
  bound [PS10, p. 65].
* `TCSlib.Cryptography.fUniversal_hard`, `TCSlib.Cryptography.fUniversal_weakOneWay`,
  `TCSlib.Cryptography.theorem_63_1` — `f_universal` is weakly one-way with `q(n) = n³`, hence
  (after amplification) strongly one-way [PS10, Theorem 63.1] (`fUniversal_hard` and
  `fUniversal_weakOneWay` are proved from the hypothesis of `lemma_64_3`; `theorem_63_1`
  uses the quadratic-time strong one-way family supplied by `lemma_64_3`).

## Contents

The proof of `exists_canonizerExp` uses the helper module
`TCSlib.Cryptography.Asymptotic.Universal.Canonizer` (`exists_codeCanonizer`,
`exists_effectiveMachineCode_canonizerTime_le`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13: Theorem 63.1, Algorithm 64.2, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding) and Exercise 2.4.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4: encodings of machines, universal simulation.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The clocked universal simulation -/

/-- The answer of the clocked simulation of the coded machine `c.decode α` on the input `x`
with the budget `t`: `true :: output` if the machine has halted within `t` steps (deadline
included), `[false]` (the `⊥` of [PS10, Algorithm 64.2]) otherwise — the output convention of
`Turing.timed_universal`. -/
def clockedAnswer (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  if ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none then
    true :: ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output
  else [false]

/-- The code-dependent coefficient of the quadratic time bound of the clocked universal
simulation, as displayed in `Turing.timed_universal_concrete` (startup part
`3|α| + canonizerTime |α| + |serialize| + 2|bits numStates| + 2 q₀ + 16`, then
`Turing.universalBlockBound c α + 14`). -/
def univCoeff (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
    universalBlockBound c α + 14

/-- If the coded machine computes `out` from `x` within `t` steps, the clocked answer is
`true :: out`. -/
theorem clockedAnswer_eq_cons_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (h : (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = true :: out := by
  obtain ⟨hs, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  have hs' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none := hs
  have ho' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output = out := ho
  unfold clockedAnswer
  rw [if_pos hs', ho']

/-- If the coded machine does not halt on `x` within `t` steps, the clocked answer is the
timeout symbol `[false]`. -/
theorem clockedAnswer_eq_false_of_not_computesInTime (c : EffectiveMachineCode)
    {α x : List Bool} {t : ℕ} (h : ∀ out, ¬ (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = [false] := by
  have hs : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
    intro hs
    exact h _ ((FinTM.computesInTime_iff (c.decode α).toFinTM _ _ _).mpr ⟨hs, rfl⟩)
  unfold clockedAnswer
  rw [if_neg hs]

/-- The clocked answer has at most `t + 1` bits (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem length_clockedAnswer_le (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (clockedAnswer c α x t).length ≤ t + 1 := by
  unfold clockedAnswer
  split_ifs
  · simp only [List.length_cons]
    exact Nat.add_le_add_right ((c.decode α).tm.output_length_le x t) 1
  · simp

/-- **The clocked universal machine** [AB09, §1.4.1; `Turing.timed_universal_concrete`]: one
machine `U` which, on `⟨⟨bits t, α⟩, x⟩`, outputs `clockedAnswer c α x t` within
`univCoeff c α · (t + 1)²` steps, for every code `α`, input `x` and budget `t`.

**Proof sketch.** The simulator of `Turing.timed_universal_concrete c`: success clause with
`clockedAnswer_eq_cons_of_computesInTime`, or timeout clause with
`clockedAnswer_eq_false_of_not_computesInTime`. -/
theorem exists_univ_computes (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (clockedAnswer c α x t)
        (univCoeff c α * (t + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  by_cases h : ∃ out, (c.decode α).toFinTM.ComputesInTime x out t
  · obtain ⟨out, hout⟩ := h
    rw [clockedAnswer_eq_cons_of_computesInTime c hout]
    exact (hU α x t).1 out hout
  · push_neg at h
    rw [clockedAnswer_eq_false_of_not_computesInTime c h]
    exact (hU α x t).2 h

/-! ## Algorithm 64.2: the universal function -/

/-- The code field of `y`: its first `⌊log₂ |y|⌋` bits ("interpret `y` as `⟨M, x⟩` where
`|M| = log |y|`", [PS10, Algorithm 64.2]). -/
def univCode (y : List Bool) : List Bool := y.take (Nat.log 2 y.length)

/-- The argument field of `y`: the bits after the first `⌊log₂ |y|⌋` [PS10, Algorithm 64.2]. -/
def univArg (y : List Bool) : List Bool := y.drop (Nat.log 2 y.length)

/-- The code field has exactly `⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univCode (y : List Bool) : (univCode y).length = Nat.log 2 y.length := by
  simp [univCode, Nat.log_le_self]

/-- The argument field has `|y| - ⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univArg (y : List Bool) :
    (univArg y).length = y.length - Nat.log 2 y.length := by
  simp [univArg]

/-- The code field of `α ++ x` is `α` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univCode_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univCode (α ++ x) = α := by
  simp only [univCode, List.length_append, ← hα]
  exact List.take_left

/-- The argument field of `α ++ x` is `x` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univArg_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univArg (α ++ x) = x := by
  simp only [univArg, List.length_append, ← hα]
  exact List.drop_left

/-- **`f_universal` as a string function** [PS10, Algorithm 64.2, corrected]: interpret `y` as
`⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, run `M` on `x` for `(|y| + 1)³` steps, and output `⟨M, M(x)⟩`
(`M(x)` prefixed by `true`) if `M` halts, `⟨M, ⊥⟩` (`⊥ = [false]`) otherwise.

**Deviation:** the output carries the code `M` (DESIGN §7, error 1); budget `(|y| + 1)³`
(error 19); machines are decoded by the effective scheme `c`. -/
def fUniversalStr (c : EffectiveMachineCode) (y : List Bool) : List Bool :=
  pairEncode (univCode y) (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))

/-- The output-length polynomial of `f_universal`: `2n + 3 + (n + 1)³`, a bound on
`|⟨M, answer⟩| = 2|M| + 2 + |answer| ≤ 2⌊log₂ n⌋ + 2 + (n + 1)³ + 1`. -/
def univOutLen : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.const 3)) (.pow (.add .var (.const 1)) 3)

/-- `univOutLen` evaluates to `2n + 3 + (n + 1)³`. -/
@[simp] theorem eval_univOutLen (n : ℕ) : univOutLen.eval n = 2 * n + 3 + (n + 1) ^ 3 := rfl

/-- The output of `f_universal` on `y` has at most `univOutLen |y|` bits (so the family
`fUniversal` pads and never truncates). -/
theorem length_fUniversalStr_le (c : EffectiveMachineCode) (y : List Bool) :
    (fUniversalStr c y).length ≤ univOutLen.eval y.length := by
  simp only [fUniversalStr, length_pairEncode, length_univCode, eval_univOutLen]
  have h₁ := length_clockedAnswer_le c (univCode y) (univArg y) ((y.length + 1) ^ 3)
  have h₂ := Nat.log_le_self 2 y.length
  omega

/-- On a well-formed `y = α ++ x` (`|α| = ⌊log₂ |y|⌋`) whose coded machine computes `out`
from `x` within the budget, `f_universal (y) = ⟨α, true :: out⟩`: the evaluation step
"`f_universal (⟨M_g, x⟩) = ⟨M_g, g(x)⟩`" of the proof of [PS10, Theorem 63.1]. -/
theorem fUniversalStr_append_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (hα : α.length = Nat.log 2 (α.length + x.length))
    (h : (c.decode α).toFinTM.ComputesInTime x out t) (ht : t ≤ (α.length + x.length + 1) ^ 3) :
    fUniversalStr c (α ++ x) = pairEncode α (true :: out) := by
  simp only [fUniversalStr, univCode_append hα, univArg_append hα, List.length_append]
  rw [clockedAnswer_eq_cons_of_computesInTime c (h.mono ht)]

/-- **`f_universal` as a function family** [PS10, Algorithm 64.2]: parameter = input length,
output length `univOutLen` (the string output padded with `false`, never truncated by
`length_fUniversalStr_le`). -/
def fUniversal (c : EffectiveMachineCode) : FunFamily :=
  FunFamily.ofString (fUniversalStr c) univOutLen

/-- The input length of `fUniversal c` at `n` is `n`. -/
theorem fUniversal_inLen_eval (c : EffectiveMachineCode) (n : ℕ) :
    (fUniversal c).inLen.eval n = n :=
  FunFamily.ofString_inLen_eval _ _ n

/-- The padded reading of a string: `List.ofFn (fun i : Fin p => w.getD i false)` is
`(w ++ 0^p).take p` (the encoding of `FunFamily.ofString`'s output). -/
theorem ofFn_getD_eq_take (w : List Bool) (p : ℕ) :
    List.ofFn (fun i : Fin p => w.getD i false) = (w ++ List.replicate p false).take p :=
  ofFn_padFin_eq_take p w

/-- The encoding of `fUniversal c` at parameter `n` is the string output padded with `false`
to `univOutLen n` bits. -/
theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ)
    (x : Fin ((fUniversal c).inLen.eval n) → Bool) :
    List.ofFn ((fUniversal c).f n x) =
      (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take
        (univOutLen.eval n) := by
  refine (List.ofFn_congr (FunFamily.ofString_outLen_eval (fUniversalStr c) univOutLen n) _).trans
    (Eq.trans ?_ (ofFn_getD_eq_take _ _))
  exact congrArg List.ofFn
    (funext fun i => (FunFamily.ofString_f_apply _ _ n x _).trans (by rw [Fin.coe_cast]))

/-! ## The encoding hypothesis and the polynomial coefficient -/

/-- The canonizer of the encoding scheme `c` runs in time at most exponential in the code
length: `canonizerTime k ≤ A · 2^{B k}`. For codes of length `⌊log₂ n⌋` the coefficient
`univCoeff` of the clocked simulation is then polynomial in `n` (`exists_univCoeff_le`), which
is what makes `f_universal` polynomial-time computable.

**Deviation:** [PS10] assumes a standard encoding with an implicit efficient universal
simulation; here the simulation cost of the arbitrary effective scheme `c` is made explicit
through this hypothesis (no bound is known for `Turing.exists_effectiveMachineCode`). -/
def CanonizerExp (c : EffectiveMachineCode) : Prop :=
  ∃ A B : ℕ, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)

/-- **Some effective encoding scheme has a canonizer at most exponential in the code length**
[PS10, §2.13] (run-3 audit P3-4, formerly an open problem): `∃ c, CanonizerExp c`, i.e. some
`c : EffectiveMachineCode` and `A, B` with `c.canonizerTime k ≤ A · 2^{B k}` for every `k`. So the
hypothesis `CanonizerExp c` of `theorem_63_1` is satisfiable; the headlines of this file stay
stated for an arbitrary scheme satisfying it (plan D11).

**Proof sketch.** The scheme is the machine library's one-tape code: serialization
`Turing.CodeTM.serialize`, parser `Turing.codeDecode`, and the canonizer of
`Turing.MachineFormat.exists_polyCanonizer` at `Turing.oneTapeMachineFormat`, which runs in time
`d · (n + 1)^d` on every input, malformed codes included
(`exists_effectiveMachineCode_canonizerTime_le`, in `Universal/Canonizer`). Since `k + 1 ≤ 2^k`,
`d · (k + 1)^d ≤ d · 2^{d k}`, so `A = B = d`. -/
theorem exists_canonizerExp : ∃ c : EffectiveMachineCode, CanonizerExp c := by
  obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le
  exact ⟨c, d, d, h⟩

/-- **The coefficient is polynomial on codes of logarithmic length.** If `c` has an
exponential canonizer, there is a syntactic polynomial `p` with
`univCoeff c α ≤ p(n)` for every `n` and every code `α` of length `⌊log₂ n⌋`.

**Proof sketch.** With `A, B` from `CanonizerExp c` and `k = |α| = ⌊log₂ n⌋`:
`canonizerTime k ≤ A · 2^{Bk} = A (2^k)^B ≤ A (n + 1)^B` (`Nat.pow_log_le_self`, `pow_mul`);
`|serialize| ≤ canonizerTime k` (`length_serialize_decode_le`); `numStates + 1 ≤ |serialize|`
(`numStates_add_one_le_length_serialize`), so `|bits numStates| ≤ numStates`
(`Turing.length_bits_le_self`) and `q₀.val ≤ numStates` are below `|serialize|`;
`Turing.universalBlockBound c α = 3|serialize| + 5(numStates + 1) + 20`; and `3k ≤ 3n`
(`Nat.log_le_self`). Collecting, `univCoeff c α ≤ 3n + 14 A (n + 1)^B + 60`. -/
theorem exists_univCoeff_le (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    ∃ p : PolyExpr, ∀ (n : ℕ) (α : List Bool), α.length = Nat.log 2 n →
      univCoeff c α ≤ p.eval n := by
  obtain ⟨A, B, hAB⟩ := hc
  refine ⟨.add (.add (.mul (.const 3) .var)
    (.mul (.const 14) (.mul (.const A) (.pow (.add .var (.const 1)) B)))) (.const 60),
    fun n α hα => ?_⟩
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_pow]
  have h2k : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  have hT : c.canonizerTime α.length ≤ A * (n + 1) ^ B := by
    calc c.canonizerTime α.length ≤ A * 2 ^ (B * α.length) := hAB _
      _ = A * (2 ^ Nat.log 2 n) ^ B := by rw [hα, mul_comm B, pow_mul]
      _ ≤ A * (n + 1) ^ B := Nat.mul_le_mul_left A (Nat.pow_le_pow_left h2k B)
  have hS := length_serialize_decode_le c α
  have hN := numStates_add_one_le_length_serialize (c.decode α)
  have hb := length_bits_le_self (c.decode α).numStates
  have hq := (c.decode α).tm.q₀.isLt
  have hk : α.length ≤ n := hα ▸ Nat.log_le_self 2 n
  simp only [univCoeff, universalBlockBound_def]
  omega

/-! ## The evaluator machine of `f_universal` -/

/-- **The code field is polynomial-time**: the typed cut `polyTimeComputable_pairTakePoly var`
on `⟨(bits |y|).tail, y⟩` keeps the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univCode : PolyTimeComputable univCode := by
  have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univCode, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- **The argument field is polynomial-time**: the typed cut `polyTimeComputable_pairDropPoly var`
on `⟨(bits |y|).tail, y⟩` drops the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univArg : PolyTimeComputable univArg := by
  have h := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univArg, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- The input `⟨⟨bits ((|y| + 1)³), univCode y⟩, univArg y⟩` of the clocked universal machine
is polynomial-time in `y`. -/
theorem polyTimeComputable_univInput :
    PolyTimeComputable fun y : List Bool =>
      pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y) :=
  (polyTimeComputable_univBudget.pairEncode polyTimeComputable_univCode).pairEncode
    polyTimeComputable_univArg

/-- **The clocked simulation is polynomial-time** for a scheme with an exponential
canonizer: `y ↦ clockedAnswer c (univCode y) (univArg y) ((|y| + 1)³)`.

**Proof sketch.** `Turing.FinTM.exists_comp_on_image` with the machine of
`polyTimeComputable_univInput` (time `C (n + 1)^d`) and the universal machine `U` of
`exists_univ_computes c`, which on the image maps `⟨⟨bits t, univCode y⟩, univArg y⟩` to the
clocked answer within `univCoeff c (univCode y) · (t + 1)² ≤ p(|y|) · ((|y| + 1)³ + 1)²`
(`exists_univCoeff_le` at `n := |y|`, `length_univCode`, `ComputesInTime.mono`); the total
`2 C (n + 1)^d + p(n)((n + 1)³ + 1)² + 2` is a syntactic polynomial, majorised in normal form
by `PolyExpr.eval_le`. -/
theorem polyTimeComputable_clockedAnswer (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable fun y : List Bool =>
      clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3) := by
  obtain ⟨M, C, d, hM⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_univInput
  obtain ⟨U, hU⟩ := exists_univ_computes c
  obtain ⟨p, hp⟩ := exists_univCoeff_le c hc
  have hU' : ∀ y : List Bool, U.ComputesInTime
      (pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y))
      (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))
      (p.eval y.length * ((y.length + 1) ^ 3 + 1) ^ 2) := fun y =>
    (hU _ _ _).mono (Nat.mul_le_mul_right _ (hp y.length _ (length_univCode y)))
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M U _ _ (fun n => C * (n + 1) ^ d)
    (fun n => p.eval n * ((n + 1) ^ 3 + 1) ^ 2) hM hU'
  obtain ⟨C', c', hC'⟩ := PolyExpr.eval_le (.add (.add (.mul (.const 2) (.normal C d))
    (.mul p (.pow (.add (.pow (.add .var (.const 1)) 3) (.const 1)) 2))) (.const 2))
  refine (polyTimeComputable_iff _).2 ⟨N, C', c', (FinTM.computesFunInTime_iff _ _ _).2 fun y =>
    ((FinTM.computesFunInTime_iff _ _ _).1 hN y).mono ?_⟩
  have h := hC' y.length
  simpa [PolyExpr.eval_normal] using h

/-- **`f_universal` as a string function is polynomial-time** for a scheme with an
exponential canonizer: `⟨univCode y, clockedAnswer …⟩` by `PolyTimeComputable.pairEncode`. -/
theorem polyTimeComputable_fUniversalStr (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable (fUniversalStr c) :=
  polyTimeComputable_univCode.pairEncode (polyTimeComputable_clockedAnswer c hc)

/-- **`f_universal` is easy to compute** [PS10, Algorithm 64.2: "clearly `f_universal` is
computable in time `O(|y|³)`"]: for a scheme with an exponential canonizer, `fUniversal c` is
`Easy`.

**Deviation:** the evaluator is a deterministic polynomial-time machine on `⟨1^n, y⟩` (D3); the
time is `p(n) · ((n+1)³ + 1)²` with the coefficient polynomial `p` of `exists_univCoeff_le`,
not the text's `O(|y|³)` (the simulation overhead of `Turing.timed_universal_concrete` is
quadratic in the budget).

**Proof sketch.** The evaluator on `z = ⟨1^n, y⟩` (`y := pairSndD z`) is built in the FP
calculus of `ClassNP/PolyTimePairing.lean` plus one timed composition: (1) *the split at
`⌊log₂ |y|⌋`:* `Nat.bits |y|` (`Turing.FinTM.computesFunInTime_lengthBits`) has
`⌊log₂ |y|⌋ + 1` bits; its tail (`List.drop 1`, linear) paired with `y` and split by
`Turing.FinTM.computesFunInTime_pairSplitAt` gives `⟨univCode y, univArg y⟩`; (2) *the budget*
`Nat.bits ((|y| + 1)³)` by `Turing.FinTM.computesFunInTime_polyBits 1 3`; (3) *the universal
input* `g y := ⟨⟨bits t, univCode y⟩, univArg y⟩` by `PolyTimeComputable.pairEncode`; (4) *the
simulation:* `Turing.FinTM.exists_comp_on_image` with `M` computing `g` in time `T₁` and `U`
from `exists_univ_computes c` computing `clockedAnswer c (univCode y) (univArg y) t` on the image
within `T₂ |z| := p(|z|) · ((|z| + 1)³ + 1)²`, where `univCoeff c (univCode y) ≤ p(|y|) ≤ p(|z|)`
by `exists_univCoeff_le` (at `n := |y|`, `length_univCode`) and `PolyExpr.eval_mono`; (5) *the
output* `pairEncode (univCode y) answer` by `PolyTimeComputable.pairEncode`, which is
`fUniversalStr c y`; (6) *the padding* `(w ++ 0^{p(n)}).take (p(n))` with
`0^{p(n)} = zipWith xor 1^{p(n)} 1^{p(n)}` (`Complexity.polyTimeComputable_unaryPoly univOutLen`
on `1^n = pairFstD z`, `Complexity.polyTimeComputable_pairXor`), `PolyTimeComputable.append`,
`Complexity.polyTimeComputable_pairTakePoly univOutLen` on `⟨1^n, w ++ 0^{p(n)}⟩`. Correctness
on `advInput n (List.ofFn x)` is `ofFn_fUniversal_f` with `List.length_ofFn`,
`Turing.pairDecode_pairEncode` and `List.length_replicate`. -/
theorem fUniversal_easy (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    (fUniversal c).Easy := by
  have hF : PolyTimeComputable fun z =>
      padStr univOutLen (pairFstD z) (fUniversalStr c (pairSndD z)) := by
    have h := PolyTimeComputable.comp' (polyTimeComputable_padStr univOutLen)
      (polyTimeComputable_pairFstD.pairEncode
        (PolyTimeComputable.comp' (polyTimeComputable_fUniversalStr c hc)
            polyTimeComputable_pairSndD))
    convert h using 1
    funext z
    simp
  refine (FunFamily.easy_iff _).2 ⟨_, hF, fun n x => ?_⟩
  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [ofFn_fUniversal_f]
  simp [padStr_eq]

/-! ## Lemma 64.3: a strong one-way function computable in quadratic time -/

/-- `𝓕` is *computable in quadratic time by a coded machine*: some `Turing.CodeTM` (one work
tape, binary alphabet — the machines the universal machine interprets) computes
`f n x` from the bare input `x` within `c₀ (|x| + 1)²` steps. This is "`g'` is computable in
time `O(n²)`" of [PS10, Lemma 64.3], at the level of the coded machines of
[PS10, Algorithm 64.2]. -/
def FunFamily.QuadraticCode (𝓕 : FunFamily) : Prop :=
  ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓕.f n x))
      (c₀ * (𝓕.inLen.eval n + 1) ^ 2)

/-- **Strong one-way functions computable in quadratic time** [PS10, Lemma 64.3]: if there is
a strong one-way function, there is a strong one-way function `g'` with parameter = input
length (`inLen = var`) computable by a coded machine in time `c₀ (n + 1)²` on the bare input.

**Deviation:** the text defines `g'(⟨a, b⟩) = ⟨a, g(b)⟩` on lengths `m = n^c` only and
leaves the recovery of `n` from `m` implicit; the formal `g'` is defined at every length `m`
with `ν(m) := max {n ≤ m : n^d ≤ m}` recovered from the input length for a fixed
dominating degree d. The output `a ++ g_{ν m}(b)` is padded with `false` to the syntactic
length `2·var` and is truncated on smaller parameters before domination applies.

Repair (run-3 audit P3-3): the sketch's family is `𝓖 := ⟨var, mul (const 2) var, g'⟩`, not
`⟨var, add var outLen, g'⟩` — padding to `m + outLen(m)` bits is not computable within the
quadratic one-tape budget when `deg outLen ≥ 2`; the raw output has at most `2m` bits. The
"non-constant input length" sub-lemma is unnecessary (`P` is strictly increasing because of its
summand `n`). Statement unchanged.

**Proof sketch.** Extract an evaluator F of the strong one-way family and
its polynomial running time. Choose a fixed degree d that eventually dominates
the input length, output length and the cost of F on an encoded parameter
and input. The family PadQuad.family uses the recovered parameter
ν(m) = max {n ≤ m : n^d ≤ m}. Its output is the retained suffix followed by
F on the encoded parameter and data prefix, padded and truncated to twice m.

The padding inverter samples the retained suffix and uses the supplied
padded-family inverter at a length selected as advice. Equality of padded
outputs gives equality of the retained suffix and equality of the original
family's outputs once the dominating bound holds. This proves the padded
family's strong one-wayness.

For time, the binary parameter search followed by unary emission computes
the shifted root in linear multitape time. The sharp unary polynomial
evaluator and the source call are charged at their actual short arguments.
The pairing, splitting and padding stages have linear overhead. The existing
one-work-tape binary conversion squares that linear bound, and the code
representation transports the runs. This is PadQuad.exists_family.
-/
theorem lemma_64_3 (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode :=
  PadQuad.exists_family h

/-! ## Claims 65.1 and 65.2: the counting steps -/

/-- **`PickG`** [PS10, p. 65, Claim 65.1 of the inventory]: for a uniform `y ∈ {0,1}^n` and any
fixed code `code` of `⌊log₂ n⌋` bits (the description of `M_g` padded to that length), the
first `⌊log₂ n⌋` bits of `y` equal `code` with probability `2^{-⌊log₂ n⌋} ≥ 1/n`.

**Proof sketch.** Split `y` as `(prefix, rest)` by `Fin.appendEquiv` (`uprob_comp_equiv`); the
event is a point event on the first component (`uprob_fst`, `OneWay.uprob_eq_one_div_card`),
of probability `1/2^k`, and `2^k ≤ n` (`Nat.pow_log_le_self`). -/
theorem claim_65_1 (n : ℕ) (hn : n ≠ 0) (code : Fin (Nat.log 2 n) → Bool) :
    1 / (n : ℝ) ≤ uprob fun y : Fin n → Bool =>
      (List.ofFn y).take (Nat.log 2 n) = List.ofFn code := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have hP : (fun z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) =>
      (List.ofFn (e z)).take (Nat.log 2 n) = List.ofFn code) = fun z => z.1 = code := by
    funext z
    have h1 : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
    rw [h1, List.take_left' (List.length_ofFn (f := z.1)), List.ofFn_inj]
  rw [hP, uprob_fst (fun a : Fin (Nat.log 2 n) → Bool => a = code), OneWay.uprob_eq_one_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  have hpos : (0 : ℝ) < ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le hpos h2

/-- **The union bound** [PS10, p. 65, the displayed inequalities]: if `A` inverts with
probability more than `1 - 1/n³` (`Invert`) and the code field is `M_g` with probability at
least `1/n` (`PickG`), then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + (1 - 1/n)`, i.e.
`Pr[Invert ∧ PickG] ≥ 1/n - 1/n³` (which is `≥ 1/n³` for `n ≥ 2`, the text's bound).

**Proof sketch.** `uprob_or_le` on the complements and `uprob_not`. -/
theorem claim_65_2 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Invert PickG : Ω → Prop) (n : ℕ)
    (hI : 1 - 1 / (n : ℝ) ^ 3 < uprob Invert) (hP : 1 / (n : ℝ) ≤ uprob PickG) :
    1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 ≤ uprob fun w => Invert w ∧ PickG w := by
  have h1 : uprob (fun w => ¬ (Invert w ∧ PickG w)) ≤
      uprob (fun w => ¬ Invert w) + uprob (fun w => ¬ PickG w) := by
    calc uprob (fun w => ¬ (Invert w ∧ PickG w))
        = uprob (fun w => ¬ Invert w ∨ ¬ PickG w) := by
          congr 1
          funext w
          exact propext not_and_or
      _ ≤ _ := uprob_or_le _ _
  rw [uprob_not, uprob_not, uprob_not] at h1
  linarith

/-- The probability of an event on the fibre over a fixed first coordinate is at most
`|α|` times its probability on the product: `Pr_b[E(a, b)] ≤ |α| · Pr_{(a', b)}[E]`
(Fubini, `uprob_prod`, one term of the average). -/
theorem uprob_fiber_le_card_mul {α β : Type*} [Fintype α] [Fintype β] (E : α × β → Prop)
    (a : α) : uprob (fun b => E (a, b)) ≤ Fintype.card α * uprob E := by
  haveI : Nonempty α := ⟨a⟩
  rw [uprob_prod, uexp_def]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard]
  exact Finset.single_le_sum (f := fun a' => uprob fun b => E (a', b))
    (fun a' _ => uprob_nonneg _) (Finset.mem_univ a)

/-- **The conditional form of the union bound** (the form the reduction of
[PS10, Theorem 63.1] uses): if `Invert` has probability at least `1 - 1/n³` on the product
`α × β` with `|α| ≤ n` (the code field, `|α| = 2^{⌊log₂ n⌋}`), then conditioned on the code
field being `a` — i.e. on the fibre — `Invert` has probability at least `1 - 1/n²`.

**Proof sketch.** `uprob_fiber_le_card_mul` for the complement: `Pr_b[¬Invert(a, b)] ≤ |α| ·
Pr[¬Invert] ≤ n · (1/n³) = 1/n²`, then `uprob_not`. -/
theorem claim_65_2_cond {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (Invert : α × β → Prop) (a : α) (n : ℕ) (hn : 0 < n) (hα : Fintype.card α ≤ n)
    (hI : 1 - 1 / (n : ℝ) ^ 3 ≤ uprob Invert) :
    1 - 1 / (n : ℝ) ^ 2 ≤ uprob fun b => Invert (a, b) := by
  haveI : Nonempty α := ⟨a⟩
  have h1 := uprob_fiber_le_card_mul (fun z => ¬ Invert z) a
  rw [uprob_not, uprob_not] at h1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have h2 : (Fintype.card α : ℝ) * (1 - uprob Invert) ≤ n * (1 / (n : ℝ) ^ 3) :=
    mul_le_mul hcard (by linarith) (by linarith [uprob_le_one Invert]) (by positivity)
  have h3 : (n : ℝ) * (1 / (n : ℝ) ^ 3) = 1 / (n : ℝ) ^ 2 := by
    field_simp
  linarith

/-! ## Theorem 63.1: the universal one-way function -/

/-! ### The reduction of Theorem 63.1 -/

/-- **Evaluation on the fibre of the code field** [PS10, Theorem 63.1,
"`f_universal(⟨M_g, x⟩) = ⟨M_g, g(x)⟩`"]: for a code of `⌊log₂ n⌋` bits decoding to the
quadratic machine `M_g` of `g` and an argument `x` of `n − ⌊log₂ n⌋` bits,
`fUniversalStr c (code ++ x) = ⟨code, true :: g(x)⟩`.

**Proof sketch.** `fUniversalStr_append_of_computesInTime` with `|code| + |x| = n`: the code
field is `code` (its length is `⌊log₂ n⌋`), the decoded machine is `M_g` (`hdec`), which
computes `g(x)` within `c₀ (|x| + 1)² ≤ (n + 1)³` (`quadratic_le_cubic`). -/
private theorem fUniversalStr_ofFn_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) :
    fUniversalStr c (List.ofFn y) = pairEncode code (true :: List.ofFn (g _ x)) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hsum : code.length + (List.ofFn x).length = n := by
    rw [hcode, List.length_ofFn]
    omega
  have hα : code.length = Nat.log 2 (code.length + (List.ofFn x).length) := by
    rw [hsum, hcode]
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g _ x))
      (c₀ * ((n - Nat.log 2 n) + 1) ^ 2) := by
    rw [hdec]
    exact hMg _ x
  rw [hy]
  exact fUniversalStr_append_of_computesInTime c hα hM
    (by rw [hsum]; exact quadratic_le_cubic (by omega) hc₀)

/-- The padded encoding of `f_universal (code ++ x)` is the padding evaluator on
`⟨code, true :: g(x)⟩`: the pre-processing of the reduction produces exactly the challenge
`A` expects (`ofFn_fUniversal_f`, `fUniversalStr_ofFn_eq`). -/
private theorem padStr_eq_ofFn_fUniversal_f (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool)
    (y : Fin ((fUniversal c).inLen.eval n) → Bool) (hy : List.ofFn y = code ++ List.ofFn x) :
    padStr univOutLen (List.replicate n true) (pairEncode code (true :: List.ofFn (g _ x))) =
      List.ofFn ((fUniversal c).f n y) := by
  obtain ⟨y₀, hy₀⟩ := exists_ofFn_eq_of_length (m := n) (w := List.ofFn y)
    (by rw [List.length_ofFn, fUniversal_inLen_eval])
  rw [ofFn_fUniversal_f, ← hy₀,
    fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y₀ (hy₀.trans hy), padStr_eq,
    List.length_replicate]

/-- **Inverses on the fibre** [PS10, Theorem 63.1, "`A` outputs `⟨M_g, x'⟩` with
`g(x') = g(x)`"]: if `y'` has the same `f_universal`-value as `y = code ++ x` (code of
`⌊log₂ n⌋` bits decoding to `M_g`), then the argument field of `y'` is some `x'` with
`g(x') = g(x)`.

**Proof sketch.** Both padded outputs are `⟨·, ·⟩ ++ 0^*` with first components of
`⌊log₂ n⌋` bits (`length_univCode`), so `pairEncode_append_eq` gives `univCode y' = code` and
equal padded answers; the answer on `y'` is `clockedAnswer c code x' ((n+1)³) = true :: g(x')`
(`clockedAnswer_eq_cons_of_computesInTime`, budget `quadratic_le_cubic`), and the two
`g`-values have the same length, so they agree (`List.append_inj_left`, `List.ofFn_injective`). -/
private theorem exists_preimage_of_fUniversal_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool)
    (y y' : Fin ((fUniversal c).inLen.eval n) → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) (h : (fUniversal c).f n y' = (fUniversal c).f n y) :
    ∃ x' : Fin (n - Nat.log 2 n) → Bool,
      List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  obtain ⟨x', hx'⟩ := exists_ofFn_eq_of_length (m := n - Nat.log 2 n)
    (w := univArg (List.ofFn y')) (by simp [fUniversal_inLen_eval])
  refine ⟨x', hx', ?_⟩
  obtain ⟨y₀, hy₀⟩ := exists_ofFn_eq_of_length (m := n) (w := List.ofFn y)
    (by rw [List.length_ofFn, fUniversal_inLen_eval])
  have h1 := congrArg List.ofFn h
  rw [ofFn_fUniversal_f, ofFn_fUniversal_f,
    take_append_replicate_of_le
      (by simpa [fUniversal_inLen_eval] using length_fUniversalStr_le c (List.ofFn y')),
    take_append_replicate_of_le
      (by simpa [fUniversal_inLen_eval] using length_fUniversalStr_le c (List.ofFn y)),
    ← hy₀, fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y₀ (hy₀.trans hy)] at h1
  unfold fUniversalStr at h1
  simp only [List.length_ofFn] at h1
  rw [show ((fUniversal c).inLen.eval n + 1) ^ 3 = (n + 1) ^ 3 by rw [fUniversal_inLen_eval]] at h1
  obtain ⟨hcd, hans⟩ := pairEncode_append_eq (by simp [hcode, fUniversal_inLen_eval]) h1
  rw [hcd, ← hx'] at hans
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x') (List.ofFn (g _ x'))
      ((n + 1) ^ 3) := by
    rw [hdec]
    exact (hMg _ x').mono (quadratic_le_cubic (by omega) hc₀)
  rw [clockedAnswer_eq_cons_of_computesInTime c hM, List.cons_append, List.cons_append] at hans
  exact List.ofFn_injective (List.append_inj_left (List.tail_eq_of_cons_eq hans) (by simp))

/-- **The reduction wins on the fibre** [PS10, Theorem 63.1, the displayed bound
`Pr[Invert ∧ PickG]`]: if `A` inverts `f_universal` at parameter `n` with probability more
than `1 − 1/n³`, and `B` at parameter `m = n − ⌊log₂ n⌋` runs `A` on the padded
`⟨code, true :: y⟩` and returns the argument field of its answer, then `B` inverts `g` at `m`
with probability at least `1 − 1/n²`.

**Proof sketch.** Split `{0,1}^n ≃ {0,1}^{⌊log₂ n⌋} × {0,1}^m` (`Fin.appendEquiv`); the
inversion event of `A` on the product has probability `invProbAt A n`
(`invProbAt_eq_uprob`, `uprob_comp_equiv`), so `claim_65_2_cond` with
`2^{⌊log₂ n⌋} ≤ n` (`OneWay.card_log_bits_le`) gives probability `≥ 1 − 1/n²` on the fibre of
the code. On that fibre `B`'s challenge is `A`'s (`padStr_eq_ofFn_fUniversal_f`), `B`'s coins
are `A`'s followed by unread coins (`uprob_comp_equiv`, `uprob_fst`), and `A`'s success gives
`B`'s by `exists_preimage_of_fUniversal_eq` (`uprob_mono`). -/
private theorem invProbAt_reduction_ge (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    (A B : NUPPT) {n : ℕ} (hn : 2 ≤ n) {code : List Bool} (hcode : code.length = Nat.log 2 n)
    (hdec : c.decode code = Mg) (hc₀ : c₀ ≤ n + 1)
    (hBc : A.coinLen n ≤ B.coinLen (n - Nat.log 2 n))
    (hB : ∀ y (r : List Bool), B.runAtL (n - Nat.log 2 n) y r =
      univArg (A.runAtL n (padStr univOutLen (List.replicate n true) (pairEncode code (true :: y)))
        (r.take (A.coinLen n))))
    (hA : 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n) :
    1 - 1 / (n : ℝ) ^ 2 ≤ (⟨.var, L, g⟩ : FunFamily).invProbAt B (n - Nat.log 2 n) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  have hofn : ∀ z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool),
      List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
    intro z
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
  obtain ⟨cf, hcf⟩ := exists_ofFn_eq_of_length (m := Nat.log 2 n) hcode
  let Invert : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) → Prop :=
    fun w => ∃ y',
      A.runAt n (List.ofFn ((fUniversal c).f n (e (w.1, w.2.1)))) w.2.2 = List.ofFn y' ∧
      (fUniversal c).f n y' = (fUniversal c).f n (e (w.1, w.2.1))
  have hInv : uprob Invert = (fUniversal c).invProbAt A n := by
    rw [FunFamily.invProbAt_eq_uprob]
    let e' : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ≃
        (Fin ((fUniversal c).inLen.eval n) → Bool) × A.Coins n :=
      (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr e (Equiv.refl _))
    rw [← uprob_comp_equiv e']
    exact OneWay.uprob_congr fun w => Iff.rfl
  have hfib := claim_65_2_cond Invert cf n (by omega) (OneWay.card_log_bits_le (by omega))
    (by rw [hInv]; exact hA.le)
  rw [FunFamily.invProbAt_eq_uprob]
  have hlen : B.coinLen (n - Nat.log 2 n) =
      A.coinLen n + (B.coinLen (n - Nat.log 2 n) - A.coinLen n) := by omega
  let e₂ : ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ×
      (Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool) ≃
      (Fin (n - Nat.log 2 n) → Bool) × B.Coins (n - Nat.log 2 n) :=
    (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))))
  rw [← uprob_comp_equiv e₂]
  refine hfib.trans ?_
  rw [← uprob_fst (β := Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool)
    (fun b : (Fin (n - Nat.log 2 n) → Bool) × A.Coins n => Invert (cf, b))]
  refine uprob_mono fun w hw => ?_
  obtain ⟨y', hy', hfy'⟩ := hw
  have hcoins : List.ofFn (e₂ w).2 = List.ofFn w.1.2 ++ List.ofFn w.2 := by
    show List.ofFn ((Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))
      (Fin.appendEquiv _ _ (w.1.2, w.2))) = _
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm (Fin.append w.1.2 w.2)).symm
  have hy : List.ofFn (e (cf, w.1.1)) = code ++ List.ofFn w.1.1 := by rw [hofn, hcf]
  show ∃ x', B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 = List.ofFn x' ∧
    g _ x' = g _ w.1.1
  have hBrun : B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 =
      univArg (List.ofFn y') := by
    rw [NUPPT.runAt_eq, hB, hcoins, List.take_left' (List.length_ofFn (f := w.1.2)),
      ← NUPPT.runAt_eq,
      padStr_eq_ofFn_fUniversal_f c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) hy, hy']
  obtain ⟨x', hx', hgx'⟩ :=
    exists_preimage_of_fUniversal_eq c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) y' hy hfy'
  exact ⟨x', by rw [hBrun, hx'], hgx'⟩

/-- **`f_universal` is hard to invert with `q(n) = n³`** [PS10, Theorem 63.1, proof of weak
one-wayness]: for a scheme `c` with an exponential canonizer, if some strong one-way function
`𝓖` with `inLen = var` is computable in quadratic time by a coded machine (the output of
`lemma_64_3`), every non-uniform PPT inverts `fUniversal c` with probability at most
`1 - 1/n³` for all large `n`.

**Deviation:** the hypothesis is the conclusion of Lemma 64.3 (`theorem_63_1` composes the
two); `q(n) = n³` is literal; `Invert` is `invProbAt_eq_uprob`'s event with the inverse
decoded as an `n`-bit string (D5).

**Proof sketch.** Let `M_g, c₀` be the coded machine of `hG.2.2`, `α₀ := c.encode M_g`, and
suppose `A` inverts with probability `> 1 - 1/n³` for infinitely many `n`. Fix such an
`n ≥ max c₀ 2^{|α₀|+1}`, `k := ⌊log₂ n⌋ ≥ |α₀|`, `m := n - k`, `code := α₀ ++ 1^{k - |α₀|}`
(`c.decode code = M_g` by `Turing.MachineCode.decode_encode_pad`). *Evaluation on `PickG`:*
for `y = code ++ x`, `|x| = m`, `fUniversalStr_append_of_computesInTime` with `hG.2.2` at `m`
and `c₀ (m + 1)² ≤ (n + 1)³` gives `fUniversalStr c y = pairEncode code (true :: ofFn (g m x))`,
`ofFn_fUniversal_f` the padded encoding. *Conditioning:* split `{0,1}^n ≃ {0,1}^k × {0,1}^m`
(`Fin.appendEquiv`, `uprob_comp_equiv`, as in `claim_65_1`); `claim_65_2_cond` with
`2^k ≤ n` (`OneWay.card_log_bits_le`) gives `Pr_{x, r}[Invert(code ++ x, r)] ≥ 1 - 1/n²`.
*Inverses on the fibre:* an answer `y' = code' ++ x'` with equal padded outputs has
`code' = code` (the first `2k + 2` bits are the doubled code and the separator,
`Turing.pairEncode`, `List.take` of `ofFn_fUniversal_f`), then
`ofFn (g m x') = ofFn (g m x)` (equal lengths `1 + outLen m`), so `g m x' = g m x`
(`List.ofFn_injective`). *The reduction `B`* for `𝓖` at parameter `m`: advice `⟨1^n, code⟩`
with `n ≤ 2(m + 1)` (`2⌊log₂ n⌋ ≤ n + 2`), by `NUPPT.exists_reparam_advice A φ
(mul (const 2) (add var (const 1)))` with `φ m := n` on the infinitely many `m = n - ⌊log₂ n⌋`
with `n` good (`0` elsewhere; fibres of `n ↦ n - ⌊log₂ n⌋` have at most two elements),
composed (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`) with the pre-processing
`z ↦ (pairEncode code (true :: z) ++ 0^{univOutLen n}).take (univOutLen n)` and the
post-processing `univArg` (the split of `fUniversal_easy` (1)); extra coins unread
(`List.take`, `uprob_fst` on `Fin.appendEquiv`). *Functional identity:*
`B.inverter m _ _ (g m x) r = some x'` iff `A.runAt n (ofFn ((fUniversal c).f n (code ++ x))) r'
= ofFn (code ++ x')` (`NUPPT.inverter_eq_some_iff`, `decodeFin_ofFn`, `univArg_append`), so
`𝓖.invProbAt B m ≥ 1 - 1/n² ≥ 1/2` (`invProbAt_eq_uprob`, `uprob_mono`). *Conclusion:* for
infinitely many `m` (unbounded, `m ≥ n/2`), so `fun m => 𝓖.invProbAt B m` is not negligible
(`not_negligible_iff` with `c = 1`), contradicting `hG.2.1.hard B`. -/
theorem fUniversal_hard (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) (A : NUPPT) :
    ∃ n₀, ∀ n ≥ n₀, (fUniversal c).invProbAt A n ≤ 1 - 1 / (n : ℝ) ^ 3 := by
  classical
  obtain ⟨⟨ℓ, L, g⟩, hℓ, hsow, Mg, c₀, hMg⟩ := hG
  dsimp only at hℓ
  subst hℓ
  by_contra hcon
  push_neg at hcon
  -- the good parameters, the code of `M_g` padded to `⌊log₂ n⌋` bits, the parameter change
  set α₀ := c.encode Mg with hα₀
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ α₀.length = K := ⟨_, rfl⟩
  set N₀ := K + c₀ + 4 with hN₀
  let good : ℕ → Prop := fun n => N₀ ≤ n ∧ 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n
  let φ : ℕ → ℕ := fun m => if h : ∃ n, good n ∧ n - Nat.log 2 n = m then h.choose else 0
  have hφ : ∀ m, φ m ≤ (PolyExpr.mul (.const 2) .var).eval m := by
    intro m
    simp only [φ, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    split_ifs with h
    · have h1 := h.choose_spec.2
      have h2 := two_mul_log_two_le h.choose
      omega
    · exact Nat.zero_le _
  have hφ_spec : ∀ m, (∃ n, good n ∧ n - Nat.log 2 n = m) →
      good (φ m) ∧ φ m - Nat.log 2 (φ m) = m := by
    intro m h
    simp only [φ, dif_pos h]
    exact h.choose_spec
  let code : ℕ → List Bool := fun n => α₀ ++ List.replicate (Nat.log 2 n - α₀.length) true
  have hcode_len : ∀ n, N₀ ≤ n → (code n).length = Nat.log 2 n := by
    intro n hn
    have : α₀.length ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by rw [hK]; omega)
    simp only [code, List.length_append, List.length_replicate]
    omega
  have hcode_dec : ∀ n, c.decode (code n) = Mg := fun n => c.decode_encode_pad Mg _
  have hcode_le : ∀ n, (code n).length ≤ α₀.length + n := by
    intro n
    have := Nat.log_le_self 2 n
    simp only [code, List.length_append, List.length_replicate]
    omega
  -- the reduction `B`
  let β : ℕ → List Bool := fun m => pairEncode (List.replicate (φ m) true) (code (φ m))
  have hβ : ∀ m, (β m).length ≤
      (PolyExpr.add (.add (.mul (.const 6) .var) (.const 2)) (.const α₀.length)).eval m := by
    intro m
    have h1 := hφ m
    have h2 := hcode_le (φ m)
    simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var] at h1
    simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hpre : PolyTimeComputable fun w => padStr univOutLen (pairFstD (pairFstD w))
      (pairEncode (pairSndD (pairFstD w)) (true :: pairSndD w)) := by
    have h := PolyTimeComputable.comp' (polyTimeComputable_padStr univOutLen)
      ((PolyTimeComputable.comp' polyTimeComputable_pairFstD polyTimeComputable_pairFstD).pairEncode
        ((PolyTimeComputable.comp' polyTimeComputable_pairSndD
            polyTimeComputable_pairFstD).pairEncode
          (PolyTimeComputable.comp' (StateLoop.cons_poly true) polyTimeComputable_pairSndD)))
    convert h using 1
    funext w
    simp
  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_pre_post φ _ hφ β _ hβ hpre polyTimeComputable_univArg
  have hB' : ∀ m y r, B.runAtL m y r = univArg (A.runAtL (φ m)
      (padStr univOutLen (List.replicate (φ m) true) (pairEncode (code (φ m)) (true :: y)))
      (r.take (A.coinLen (φ m)))) := by
    intro m y r
    rw [hB]
    simp [β]
  -- `B` inverts `g` with probability `≥ 1/2` infinitely often, contradicting its one-wayness
  refine (not_negligible_iff.mpr ⟨1, fun m₀ => ?_⟩) (hsow.hard B)
  obtain ⟨n, hn, hgood⟩ := hcon (max (2 * m₀) N₀)
  have hNn : N₀ ≤ n := le_of_max_le_right hn
  have hmn : 2 * m₀ ≤ n := le_of_max_le_left hn
  have hgoodn : good n := ⟨hNn, hgood⟩
  obtain ⟨hgood', hφm⟩ := hφ_spec (n - Nat.log 2 n) ⟨n, hgoodn, rfl⟩
  have hlog := two_mul_log_two_le n
  have hm₀ : m₀ ≤ n - Nat.log 2 n := by omega
  refine ⟨n - Nat.log 2 n, hm₀, ?_⟩
  have hn'N : N₀ ≤ φ (n - Nat.log 2 n) := hgood'.1
  have hcoins : A.coinLen (φ (n - Nat.log 2 n)) ≤
      B.coinLen (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) := by
    rw [hφm]
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst]
    exact A.coins.eval_mono (hφ _)
  have hrun : ∀ y (r : List Bool),
      B.runAtL (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) y r =
      univArg (A.runAtL (φ (n - Nat.log 2 n)) (padStr univOutLen
        (List.replicate (φ (n - Nat.log 2 n)) true)
        (pairEncode (code (φ (n - Nat.log 2 n))) (true :: y)))
        (r.take (A.coinLen (φ (n - Nat.log 2 n))))) := by
    intro y r
    rw [hφm]
    exact hB' _ y r
  have hkey := invProbAt_reduction_ge c g Mg c₀ hMg A B (n := φ (n - Nat.log 2 n)) (by omega)
    (hcode_len _ hn'N) (hcode_dec _) (by omega) hcoins hrun hgood'.2
  rw [hφm] at hkey
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  refine le_trans ?_ hkey
  have hm2 : (2 : ℝ) ≤ ((n - Nat.log 2 n : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n - Nat.log 2 n by omega)
  have hn2 : (2 : ℝ) ≤ ((φ (n - Nat.log 2 n) : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ φ (n - Nat.log 2 n) by omega)
  have h1 : 1 / ((n - Nat.log 2 n : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2
  have h2 : 1 / ((φ (n - Nat.log 2 n) : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  simp only [pow_one]
  linarith

/-- **`f_universal` is weakly one-way** [PS10, Theorem 63.1, "we claim that this function is
weakly one-way"] with the polynomial `q(n) = (n + 1)³`, for a scheme with an exponential
canonizer, given a quadratic-time strong one-way function (`lemma_64_3`).

**Deviation:** `WeakOneWay` requires `0 < q(n)` at every `n`, so the text's `q(n) = n³` is
replaced by `(n + 1)³ ≥ n³` (the bound `1 - 1/n³ ≤ 1 - 1/(n+1)³` of `fUniversal_hard` is the
stronger one).

**Proof sketch.** `fUniversal_easy` and `fUniversal_hard`; `1/(n+1)³ ≤ 1/n³` for `n ≥ 1`
(`one_div_le_one_div_of_le`), and at `n = 0` the bound `1 - 1/1 = 0` is only needed for
`n ≥ max n₀ 1`. -/
theorem fUniversal_weakOneWay (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) :
    (fUniversal c).WeakOneWay := by
  refine ⟨fUniversal_easy c hc, PolyExpr.normal 1 3, fun n => by simp [PolyExpr.eval_normal],
    fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := fUniversal_hard c hc hG A
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / ((n : ℝ) + 1) ^ 3 ≤ 1 / (n : ℝ) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  simp only [PolyExpr.eval_normal, Nat.cast_one, Nat.cast_pow, Nat.cast_add, one_mul]
  linarith

/-- **The universal one-way function** [PS10, Theorem 63.1]: if there exists a (strong)
one-way function, then `f_universal` (for a scheme with an exponential canonizer) is weakly
one-way, and its direct product `(fUniversal c).prod q` is strongly one-way for some
polynomial `q` (hardness amplification, [PS10, Theorem 35.1], `weak_to_strong`).

**Deviation:** the output of `f_universal` carries the machine description (DESIGN §7,
error 1); "hardness amplification from §2.3" of the text is §2.4 (error 19); the scheme
hypothesis `CanonizerExp c`; the strong one-way function is the amplified product.

**Proof sketch.** `lemma_64_3`, `fUniversal_weakOneWay`, `weak_to_strong`. -/
theorem theorem_63_1 (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    (fUniversal c).WeakOneWay ∧ ∃ q : PolyExpr, FunFamily.StrongOneWay ((fUniversal c).prod q) :=
  have hw := fUniversal_weakOneWay c hc (lemma_64_3 h)
  ⟨hw, weak_to_strong hw⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.TuringMachine.CodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An effective machine code with a polynomial canonizer

The encoding hypothesis of [PS10, §2.13, Theorem 63.1] as formalized (`CanonizerExp`) asks for an
effective machine code whose canonizer runs in time at most exponential in the code length. The
machine library's one-tape code format has a canonizer running in time `d · (n + 1)^d` on every
input (`Turing.MachineFormat.exists_polyCanonizer`, at `Turing.oneTapeMachineFormat`). This file
reads its specification as one of `α ↦ (codeDecode α).serialize`
(`Turing.oneTapeMachineFormat_serialize_decode`, `Turing.oneTapeFormat_serialize_decode`), builds
the effective machine code with the serialization `CodeTM.serialize`, the decoder `codeDecode`
and that canonizer (the scheme of `Turing.exists_uniformMachineCode`, here with its time bound
visible), and bounds the polynomial time by an exponential: `d · (k + 1)^d ≤ d · 2^{d k}`.

## Main results

* `TCSlib.Cryptography.exists_codeCanonizer`: a machine computing `α ↦ (codeDecode α).serialize`
  in time `d · (n + 1)^d`.
* `TCSlib.Cryptography.exists_effectiveMachineCode_canonizerTime_le`: an effective machine code
  with `canonizerTime k ≤ d · 2^{d k}` for every `k`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.13, Theorem 63.1 (book p. 63).
-/

namespace TCSlib.Cryptography

open Turing

/-- **A polynomial canonizer of the one-tape codes:** there are a machine `C` and a degree `d`
such that `C` computes `α ↦ (codeDecode α).serialize` in time `n ↦ d · (n + 1)^d`, on every input
(malformed codes included: they decode to the fallback machine):
`∃ C d, C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`.

**Proof sketch.** `Turing.MachineFormat.exists_polyCanonizer` at `oneTapeMachineFormat` computes
`α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)`, which is
`(codeDecode α).serialize` by the readers `oneTapeMachineFormat_serialize_decode` and
`oneTapeFormat_serialize_decode`. -/
theorem exists_codeCanonizer :
    ∃ (C : FinTM Bool) (d : ℕ),
      C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d := by
  obtain ⟨C, d, hC⟩ := oneTapeMachineFormat.exists_polyCanonizer
  have hf : (fun α => oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)) =
      fun α => (codeDecode α).serialize :=
    funext fun α =>
      (oneTapeMachineFormat_serialize_decode α).trans (oneTapeFormat_serialize_decode α)
  exact ⟨C, d, hf ▸ hC⟩

/-- **An effective machine code with an exponential canonizer** [PS10, §2.13, the encoding
behind Theorem 63.1]: there are an effective machine code `c` and `d : ℕ` with
`c.canonizerTime k ≤ d · 2^{d k}` for every `k`.

**Proof sketch.** Take `C, d` from `exists_codeCanonizer` and the code
`⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩` with canonizer `C` and
`canonizerTime n = d · (n + 1)^d`. Since `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`),
`(k + 1)^d ≤ (2^k)^d = 2^{d k}` (`Nat.pow_le_pow_left`, `pow_mul`). The case `d = 0` needs no
care (both sides are `0`), nor does `k = 0` (`1 ≤ 1`). -/
theorem exists_effectiveMachineCode_canonizerTime_le :
    ∃ (c : EffectiveMachineCode) (d : ℕ), ∀ k, c.canonizerTime k ≤ d * 2 ^ (d * k) := by
  obtain ⟨C, d, hC⟩ := exists_codeCanonizer
  refine ⟨{ toMachineCode := ⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩
            canonizer := C
            canonizerTime := fun n => d * (n + 1) ^ d
            canonizer_computes := hC }, d, fun k => ?_⟩
  show d * (k + 1) ^ d ≤ d * 2 ^ (d * k)
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hpow : (k + 1) ^ d ≤ 2 ^ (d * k) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hk d
  exact Nat.mul_le_mul_left d hpow

end TCSlib.Cryptography

## ===== TCSlib/Complexity/TuringMachine/CodeFormat.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CodeParser

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-code formats

The shared record and table parser layer for fixed machine serializations.
This factors the one- and two-work-tape constructions of [AB09, §1.4].

## Main definitions

* `Turing.CodeFormat` — a table grammar, its laws and its fallback.
* `Turing.actionBitsK` / `Turing.codeReadActionK` — records for any work-tape count.
* `Turing.CodeTable2` — the shared 27-record two-work-tape table.
* `Turing.oneTapeFormat` — the one-work-tape instance and public decoder wrappers.

## Main results

* `Turing.CodeFormat.decode_serialize_pad` — padded decoding recovers the machine.
* `Turing.CodeFormat.canonical_eq` — scanning computes its canonical serialization.
* `Turing.CodeFormat.numStates_decode_le` — the guarded decoded-size bound.
* `Turing.actionBitsK_eq`, `Turing.codeSkipActionK_append` — a record's fields, and skipping it
  (the ND inventory API, round 2; gate 37, finding 1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing


/-! ## Transition records -/

/-- The serialization of a transition record lists the input move, each work-tape write
and move in tape order, the output, and the successor state. [AB09, §1.4] -/
def actionBitsK {k n : ℕ} (a : Action k Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++
    (List.finRange k).flatMap
      (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) ++
    optBoolBits a.output ++ optStateBits a.state

/-- **A record's fields** (the ND inventory API, round 2; gate 37, finding 1): the input move,
each work tape's write and move in tape order, the output, the successor state. [AB09, §1.4] -/
theorem actionBitsK_eq {k n : ℕ} (a : Action k Bool (Fin (n + 1))) :
    actionBitsK a = signBits a.inputTape ++
      (List.finRange k).flatMap
        (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) ++
      optBoolBits a.output ++ optStateBits a.state := rfl

/-- Read an optional work-tape write and its head move. [AB09, §1.4] -/
def codeReadWork (xs : List Bool) :
    Option ((Option (Option Bool) × SignType) × List Bool) := do
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  pure ((wr, wm), xs)

/-- Read a transition record with a vector of `k` work-tape actions. [AB09, §1.4] -/
def codeReadActionK (k n : ℕ) (xs : List Bool) :
    Option (Action k Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (ws, xs) ← codeReadVec codeReadWork k xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, ws, out, q⟩, xs)

/-- Skip a work-tape write and move, enforcing their field grammar. [AB09, §1.4] -/
def codeSkipWork (xs : List Bool) : Option (List Bool) :=
  (codeSkipPair (fun _ _ => true) xs).bind (codeSkipPair (fun a b => a || !b))

/-- Skip a transition record for `k` work tapes, checking the successor state bound. [AB09, §1.4] -/
def codeSkipActionK (k n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipRepeat codeSkipWork k xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs

/-- Reading a serialized work-tape action recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadWork_append (p : Option (Option Bool) × SignType) (xs : List Bool) :
    codeReadWork ((optOptBoolBits p.1 ++ signBits p.2) ++ xs) = some (p, xs) := by
  rcases p with ⟨wr, wm⟩
  simp only [codeReadWork, List.append_assoc, codeReadWrite_append, codeReadSign_append,
    bind, Option.bind, pure]

/-- Reading a serialized transition recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadActionK_append {k n : ℕ} (a : Action k Bool (Fin (n + 1))) (xs : List Bool) :
    codeReadActionK k n (actionBitsK a ++ xs) = some (a, xs) := by
  rcases a with ⟨im, ws, out, q⟩
  have hv : ∀ ys, codeReadVec codeReadWork k
      ((List.finRange k).flatMap (fun i => optOptBoolBits (ws i).1 ++ signBits (ws i).2) ++ ys) =
        some (ws, ys) :=
    codeReadVec_append codeReadWork (fun p => optOptBoolBits p.1 ++ signBits p.2)
      codeReadWork_append k ws
  simp only [actionBitsK, List.append_assoc, codeReadActionK, codeReadSign_append, hv,
    codeReadOutput_append, codeReadState_append, bind, Option.bind, pure]

/-- A successful work-tape read consumes exactly the serialization of its result. [AB09, §1.4] -/
lemma codeReadWork_sound (xs : List Bool) (p : Option (Option Bool) × SignType)
    (rest : List Bool) (h : codeReadWork xs = some (p, rest)) :
    xs = (optOptBoolBits p.1 ++ signBits p.2) ++ rest := by
  simp only [codeReadWork, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨wr, r₁⟩, h₁, ⟨⟨wm, r₂⟩, h₂, h⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadWrite_sound xs wr r₁ h₁, codeReadSign_sound r₁ wm r₂ h₂]
  simp [List.append_assoc]

/-- A successful transition read consumes exactly the serialization of its result. [AB09, §1.4] -/
lemma codeReadActionK_sound {k n : ℕ} (xs : List Bool) (a : Action k Bool (Fin (n + 1)))
    (rest : List Bool) (h : codeReadActionK k n xs = some (a, rest)) :
    xs = actionBitsK a ++ rest := by
  simp only [codeReadActionK, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨ws, r₂⟩, h₂, ⟨⟨out, r₃⟩, h₃, ⟨⟨q, r₄⟩, h₄, h⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁,
    codeReadVec_sound codeReadWork (fun p => optOptBoolBits p.1 ++ signBits p.2)
      codeReadWork_sound k r₁ ws r₂ h₂,
    codeReadOutput_sound r₂ out r₃ h₃, codeReadState_sound r₃ q r₄ h₄]
  simp [actionBitsK, List.append_assoc]

/-- Erasing the work-tape reader result gives the work-tape skipper. [AB09, §1.4] -/
lemma codeEraseWork (xs : List Bool) : (codeReadWork xs).map Prod.snd = codeSkipWork xs := by
  simp only [codeReadWork, codeSkipWork, bind, Option.map_bind, Function.comp_def, pure,
    Option.map_some]
  rw [← codeEraseWrite xs, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseSign p.2

/-- Erasing the transition reader result gives the transition skipper. [AB09, §1.4] -/
lemma codeEraseActionK (k n : ℕ) (xs : List Bool) :
    (codeReadActionK k n xs).map Prod.snd = codeSkipActionK k n xs := by
  have hv (ys : List Bool) :
      (codeReadVec codeReadWork k ys).map Prod.snd = codeSkipRepeat codeSkipWork k ys := by
    rw [codeEraseVec]
    exact congrArg (fun r => codeSkipRepeat r k ys) (funext codeEraseWork)
  simp only [codeReadActionK, codeSkipActionK, bind, Option.map_bind, Function.comp_def, pure,
    Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← hv p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

/-- **Skipping a serialized record leaves its suffix** (the ND inventory API, round 2; gate 37,
finding 1): `codeSkipActionK k n (actionBitsK a ++ xs) = some xs`. [AB09, §1.4]

**Proof sketch.** The skipper is the reader with its result erased (`codeEraseActionK`), and the
reader recovers `a` with the suffix `xs` (`codeReadActionK_append`). -/
theorem codeSkipActionK_append {k n : ℕ} (a : Action k Bool (Fin (n + 1))) (xs : List Bool) :
    codeSkipActionK k n (actionBitsK a ++ xs) = some xs := by
  rw [← codeEraseActionK, codeReadActionK_append]
  rfl

/-- Every `k`-work-tape record has at least `4 * k + 5` bits. [AB09, §1.4]

**Proof sketch.** Each work tape contributes four bits. The input move and output contribute
four more, and the successor-state field contributes at least one. -/
lemma codeActionK_length {k n : ℕ} (a : Action k Bool (Fin (n + 1))) :
    4 * k + 5 ≤ (actionBitsK a).length := by
  have hs (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have ho (b : Option Bool) : (optBoolBits b).length = 2 := by
    rcases b with _ | b
    · rfl
    · cases b <;> rfl
  have hw (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    rcases b with _ | (_ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  have hq : 1 ≤ (optStateBits a.state).length := by
    cases a.state <;>
      simp only [optStateBits, unaryFin, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil] <;> omega
  have hv : 4 * k ≤ ((List.finRange k).flatMap fun i =>
      optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2).length := by
    simpa using codeFlatMap_length (List.finRange k)
      (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) 4
      (fun i _ => by simp [hs, hw])
  simp only [actionBitsK, List.length_append, hs, ho]
  omega

/-- The work-symbol function reading `w₀` on tape `0` and `w₁` on tape `1`,
for the fixed table enumeration of `Turing.CodeNDTM.serialize`. -/
def workPair (w₀ w₁ : Option Bool) : Fin 2 → Option Bool :=
  fun j => if j = 0 then w₀ else w₁

/-- Serialization of one two-work-tape transition record: the input-head move,
then each work tape's optional write and move in tape order, then the emission
and the successor state — `Turing.actionBits` with a second work-tape record. -/
def actionBits₂ {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++
    optOptBoolBits (a.workTapes 0).1 ++ signBits (a.workTapes 0).2 ++
    optOptBoolBits (a.workTapes 1).1 ++ signBits (a.workTapes 1).2 ++
    optBoolBits a.output ++ optStateBits a.state

/-- The fixed one-work-tape serialization agrees with the generic record serialization. [AB09, §1.4] -/
lemma actionBits_eq_actionBitsK {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    actionBits a = actionBitsK a := by
  simp [actionBits, actionBitsK, List.finRange_succ, List.append_assoc]

/-- The fixed two-work-tape serialization agrees with the generic record serialization. [AB09, §1.4] -/
lemma actionBits₂_eq_actionBitsK {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) :
    actionBits₂ a = actionBitsK a := by
  simp [actionBits₂, actionBitsK, List.finRange_succ, List.append_assoc]

/-- The fixed one-work-tape skipper agrees with the generic skipper at `k = 1`. [AB09, §1.4] -/
lemma codeSkipAction_eq_codeSkipActionK (n : ℕ) (xs : List Bool) :
    codeSkipAction n xs = codeSkipActionK 1 n xs := by
  have h1 (ys : List Bool) : codeSkipRepeat codeSkipWork 1 ys = codeSkipWork ys := by
    cases h : codeSkipWork ys <;> simp [codeSkipRepeat, h]
  simp only [codeSkipAction, codeSkipActionK, h1, codeSkipWork, bind, Option.bind_assoc]

/-! ## Table formats -/

/-- A machine-code format specifies a transition-table grammar under the shared
state-count and initial-state header, together with its parser laws and fallback. [AB09, §1.4] -/
structure CodeFormat where
  /-- the coded machines -/
  Code : Type
  /-- the transition table of a machine with `n + 1` states -/
  Table : ℕ → Type
  /-- one less than the number of states -/
  numStates : Code → ℕ
  /-- assemble a machine from its state count, initial state and table -/
  assemble : (n : ℕ) → Fin (n + 1) → Table n → Code
  /-- the format's fixed serialization -/
  serialize : Code → List Bool
  /-- the fixed serialization of a table -/
  tableBits : {n : ℕ} → Table n → List Bool
  /-- the table reader -/
  readTable : (n : ℕ) → List Bool → Option (Table n × List Bool)
  /-- the erased table reader -/
  skipTable : ℕ → List Bool → Option (List Bool)
  /-- the minimum number of table bits per state (the up-front guard constant) -/
  guard : ℕ
  /-- the machine denoted by every malformed string -/
  fallback : Code
  numStates_assemble : ∀ n q t, numStates (assemble n q t) = n
  serialize_assemble : ∀ n q (t : Table n),
    serialize (assemble n q t) = pairEncode n.bits (unaryFin q ++ tableBits t)
  assemble_surj : ∀ M, ∃ n q t, assemble n q t = M
  readTable_append : ∀ n (t : Table n) xs, readTable n (tableBits t ++ xs) = some (t, xs)
  readTable_sound : ∀ n xs (t : Table n) rest,
    readTable n xs = some (t, rest) → xs = tableBits t ++ rest
  readTable_erase : ∀ n xs, (readTable n xs).map Prod.snd = skipTable n xs
  tableBits_length : ∀ n (t : Table n), guard * (n + 1) ≤ (tableBits t).length

namespace CodeFormat

variable (F : CodeFormat)

/-- Parse a machine and retain its all-true padding; check the table-length guard
before reading any state-indexed table entries. [AB09, §1.4] -/
def parseFull (xs : List Bool) : Option (F.Code × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if F.guard * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← F.readTable n rest
      if rest.all id then pure (F.assemble n q table, rest) else none

/-- Decode every string, choosing the format's fallback on any malformed input. [AB09, §1.4] -/
def decode (xs : List Bool) : F.Code := ((F.parseFull xs).map Prod.fst).getD F.fallback

/-- Check the same header, table-length guard and padding as the parser,
retaining only the unconsumed suffix. [AB09, §1.4] -/
def scan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if F.guard * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← F.skipTable n rest
      if rest.all id then pure rest else none

/-- Return the consumed prefix when scanning succeeds and the fallback's serialization
when scanning fails. [AB09, §1.4] -/
def canonical (xs : List Bool) : List Bool :=
  (F.scan xs).casesOn (F.serialize F.fallback) fun tail => xs.take (xs.length - tail.length)

/-- Parsing a serialization followed by true padding recovers the machine and padding. [AB09, §1.4]

**Proof sketch.** The doubled header recovers the canonical state-count bits. The table-length
bound discharges the early guard; the initial-state and table inverse laws recover
the assembled machine and leave the replicated true suffix, which passes the padding test. -/
theorem parseFull_serialize_pad (M : F.Code) (m : ℕ) :
    F.parseFull (F.serialize M ++ List.replicate m true) =
      some (M, List.replicate m true) := by
  obtain ⟨n, q, t, rfl⟩ := F.assemble_surj M
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  rw [F.serialize_assemble, hp]
  unfold parseFull
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := F.tableBits_length n t
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [List.append_assoc, codeReadFin_append, F.readTable_append,
    List.all_replicate, id_eq, ite_self, ↓reduceIte, pure]

/-- Decoding a serialization followed by arbitrary true padding recovers the machine. [AB09, §1.4] -/
theorem decode_serialize_pad (M : F.Code) (m : ℕ) :
    F.decode (F.serialize M ++ List.replicate m true) = M := by
  simp only [decode, parseFull_serialize_pad, Option.map_some, Option.getD_some]

/-- Every successful parse expresses the input as the decoded serialization and suffix. [AB09, §1.4]

**Proof sketch.** Decompose the successful parse and use the field and table soundness equations.
The canonical state-count check reconstructs the doubled header, giving exactly
the machine serialization followed by the retained suffix. -/
theorem parseFull_sound (xs : List Bool) (M : F.Code) (tail : List Bool)
    (h : F.parseFull xs = some (M, tail)) : xs = F.serialize M ++ tail := by
  unfold parseFull at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := F.readTable_sound _ _ _ _ ht
        dsimp only at htable
        rw [F.serialize_assemble, eq_pairEncode_of_pairDecode xs bits rest hp,
          codeReadFin_sound rest q r₁ hq, htable]
        simp only [pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- The erased scanner returns exactly the suffix retained by the full parser. [AB09, §1.4]

**Proof sketch.** Push suffix projection through the parser's binds and branches. The initial-state
and table erasure laws replace their readers by the corresponding skippers; the
header checks and final padding test are unchanged. -/
theorem scan_full (xs : List Bool) : F.scan xs = (F.parseFull xs).map Prod.snd := by
  simp only [scan, parseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool) (t : F.Table (codeBitsNat p.1) × List Bool) :
      (if t.2.all id then some (F.assemble (codeBitsNat p.1) q.1 t.1, t.2) else none).map
          Prod.snd = (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  rw [← F.readTable_erase, ← codeErase_bind]

/-- The scanner-based canonical prefix equals the serialization of the decoded machine. [AB09, §1.4] -/
theorem canonical_eq (xs : List Bool) : F.canonical xs = F.serialize (F.decode xs) := by
  unfold canonical decode
  rw [scan_full]
  cases h : F.parseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [F.parseFull_sound xs M tail h]
    simp

/-- The decoded serialization is no longer than the input or the fixed fallback,
whichever is longer. [AB09, §1.4] -/
theorem serialize_decode_length_le (α : List Bool) :
    (F.serialize (F.decode α)).length ≤ max α.length (F.serialize F.fallback).length := by
  rw [← F.canonical_eq]
  unfold canonical
  cases F.scan α with
  | none => exact Nat.le_max_right _ _
  | some tail => exact (List.length_take_le' _ _).trans (Nat.le_max_left _ _)

/-- The guarded table-size lower bound for the decoded machine is bounded by the
input length or the fallback length, whichever is larger. [AB09, §1.4] -/
theorem numStates_decode_le (α : List Bool) :
    F.guard * (F.numStates (F.decode α) + 1) ≤
      max α.length (F.serialize F.fallback).length := by
  have hsize := F.serialize_decode_length_le α
  obtain ⟨n, q, t, h⟩ := F.assemble_surj (F.decode α)
  rw [← h, F.serialize_assemble, length_pairEncode, List.length_append] at hsize
  rw [← h, F.numStates_assemble]
  have htable := F.tableBits_length n t
  omega

/-- A failed full parse decodes to the format's fallback. [AB09, §1.4] -/
theorem decode_of_parseFull_none (α : List Bool) (h : F.parseFull α = none) :
    F.decode α = F.fallback := by
  simp [decode, h]

/-- A failed table-length guard decodes to the fallback before table recursion. [AB09, §1.4] -/
theorem decode_of_guard_lt (α bits rest : List Bool) (hp : pairDecode α = some (bits, rest))
    (hg : rest.length < F.guard * (codeBitsNat bits + 1)) : F.decode α = F.fallback := by
  simp [decode, parseFull, hp, hg]

end CodeFormat

/-! ## Two-work-tape tables -/

/-- A two-work-tape transition table is indexed by state, input read, and both work reads. [AB09, §1.4] -/
abbrev CodeTable2 (n : ℕ) : Type :=
  Fin (n + 1) → Option Bool → Option Bool → Option Bool → Action 2 Bool (Fin (n + 1))

/-- Serialize all two-work-tape table entries in state, input, work-0, work-1 order. [AB09, §1.4] -/
def codeTable2Bits {n : ℕ} (t : CodeTable2 n) : List Bool :=
  (List.finRange (n + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
          actionBitsK (t q inp w₀ w₁)

/-- Read the 27 two-work-tape transition records for every state. [AB09, §1.4] -/
def codeReadTable2 (n : ℕ) : List Bool → Option (CodeTable2 n × List Bool) :=
  codeReadVec (codeReadSymbols (codeReadSymbols (codeReadSymbols (codeReadActionK 2 n)))) (n + 1)

/-- Skip the 27 two-work-tape transition records for every state. [AB09, §1.4] -/
def codeSkipTable2 (n : ℕ) : List Bool → Option (List Bool) :=
  codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipActionK 2 n) 3) 3) 3)
    (n + 1)

/-- Reading a serialized two-work-tape table recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadTable2_append {n : ℕ} (t : CodeTable2 n) (xs : List Bool) :
    codeReadTable2 n (codeTable2Bits t ++ xs) = some (t, xs) :=
  codeReadVec_append _ _ (fun _ _ => codeReadSymbols_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadActionK_append _ _) _ _) _ _) _ _ _

/-- A successful two-work-tape table read consumes exactly its serialization. [AB09, §1.4] -/
lemma codeReadTable2_sound {n : ℕ} (xs : List Bool) (t : CodeTable2 n) (rest : List Bool)
    (h : codeReadTable2 n xs = some (t, rest)) : xs = codeTable2Bits t ++ rest :=
  codeReadVec_sound _ _ (fun _ _ _ => codeReadSymbols_sound _ _
    (fun _ _ _ => codeReadSymbols_sound _ _
      (fun _ _ _ => codeReadSymbols_sound _ _ codeReadActionK_sound _ _ _) _ _ _) _ _ _)
    _ _ _ _ h

/-- Erasing the two-work-tape table reader result gives the corresponding skipper. [AB09, §1.4] -/
lemma codeEraseTable2 (n : ℕ) (xs : List Bool) :
    (codeReadTable2 n xs).map Prod.snd = codeSkipTable2 n xs := by
  have ht := codeEraseVec
    (codeReadSymbols (codeReadSymbols (codeReadSymbols (codeReadActionK 2 n)))) (n + 1) xs
  simp only [codeEraseSymbols, codeEraseActionK] at ht
  exact ht

/-- Every two-work-tape table has at least 351 bits per state. [AB09, §1.4]

**Proof sketch.** Every record has at least 13 bits. Sum this lower bound over each of the
three possible symbols on each of three reads, giving 27 records and 351 bits
per state; then sum over the state enumeration. -/
lemma codeTable2Bits_length {n : ℕ} (t : CodeTable2 n) :
    351 * (n + 1) ≤ (codeTable2Bits t).length := by
  have hr : ∀ a : Action 2 Bool (Fin (n + 1)), 13 ≤ (actionBitsK a).length :=
    fun a => by have := codeActionK_length a; omega
  have h := codeFlatMap_length (List.finRange (n + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
          actionBitsK (t q inp w₀ w₁)) 351 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
            actionBitsK (t q inp w₀ w₁)) 117 (by
          intro inp _
          have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
            (fun w₀ => ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBitsK (t q inp w₀ w₁)) 39 (by
                intro w₀ _
                simpa using codeFlatMap_length
                  ([none, some false, some true] : List (Option Bool))
                  (fun w₁ => actionBitsK (t q inp w₀ w₁)) 13 (fun _ _ => hr _))
          simpa using h)
      simpa using h)
  simpa [codeTable2Bits] using h

/-! ## One-work-tape instance -/

private lemma codeReadActionK_one_append {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) (xs : List Bool) :
    codeReadActionK 1 n (actionBits a ++ xs) = some (a, xs) := by
  rw [actionBits_eq_actionBitsK]; exact codeReadActionK_append a xs

private lemma codeReadActionK_one_sound {n : ℕ} (xs : List Bool) (a : Action 1 Bool (Fin (n + 1)))
    (rest : List Bool) (h : codeReadActionK 1 n xs = some (a, rest)) :
    xs = actionBits a ++ rest := by
  rw [actionBits_eq_actionBitsK]; exact codeReadActionK_sound xs a rest h

private lemma codeEraseActionK_one (n : ℕ) (xs : List Bool) :
    (codeReadActionK 1 n xs).map Prod.snd = codeSkipAction n xs := by
  rw [codeEraseActionK, codeSkipAction_eq_codeSkipActionK]

/-- The one-work-tape `CodeTM` format has nine records per state and guard 81. [AB09, §1.4]

**Proof sketch.** The frozen record serialization is the generic one at one work tape. Nested
vector and symbol-reader laws provide table inversion, soundness and erasure;
summing the nine-bit record bound over the nine records gives guard 81. -/
def oneTapeFormat : CodeFormat where
  Code := CodeTM
  Table := fun n => Fin (n + 1) → Option Bool → Option Bool → Action 1 Bool (Fin (n + 1))
  numStates := CodeTM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun s inp w => t s inp (w 0)⟩⟩
  serialize := CodeTM.serialize
  tableBits := fun {n} t => (List.finRange (n + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (t q inp w)
  readTable := fun n =>
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadActionK 1 n))) (n + 1)
  skipTable := fun n =>
    codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1)
  guard := 81
  fallback := codeFallback
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => rfl
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, fun s inp w => tr s inp (fun _ => w), ?_⟩
    show CodeTM.mk n ⟨q, fun s inp w => tr s inp (fun _ => w 0)⟩ = CodeTM.mk n ⟨q, tr⟩
    congr 1
    congr 1
    funext s inp w
    apply congrArg (tr s inp)
    funext i
    exact congrArg w (Subsingleton.elim _ _)
  readTable_append := fun _ _ _ =>
    codeReadVec_append _ _ (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadActionK_one_append _ _) _ _) _ _ _
  readTable_sound := fun _ _ _ _ h =>
    codeReadVec_sound _ _ (fun _ _ _ => codeReadSymbols_sound _ _
      (fun _ _ _ => codeReadSymbols_sound _ _ codeReadActionK_one_sound _ _ _) _ _ _)
      _ _ _ _ h
  readTable_erase := fun n xs => by
    have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadActionK 1 n))) (n + 1) xs
    simp only [codeEraseSymbols, codeEraseActionK_one] at ht
    exact ht
  tableBits_length := fun n t => by
    have hr : ∀ a : Action 1 Bool (Fin (n + 1)), 9 ≤ (actionBits a).length := fun a => by
      rw [actionBits_eq_actionBitsK]; have := codeActionK_length a; omega
    have h := codeFlatMap_length (List.finRange (n + 1))
      (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (t q inp w)) 81 (by
        intro q _
        have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
          (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (t q inp w)) 27 (by
              intro inp _
              simpa using codeFlatMap_length
                ([none, some false, some true] : List (Option Bool))
                (fun w => actionBits (t q inp w)) 9 (fun _ _ => hr _))
        simpa using h)
    simpa using h

/-- Total decoding: every malformed string denotes the fixed fallback. -/
def codeDecode (xs : List Bool) : CodeTM :=
  oneTapeFormat.decode xs

/-- The total decoder satisfies the required exact padded round-trip law. -/
lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
    codeDecode (M.serialize ++ List.replicate m true) = M :=
  oneTapeFormat.decode_serialize_pad M m

/-- The one-tape format's canonical serialization is that of the decoded machine:
`oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`. -/
theorem oneTapeFormat_serialize_decode (xs : List Bool) :
    oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl

/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
def codeScan (xs : List Bool) : Option (List Bool) :=
  oneTapeFormat.scan xs

/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/
def codeCanonical (xs : List Bool) : List Bool :=
  oneTapeFormat.canonical xs

/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/
lemma codeCanonical_eq (xs : List Bool) : codeCanonical xs = (codeDecode xs).serialize :=
  oneTapeFormat.canonical_eq xs

end Turing

## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim); `Turing.dbl` — the doubling.
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.
* `Turing.pairDiagTM` — the diagonal pairing machine `α ↦ pairEncode α α` (MIG-1).
* `Turing.FinTM.toCodeTM` — the code normal form of a one-work-tape binary machine
  (MIG-1).

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.length_pairEncode`, `Turing.pairEncode_ne_nil`, `Turing.pairEncode_eq_dbl`,
  `Turing.pairDecode_eq_none`,
  `Turing.eq_pairEncode_of_pairDecode`, `Turing.pairEncode_replicate_inj` — the shape of
  the pairing, shared by the machine-side developments.
* `Turing.length_bits_le_self` — `|bits m| ≤ m`.
* `Turing.bits_two_pow_mul`, `Turing.bits_two_pow_eq_replicate` — the `Nat.bits` shift law
  `(2^j·m).bits = 0^j ++ m.bits` and its case `m = 1` (CH34-D4).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
  Its witness's spec is `Turing.pairDiagTM_computes` (MIG-1; sorried until the fill
  F-A).
* `Turing.FinTM.toCodeTM_computesInTime_iff` — the code normal form halts with the same
  outputs at the same times (MIG-1).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).
* `Turing.exists_codeTM_spaceUsed` — the same coded machine also uses the same space at
  every time; `Turing.CodeTM.one_le_spaceUsed` — every coded run visits a cell.

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.
* `Turing.pairEncode_eq`, `Turing.unaryFin_eq` — the two encodings as equations, the
  specification API (user, 2026-10-16).
* `Turing.signBits_neg`/`_zero`/`_pos`, `Turing.optBoolBits_none`/`_some_false`/`_some_true`,
  `Turing.optOptBoolBits_none`/`_some_none`/`_some_false`/`_some_true`,
  `Turing.optStateBits_none`/`_some` — the record fields' encoders, case by case (the ND inventory
  API, round 2; gate 37, finding 1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- **The pairing as an equation** (the specification API, user 2026-10-16): the code doubled,
the separator `false, true`, then the second word. -/
theorem pairEncode_eq (x α : List Bool) :
    pairEncode x α = (x.flatMap fun b => [b, b]) ++ [false, true] ++ α :=
  rfl

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The empty word is not a pair: `pairDecode [] = none`. -/
theorem pairDecode_nil : pairDecode [] = none :=
  rfl

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-! ### Shape of the pairing

Generic list facts about `pairEncode` and `pairDecode`, shared by the machine-side
developments (the time hierarchy, the polynomial hierarchy, logspace machines, and
the circuit-evaluation machines). -/

/-- A word with every bit written twice — the first component of `Turing.pairEncode`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [b, b]

/-- Doubling the empty word gives the empty word. -/
@[simp] lemma dbl_nil : dbl [] = [] := rfl

/-- Doubling `b :: w` is `b b` followed by doubling `w`. -/
@[simp] lemma dbl_cons (b : Bool) (w : List Bool) : dbl (b :: w) = b :: b :: dbl w := rfl

/-- Doubling a word doubles its length. -/
@[simp] lemma length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; ring

/-- Both copies of bit `c` of a doubled word read `w[c]`. -/
lemma getElem?_dbl (w : List Bool) (c : ℕ) (hc : c < w.length) (p : Bool) :
    (dbl w)[2 * c + p.toNat]? = some w[c] := by
  induction w generalizing c with
  | nil => simp at hc
  | cons b w ih =>
    cases c with
    | zero => cases p <;> simp
    | succ c =>
      have := ih c (by simpa using hc)
      simp only [dbl_cons, List.getElem_cons_succ]
      rw [show 2 * (c + 1) + p.toNat = (2 * c + p.toNat) + 1 + 1 by ring]
      simpa using this

/-- `pairEncode x y` is the doubled first word, the separator `[false, true]`, and the
second word. -/
lemma pairEncode_eq_dbl (x y : List Bool) : pairEncode x y = dbl x ++ [false, true] ++ y :=
  rfl

/-- The length of a pair: `|pairEncode x y| = 2|x| + 2 + |y|`. -/
theorem length_pairEncode (x y : List Bool) :
    (pairEncode x y).length = 2 * x.length + 2 + y.length := by
  simp [pairEncode_eq_dbl]
  omega

/-- No pair encoding is the empty word: `pairEncode x y` has length at least `2`. -/
theorem pairEncode_ne_nil (x y : List Bool) : pairEncode x y ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [length_pairEncode] at this

/-- A string that is not a pair is a doubled word followed by a malformed tail: the end
of the string, a lone bit, or the aligned pair `10`.

**Proof sketch.** Functional induction along `pairDecode`: aligned `00`/`11` pairs extend
the doubled prefix; in the remaining case the string matches none of `00`, `11`, `01`,
so it is empty, a single bit, or starts with `10`. -/
theorem pairDecode_eq_none (z : List Bool) (h : pairDecode z = none) :
    ∃ w tail, z = dbl w ++ tail ∧
      (tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) := by
  induction z using pairDecode.induct with
  | case1 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨false :: w, tail, by simp [hw], ht⟩
  | case2 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨true :: w, tail, by simp [hw], ht⟩
  | case3 xs => simp [pairDecode] at h
  | case4 xs h₁ h₂ h₃ =>
    refine ⟨[], xs, by simp, ?_⟩
    rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · cases b <;> cases c
      · exact absurd rfl (h₁ r)
      · exact absurd rfl (h₃ r)
      · exact Or.inr (Or.inr ⟨r, rfl⟩)
      · exact absurd rfl (h₂ r)

/-- A successfully decoded string is the pairing of its components.

**Proof sketch.** Functional induction along `pairDecode`, inverting
`pairDecode_pairEncode` one aligned pair at a time. -/
theorem eq_pairEncode_of_pairDecode (z a b : List Bool) (h : pairDecode z = some (a, b)) :
    z = pairEncode a b := by
  induction z using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode] at h

/-- A unary-first pair `⟨1ⁿ, u⟩` determines both `n` and `u`. -/
lemma pairEncode_replicate_inj {n n' : ℕ} {u u' : List Bool}
    (h : pairEncode (List.replicate n true) u = pairEncode (List.replicate n' true) u') :
    n = n' ∧ u = u' := by
  have := pairEncode_injective (a₁ := (List.replicate n true, u))
    (a₂ := (List.replicate n' true, u')) h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨by simpa using congrArg List.length h1, h2⟩

/-- The binary expansion of `m` has at most `m` bits. -/
lemma length_bits_le_self (m : ℕ) : m.bits.length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- **The `Nat.bits` shift law**: multiplying a positive `m` by `2 ^ j`
prepends `j` low zero bits to its little-endian binary expansion,
`(2^j·m).bits = 0^j ++ m.bits`. (Positivity is needed: `Nat.bits 0 = []`.)
The public home of the law, promoted per the fills-6 request F6-1(a)
(CH34-D4).

**Proof sketch.** Induct on `j`. A positive number stays positive after
multiplication by a power of two, and doubling a nonzero number prepends one
low zero bit to its expansion; induction counts the prepended zeros. -/
theorem bits_two_pow_mul (j m : ℕ) (hm : 0 < m) :
    (2 ^ j * m).bits = List.replicate j false ++ m.bits := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, Nat.bit0_bits _ (Nat.mul_pos (Nat.two_pow_pos j) hm).ne']
    simp only [ih, List.replicate_succ, List.cons_append]

/-- The little-endian binary expansion of `2 ^ n` is `n` zero bits followed by
one high bit: `(2^n).bits = 0^n 1`. The case `m = 1` of
`Turing.bits_two_pow_mul`, since the expansion of `1` is the single bit `1`. -/
theorem bits_two_pow_eq_replicate (n : ℕ) :
    (2 ^ n).bits = List.replicate n false ++ [true] := by
  simpa using bits_two_pow_mul n 1 Nat.one_pos

/-- **The diagonal pairing machine**. A six-state machine with no work tapes that, on input `α`,
writes each symbol of `α` twice, then the separator `false, true`, rewinds the input, and copies `α`
once more, so that it outputs `pairEncode α α`. It is also the witness of
`Turing.FinTM.computesFunInTime_pairDup` (consolidation: Primitives' private `pairDupTM`, which
computes the same function, retires). [AB09, proof of Theorem 1.11: the self-application input of
the `HALT` reduction] -/
def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- **The diagonal pairing machine's time**. On input `α` the diagonal pairing machine halts within
`4|α| + 5` steps with output `pairEncode α α`.

**Proof sketch.** The `have h` of today's `computesFunInTime_pairEncode_diag`, from the private
`pairDiag_run`: the doubling pass takes `2|α|` steps, the two separator steps and the first left
move `3`, the rewind `|α| + 1`, the copy `|α|`, and the halting transition `1`. -/
theorem pairDiagTM_computes (x : List Bool) :
    pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
  sorry

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- **A left move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .neg = [true, true]`. -/
theorem signBits_neg : signBits .neg = [true, true] := rfl

/-- **A stay's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .zero = [false, false]`. -/
theorem signBits_zero : signBits .zero = [false, false] := rfl

/-- **A right move's bits** (the ND inventory API, round 2; gate 37, finding 1):
`signBits .pos = [true, false]`. -/
theorem signBits_pos : signBits .pos = [true, false] := rfl

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- **No bit's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits none = [false, false]`. -/
theorem optBoolBits_none : optBoolBits none = [false, false] := rfl

/-- **The bit `false`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some false) = [true, false]`. -/
theorem optBoolBits_some_false : optBoolBits (some false) = [true, false] := rfl

/-- **The bit `true`'s bits** (the ND inventory API, round 2; gate 37, finding 1):
`optBoolBits (some true) = [true, true]`. -/
theorem optBoolBits_some_true : optBoolBits (some true) = [true, true] := rfl

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- **No write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits none = [false, false]`. -/
theorem optOptBoolBits_none : optOptBoolBits none = [false, false] := rfl

/-- **A blank write's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some none) = [false, true]`. -/
theorem optOptBoolBits_some_none : optOptBoolBits (some none) = [false, true] := rfl

/-- **Writing `false`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some false)) = [true, false]`. -/
theorem optOptBoolBits_some_false : optOptBoolBits (some (some false)) = [true, false] := rfl

/-- **Writing `true`, in bits** (the ND inventory API, round 2; gate 37, finding 1):
`optOptBoolBits (some (some true)) = [true, true]`. -/
theorem optOptBoolBits_some_true : optOptBoolBits (some (some true)) = [true, true] := rfl

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- **The unary state word as an equation** (the specification API, user 2026-10-16): `s`
`true`s, then the delimiter `false`. -/
theorem unaryFin_eq {n : ℕ} (s : Fin n) : unaryFin s = List.replicate (s : ℕ) true ++ [false] :=
  rfl

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- **Halting's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits none = [false]`. -/
theorem optStateBits_none {n : ℕ} : optStateBits (none : Option (Fin n)) = [false] := rfl

/-- **A successor state's bits** (the ND inventory API, round 2; gate 37, finding 1):
`optStateBits (some s) = true :: unaryFin s`. -/
theorem optStateBits_some {n : ℕ} (s : Fin n) : optStateBits (some s) = true :: unaryFin s := rfl

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The defining equation of `actionBits`: `actionBits a = signBits a.inputTape ++ optOptBoolBits
(a.workTapes 0).1 ++ signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state`. -/
theorem actionBits_def {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    (actionBits a : List Bool) =
      (signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
        signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state) := rfl

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

/-- The defining equation of `CodeTM.serialize` (its body, unfolded once). -/
theorem CodeTM.serialize_def (M : CodeTM) :
    CodeTM.serialize M =
      (pairEncode (Nat.bits M.numStates)
      (unaryFin M.tm.q₀ ++
        (List.finRange (M.numStates + 1)).flatMap fun q =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
              actionBits (M.tm.tr q inp fun _ => w))) := rfl

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- **A coded run visits at least one cell.** Every run of a coded machine, at every time,
has visited at least one work cell: its one work head starts somewhere. So every qualifying
budget `s` of `Complexity.space_universal` is positive, which is what lets its addend-free bound
`C · s` absorb a ruler of the header's length (the RD-3 statement gate's row-1 calculation).

**Proof sketch.** The visited set of tape `0` contains the head's initial position, and it
is one summand of the space. -/
theorem CodeTM.one_le_spaceUsed (M : CodeTM) (x : List Bool) (t : ℕ) :
    1 ≤ M.toFinTM.tm.spaceUsed (M.toFinTM.tm.initCfg x) t := by
  let i₀ : Fin M.toFinTM.k := ⟨0, by simp⟩
  have hne : (M.toFinTM.tm.visitedByTapeHead (M.toFinTM.tm.initCfg x) t i₀).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), rfl⟩⟩
  exact (Finset.card_pos.mpr hne).trans_le
    (M.toFinTM.tm.spaceUsedByTape_le_spaceUsed _ t i₀)

/-- **The space-faithful coding step.** Every one-work-tape binary machine `M` is equivalent
to a coded machine `M'` that halts with the same outputs at the same times
(`Turing.exists_codeTM`'s clause) **and uses the same space at every time**. This is the space
clause of the coding step named by `Complexity.space_hierarchy`'s sketch. [AB09, §1.4]

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited by `q₀`,
so `Fintype.equivFinOfCardEq` gives an equivalence with `Fin (|Q| - 1 + 1)`. Relabel the states
along it (`Turing.MultiTapeTM.relabelState`): by `Turing.MultiTapeTM.relabelState_runFrom_init`
the relabelled run is the original run with renamed states, so halting and outputs correspond
at every time, and the space clause is `Turing.MultiTapeTM.relabelState_spaceUsed`. The
tape-count cast uses `hk : M.k = 1`, eliminated after destructuring the bundle. -/
theorem exists_codeTM_spaceUsed (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM,
      (∀ (x output : List Bool) (t : ℕ),
        M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t) ∧
      ∀ (x : List Bool) (t : ℕ),
        M'.toFinTM.tm.spaceUsed (M'.toFinTM.tm.initCfg x) t =
          M.tm.spaceUsed (M.tm.initCfg x) t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_, ?_⟩
  · intro x output t
    simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
      MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
    constructor
    · rintro ⟨s, hhalt, hout, -⟩
      exact ⟨_, hhalt, hout, rfl⟩
    · rintro ⟨s, hhalt, hout, -⟩
      exact ⟨_, hhalt, hout, rfl⟩
  · intro x t
    exact MultiTapeTM.relabelState_spaceUsed tm e x t

/-- **The code normal form of a one-work-tape machine**. For a binary machine `M` with one work
tape, the coded machine with `|Q| - 1` as its state index bound, whose transition function is `M`'s
transported along the canonical bijection `Q ≃ Fin |Q|` (`Fintype.equivFinOfCardEq`; `Q` is
inhabited by the start state). [AB09, §1.4] Noncomputable, through `Fintype.equivFinOfCardEq`. -/
noncomputable def FinTM.toCodeTM : (M : FinTM Bool) → M.k = 1 → CodeTM
  | @FinTM.mk _ _ Q hQ dQ tm, rfl =>
    letI : Fintype Q := hQ
    letI : DecidableEq Q := dQ
    have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
      have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
      omega
    let e := Fintype.equivFinOfCardEq hcard
    ⟨Fintype.card Q - 1, tm.relabelState e⟩

/-- **The code normal form is equivalent**. For a one-work-tape binary machine `M`, its code normal
form halts on `x` with output `w` within `t` steps if and only if `M` does. [AB09, §1.4]

**Proof sketch.** The relabelled machine's run is the image of `M`'s run under the state
bijection (`Turing.MultiTapeTM.relabelState_runFrom_init`); halting and output are preserved. -/
theorem FinTM.toCodeTM_computesInTime_iff (M : FinTM Bool) (hk : M.k = 1)
    (x output : List Bool) (t : ℕ) :
    (M.toCodeTM hk).toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  simp only [FinTM.toCodeTM, CodeTM.toFinTM, FinTM.ComputesInTime,
    MultiTapeTM.ComputesInTimeAndSpace, MultiTapeTM.relabelState_runFrom_init, Cfg.mapState,
    Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation is the time clause of `Turing.exists_codeTM_spaceUsed`, whose witness
is this relabelling (`Turing.MultiTapeTM.relabelState`, from the shared state-renaming module
`TCSlib.Complexity.TuringMachine.StateRenaming`), so that the relabelling is built once. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  obtain ⟨M', h, -⟩ := exists_codeTM_spaceUsed M hk
  exact ⟨M', h⟩

end Turing

## ===== TCSlib/Complexity/Diagonalization/EXPCOM.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.TimeHierarchy.Diagonal
-- B5a sanctioned import: route Z uses the one-tape machine format.
import TCSlib.Complexity.TuringMachine.CodeSimulator
-- B5b sanctioned imports: the certificate shell and exponential-polynomial ledger.
import TCSlib.Complexity.TuringMachine.Build.CertShell
import TCSlib.Complexity.ClassNP.ExpPoly
import TCSlib.Complexity.TuringMachine.Build.WordTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `EXPCOM` oracle: `P^EXPCOM = NP^EXPCOM = EXP`

[AB09, Example 3.6(3)]: relative to the oracle
`EXPCOM = {⟨M, x, 1ⁿ⟩ : M outputs 1 on x within 2ⁿ steps}`, deterministic and
nondeterministic polynomial time coincide — both equal `EXP`, via the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`. This is the `A` half of the
Baker-Gill-Solovay theorem ([AB09, Theorem 3.7], `Diagonalization/Relativization`),
taken by the book's route per the campaign decision CH34-Q4
(`AroraBarakChapters3-4Plan.md` §2.3; the machine-light self-referential oracle
of [BGS75, Theorem 1] stays recorded there as the fallback).

## Design

* **The triple `⟨M, x, 1ⁿ⟩` is rendered code-first** as
  `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)` — the universal machine's
  layout (code before payload, chapter-1 phase-3 audit, Argument B), nested
  right so each component is recovered by one aligned-pair parse.
* **The code scheme is a uniformly-timed scheme, not the hierarchy's
  arbitrary one** (round-1 blocker): `Turing.EffectiveMachineCode` bounds no
  decoding time — `canonizerTime` is arbitrary, and the round-1 audit built
  a permitted scheme embedding an arbitrarily hard decidable language into
  `decode`, putting `EXPCOM` outside `EXP` and even separating its
  relativized `P` from `NP`. `EXPCOM` queries carry **variable** codes, so
  per-code constants (`∀ α, ∃ C` — `Turing.timed_universal`'s shape) cannot
  pay for them. The new `Turing.UniformMachineCode` packages the scheme with
  a simulator whose time is **one polynomial in the code, the input, and
  the deadline jointly**; `EXPCOM` is defined over a scheme chosen from its
  sorried existence (`Turing.exists_uniformMachineCode` — the
  `TimeHierarchy.code` mirror, with the choice-over-a-sorried-existence
  declared). The hierarchy's own `Complexity.TimeHierarchy.code` is
  unchanged: fixed-code arguments never needed uniformity.
* **"Outputs `1` within `2ⁿ` steps"** is
  `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
  predicate is monotone in the budget and "within" is faithful.
* **Totalization**: a string that does not parse as a triple is simply not in
  `EXPCOM` (the existential fails); on genuine triples the witnessing
  decomposition is unique — `Turing.pairEncode_injective` applied twice,
  then `List.length` on the equality of the replicated tails (round-1
  finding 3 corrected the earlier `pairEncode_replicate_inj` citation, whose
  unary component sits on the wrong side for this nesting) — so the defining
  condition is unambiguous.

## Main definitions

* `Turing.UniformMachineCode` — an effective scheme with a uniformly timed
  bounded-acceptance simulator (round-1 repair).
* `Complexity.expCode` — the chosen uniformly-timed scheme (noncomputable;
  via the sorried existence).
* `Complexity.EXPCOM` — the oracle language, over `expCode`.
  [AB09, Example 3.6(3)]

## Main results

* `Turing.exists_uniformMachineCode` — a uniformly-timed scheme exists.

* `Complexity.EXP_subset_POracle_EXPCOM` — one padded query decides any
  `EXP` language.
* `Complexity.NPOracle_EXPCOM_subset_EXP` — the fill summit: deterministic
  exponential-time simulation of a polynomial-time oracle NDTM, answering its
  queries with the timed universal machine.
* `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` — the chained identities.
  [AB09, Example 3.6(3)]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Example 3.6(3); Claim 2.4.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (Theorem 1: the recorded
  fallback oracle for the `A` half.)
-/

namespace Turing

/-- An effective representation scheme together with a **uniformly timed
bounded-acceptance simulator**: one machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the simulator decides whether the decoded machine outputs
`[true]` on `x` within `t` steps, in time one polynomial in
`|α| + |x| + t + 1` **jointly** — uniform in the code, which is exactly what
`EXPCOM`'s variable-code queries need and what a bare
`Turing.EffectiveMachineCode` (arbitrary `canonizerTime`) or the per-code
`∀ α, ∃ C` of `Turing.timed_universal` cannot supply (round-1 blocker). -/
structure UniformMachineCode extends EffectiveMachineCode where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-- **A uniformly-timed scheme exists**: the chapter-1
concrete scheme, with its time analysis made uniform.

**Proof sketch.** The concrete grammar of the chapter-1 scheme
(`encode := CodeTM.serialize`, `decode := codeDecode`, the encoding law from
`codeDecode_serialize_pad`), with an **independently constructed**
polynomial parser/simulator — the received generic compiler route is
arbitrary-time and its polynomial variant is explicitly superseded
(`MathlibBridge`), so no received time ledger is claimed (round-2 finding
1); the decoder's *correctness* lemmas are reused, its complexity is not.
The construction: (i) parse the nested simulator input keeping the deadline
in binary, and check the table's minimum-length guard
(`81 · (numStates + 1) ≤ rest.length`, `CodeParser`'s grammar) by **binary**
arithmetic before any per-state iteration — a huge declared state count
must never be expanded in unary; (ii) on success scan the linearly many
records with range checks (whence
`|(codeDecode α).serialize| ≤ max |α| 84`, the fallback's exact length);
(iii) simulate at most `t` source transitions under a binary countdown,
tracking the finite table, the heads, the visited work interval, and a
**three-way output status** (empty / exactly `[true]` / permanently other —
append-only output never returns), testing haltedness after the `t`-th
transition before declaring timeout; (iv) with `S := |α| + |x| + t + 1`,
bounded scans, lookups, and at most `t` rounds give `C·S^e` for a fixed
multitape machine, and `d ≥ max 1 (max C e)` gives `C·S^e ≤ d·S^d`. The
same parser emits the serialization prefix or the fallback serialization,
supplying the inherited canonizer field. Fill obligations, named: the
binary-guard parser; the simulation invariant with the three-way status;
the polynomial ledger; the degree arithmetic. **Continuation budget
certain.**

**Fill appendix (B5a, route Z).** Instantiate §12.11 at
`oneTapeMachineFormat`, as in the statement probe's `uniform_one`. The
polynomial canonizer and H1 supply the inherited canonizer and the two
simulator clauses. The canonizer and the uniform simulator are proved. -/
theorem exists_uniformMachineCode : Nonempty UniformMachineCode := by
  obtain ⟨C, dC, hC⟩ := oneTapeMachineFormat.exists_polyCanonizer
  obtain ⟨S, d, hS⟩ := oneTapeMachineFormat.exists_uniformSimulator
  exact ⟨{
    toEffectiveMachineCode := {
      toMachineCode := ⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩
      canonizer := C
      canonizerTime := fun n => dC * (n + 1) ^ dC
      canonizer_computes := hC }
    simulator := S
    simDegree := d
    simulator_accepts := fun α x t h => (hS α x t).1 h
    simulator_rejects := fun α x t h => (hS α x t).2 h }⟩

end Turing

namespace Complexity

open Turing

/-- The chosen uniformly-timed scheme for the `EXPCOM` cluster — the
`Complexity.TimeHierarchy.code` pattern over the existence `Turing.exists_uniformMachineCode`. -/
noncomputable def expCode : UniformMachineCode :=
  Classical.choice exists_uniformMachineCode

/-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
`⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
rendered over the uniformly-timed scheme `Complexity.expCode` (round-1
repair — see the module docstring) and the code-first nesting
`Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with "outputs `1` within
`2ⁿ` steps" as `Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in
the budget, since halting is absorbing). Strings that do not parse as such a
triple are not in the language; on genuine triples the decomposition is
unique (`Turing.pairEncode_injective` twice, then `List.length` on the
replicated tails). -/
def EXPCOM : Language Bool :=
  {z | ∃ (α x : List Bool) (n : ℕ),
    z = pairEncode α (pairEncode x (List.replicate n true)) ∧
    (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}

/-- A polynomial unary padding exponent pays for the quadratic normal-form
slowdown, uniformly at empty input and at exponent zero.

**Proof sketch.** Bound each constant by a power of two and absorb the added
one before squaring. The resulting exponent is at most a fixed multiple of
`(n + 1)^c`, since this quantity is positive and dominates `n^c`. -/
private lemma expcom_padding_bound (a b c n : ℕ) :
    b * (a * 2 ^ n ^ c + 1) ^ 2 ≤
      2 ^ ((b + 2 * (a + 1) + 2) * (n + 1) ^ c) := by
  have hE : 1 ≤ 2 ^ n ^ c := Nat.one_le_pow _ _ (by omega)
  have hinner : a * 2 ^ n ^ c + 1 ≤ 2 ^ (a + 1 + n ^ c) := by
    calc
      a * 2 ^ n ^ c + 1 ≤ (a + 1) * 2 ^ n ^ c := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      _ ≤ 2 ^ (a + 1) * 2 ^ n ^ c :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n := a + 1)))
      _ = 2 ^ (a + 1 + n ^ c) := (Nat.pow_add _ _ _).symm
  have hexponent : b + (a + 1 + n ^ c) * 2 ≤
      (b + 2 * (a + 1) + 2) * (n + 1) ^ c := by
    have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have hconst : b + 2 * (a + 1) ≤ (b + 2 * (a + 1)) * (n + 1) ^ c := by
      simpa using Nat.mul_le_mul_left (b + 2 * (a + 1)) hone
    have hpower : 2 * n ^ c ≤ 2 * (n + 1) ^ c := by gcongr; omega
    calc
      b + (a + 1 + n ^ c) * 2 = (b + 2 * (a + 1)) + 2 * n ^ c := by ring
      _ ≤ (b + 2 * (a + 1)) * (n + 1) ^ c + 2 * (n + 1) ^ c :=
        Nat.add_le_add hconst hpower
      _ = (b + 2 * (a + 1) + 2) * (n + 1) ^ c := by ring
  calc
    b * (a * 2 ^ n ^ c + 1) ^ 2 ≤ 2 ^ b * (2 ^ (a + 1 + n ^ c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := b)))
        (Nat.pow_le_pow_left hinner 2)
    _ = 2 ^ (b + (a + 1 + n ^ c) * 2) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hexponent

/-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
[AB09, Example 3.6(3), the first inclusion of the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`]

**Proof sketch.** Let `L ∈ EXP`, say decided by `M` within `a · 2^(n^c)`
(`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
`α_L := expCode.encode N`, recovered by
`Turing.MachineCode.decode_encode` (a **fixed** code: this inclusion never
needed uniformity, as the round-1 audit confirmed). Choose the padding exponent
`Q n := C · (n + 1)^c` with `C` absorbing `a`, the square, and the `+1`
normalizations, so that `N` outputs `[χ_L x]` within `2^(Q |x|)` steps on every
`x`. The reduction is `f x := pairEncode α_L (pairEncode x 1^(Q |x|))` —
polynomial-time by the chapter-2 padding cluster: the constant prefix
(`Complexity.polyTimeComputable_const`), the copy
(`Complexity.polyTimeComputable_id`), the unary padding emitter
(`Complexity.polyTimeComputable_polyUnary C c`), assembled by two applications
of `Complexity.PolyTimeComputable.pairEncode`. Membership: if `x ∈ L` then the
witness `(α_L, x, Q |x|)` puts `f x ∈ EXPCOM`; conversely a witness for
`f x ∈ EXPCOM` is forced to be exactly `(α_L, x, Q |x|)`
(`Turing.pairEncode_injective` twice, then `List.length` on the replicated
tails), and output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
verdict `[χ_L x]` forces `x ∈ L`. Conclude with
`Complexity.mem_POracle_of_polyTimeReducible`.

**Fill appendix (B5a).** Take `C = b + 2 * (a + 1) + 2`, where `b` is
the one-work-tape slowdown coefficient. `expcom_padding_bound` proves the
inequality for every input length, including zero, without an asymptotic
exception. The two pair injections force the full query witness. -/
theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
  intro L hL
  classical
  obtain ⟨c, a, M, hM⟩ := Set.mem_iUnion.mp hL
  obtain ⟨M', b, hk, hM'⟩ := M.one_work_tape_binary
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => a * 2 ^ n ^ c) hM
  obtain ⟨N, hN⟩ := exists_codeTM M' hk
  let C := b + 2 * (a + 1) + 2
  have hdec (x : List Bool) :
      N.toFinTM.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x]
        (2 ^ (C * (x.length + 1) ^ c)) :=
    ((hN x _ _).mpr (hM' x)).mono (expcom_padding_bound a b c x.length)
  apply mem_POracle_of_polyTimeReducible
  refine ⟨fun x => pairEncode (expCode.encode N)
      (pairEncode x (List.replicate (C * (x.length + 1) ^ c) true)),
    (polyTimeComputable_const (expCode.encode N)).pairEncode
      (polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary C c)), ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨expCode.encode N, x, C * (x.length + 1) ^ c, rfl, ?_⟩
    rw [expCode.toMachineCode.decode_encode]
    simpa [MultiTapeTM.indicator, hx] using hdec x
  · rintro ⟨α, y, n, heq, hy⟩
    have hpair :
        (expCode.encode N, pairEncode x (List.replicate (C * (x.length + 1) ^ c) true)) =
          (α, pairEncode y (List.replicate n true)) := pairEncode_injective heq
    have hcode := congrArg Prod.fst hpair
    have hinner : (x, List.replicate (C * (x.length + 1) ^ c) true) =
        (y, List.replicate n true) := pairEncode_injective (congrArg Prod.snd hpair)
    have hinput := congrArg Prod.fst hinner
    dsimp only at hcode hinput
    have hlen := congrArg List.length (congrArg Prod.snd hinner)
    simp only [List.length_replicate] at hlen
    rw [← hcode, expCode.toMachineCode.decode_encode, ← hinput, ← hlen] at hy
    have hout := hy.output_unique (hdec x)
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x = true := by
      simpa using hout.symm
    by_contra hx
    simp [MultiTapeTM.indicator, hx] at hi

/-- The unary deadline field, projected from a possibly malformed query. -/
private def expcom_tail (z : List Bool) : List Bool := pairSndD (pairSndD z)

/-- The guard checks both pair separators and the unary deadline field. -/
private def expcom_ok (z : List Bool) : Bool :=
  (pairDecode z).isSome && (pairDecode (pairSndD z)).isSome &&
    decide ((incFixed (expcom_tail z)).getD [] = [])

/-- Rebuild the uniform simulator's input, replacing the unary deadline exponent
by its little-endian power-of-two clock. Only guarded queries use this word. -/
private def expcom_simIn (z : List Bool) : List Bool :=
  pairEncode (pairEncode ((incFixed (expcom_tail z ++ [false])).getD []) (pairFstD z))
    (pairFstD (pairSndD z))

/-- Malformed queries are redirected to the fixed zero-deadline simulator input. -/
private def expcom_front (z : List Bool) : List Bool :=
  if expcom_ok z then expcom_simIn z else pairEncode (pairEncode [] []) []

/-- The guard accepts exactly the specified nested triples.

**Proof sketch.** Recover each pair from a successful parse, then use the empty
increment output to identify the unary tail. Conversely both pair parsers succeed
on an encoded triple and the all-`true` increment overflows. -/
private lemma expcom_ok_iff (z : List Bool) :
    expcom_ok z = true ↔ ∃ (α x : List Bool) (n : ℕ),
      z = pairEncode α (pairEncode x (List.replicate n true)) := by
  constructor
  · intro h
    have hp : ((pairDecode z).isSome = true ∧
        (pairDecode (pairSndD z)).isSome = true) ∧
        (incFixed (expcom_tail z)).getD [] = [] := by
      simpa only [expcom_ok, Bool.and_eq_true, decide_eq_true_eq] using h
    obtain ⟨⟨α, v⟩, ha⟩ := Option.isSome_iff_exists.mp hp.1.1
    have hz := eq_pairEncode_of_pairDecode z α v ha
    subst z
    have hv : (pairDecode v).isSome = true := by simpa using hp.1.2
    obtain ⟨⟨x, w⟩, hx⟩ := Option.isSome_iff_exists.mp hv
    have hv := eq_pairEncode_of_pairDecode v x w hx
    subst v
    have hw : w = List.replicate w.length true :=
      (incFixed_getD_eq_nil_iff w).mp (by simpa [expcom_tail] using hp.2)
    exact ⟨α, x, w.length, by rw [← hw]⟩
  · rintro ⟨α, x, n, rfl⟩
    have hinc : incFixed (List.replicate n true) = none := by
      simpa [incFixed] using incFixed_replicate_true_append n []
    simp [expcom_ok, expcom_tail, hinc, pairDecode_pairEncode]

/-- The guarded input reconstruction is polynomial-time.

**Proof sketch.** Compose the two projections, grammar tests, fixed-width
increment and whole-word equality test. Two conjunctions form the guard. Append
a zero and increment to build the clock, pair the three fields, then branch to
this input or the constant zero-deadline input. Every machine is a cited public
composition or primitive. -/
private lemma expcom_front_poly : PolyTimeComputable expcom_front := by
  have hi : PolyTimeComputable (fun w => (incFixed w).getD []) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_incFixed
  have ht : PolyTimeComputable expcom_tail :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hv : PolyTimeComputable (fun z => [(pairDecode z).isSome]) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
  have hu : PolyTimeComputable
      (fun z => [decide ((incFixed (expcom_tail z)).getD [] = [])]) := by
    simpa only [Function.comp_def] using
      (polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq [])).comp (hi.comp ht)
  have hg : PolyTimeComputable (fun z => [expcom_ok z]) :=
    polyTimeComputable_and
      (polyTimeComputable_and hv (hv.comp polyTimeComputable_pairSndD)) hu
  have hc : PolyTimeComputable (fun z => (incFixed (expcom_tail z ++ [false])).getD []) :=
    hi.comp ((polyTimeComputable_of_linear (FinTM.computesFunInTime_appendBit false)).comp ht)
  -- Use the public swap row for the simulator's clock-before-code layout.
  have hp : PolyTimeComputable (fun z =>
      pairEncode ((incFixed (expcom_tail z ++ [false])).getD []) (pairFstD z)) := by
    simpa only [Function.comp_def, pairSndD_pairEncode, pairFstD_pairEncode] using
      polyTimeComputable_pairSwap.comp (polyTimeComputable_pairFstD.pairEncode hc)
  have hs : PolyTimeComputable expcom_simIn :=
    hp.pairEncode (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite hg hs (polyTimeComputable_const (pairEncode (pairEncode [] []) []))

/-- On an encoded triple the front end supplies the simulator's canonical input. -/
private lemma expcom_front_triple (α x : List Bool) (n : ℕ) :
    expcom_front (pairEncode α (pairEncode x (List.replicate n true))) =
      pairEncode (pairEncode (Nat.bits (2 ^ n)) α) x := by
  have hok : expcom_ok (pairEncode α (pairEncode x (List.replicate n true))) = true :=
    (expcom_ok_iff _).mpr ⟨α, x, n, rfl⟩
  simp [expcom_front, hok, expcom_simIn, expcom_tail, incFixed_replicate_true_append,
    incFixed, bits_two_pow_eq_replicate]

/-- The polynomial front end and simulator budget fit a linear exponential.

**Proof sketch.** Since `m + 1 ≤ 2^m`, both `m + 1` and `m + 2^m + 1`
are at most `2^(m+1)`. Raising to the two fixed degrees and increasing both
exponents to their sum gives a common power; its positivity absorbs the final
two transitions. -/
private lemma expcom_decider_budget (C c d m : ℕ) :
    2 * (C * (m + 1) ^ c) + d * (m + 2 ^ m + 1) ^ d + 2 ≤
      (2 * C + d + 2) * 2 ^ ((c + d) * (m + 1)) := by
  have hm : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have hbase : m + 2 ^ m + 1 ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    omega
  have he (e : ℕ) (he : e ≤ c + d) :
      (2 ^ (m + 1)) ^ e ≤ 2 ^ ((c + d) * (m + 1)) := by
    rw [← Nat.pow_mul, Nat.mul_comm (m + 1) e]
    exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ he)
  have hp : (m + 1) ^ c ≤ 2 ^ ((c + d) * (m + 1)) :=
    (Nat.pow_le_pow_left (by omega : m + 1 ≤ 2 ^ (m + 1)) c).trans (he c (by omega))
  have hs : (m + 2 ^ m + 1) ^ d ≤ 2 ^ ((c + d) * (m + 1)) :=
    (Nat.pow_le_pow_left hbase d).trans (he d (by omega))
  have hone : 1 ≤ 2 ^ ((c + d) * (m + 1)) := Nat.one_le_pow _ _ (by omega)
  calc
    _ = (2 * C) * (m + 1) ^ c + d * (m + 2 ^ m + 1) ^ d + 2 * 1 := by ring
    _ ≤ (2 * C) * 2 ^ ((c + d) * (m + 1)) +
        d * 2 ^ ((c + d) * (m + 1)) + 2 * 2 ^ ((c + d) * (m + 1)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hp)
        (Nat.mul_le_mul_left _ hs)) (Nat.mul_le_mul_left _ hone)
    _ = _ := by ring

/-- A genuine triple is in `EXPCOM` exactly when its bounded computation accepts.

**Proof sketch.** Inject the outer pair and then the inner pair; the lengths of
the equal unary tails identify the exponent. This is the one private reuse of
the frozen padding reduction's inline parse-uniqueness argument. -/
private lemma expcom_mem_triple (α x : List Bool) (n : ℕ) :
    pairEncode α (pairEncode x (List.replicate n true)) ∈ EXPCOM ↔
      (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n) := by
  constructor
  · rintro ⟨β, y, m, hz, hm⟩
    have hp : (α, pairEncode x (List.replicate n true)) =
        (β, pairEncode y (List.replicate m true)) := pairEncode_injective hz
    have hα : α = β := congrArg Prod.fst hp
    have hi : (x, List.replicate n true) = (y, List.replicate m true) :=
      pairEncode_injective (congrArg Prod.snd hp)
    have hx : x = y := congrArg Prod.fst hi
    have hn : n = m := by
      simpa only [List.length_replicate] using congrArg List.length (congrArg Prod.snd hi)
    simpa only [hα, hx, hn] using hm
  · intro h
    exact ⟨α, x, n, rfl, h⟩

/-- The uniform simulator computes the membership bit on the front end's image.

**Proof sketch.** On a genuine triple, the front end builds the canonical clock
and the two uniform simulator clauses decide the unique parsed computation.
Every component length is at most the original query length, so its exponential
budget dominates the simulator's polynomial in the numerical deadline. A failed
guard excludes membership and selects the zero-deadline input; its simulated
initial state is live, hence the simulator's rejection clause applies. -/
private lemma expcom_simulator_on_image (z : List Bool) :
    expCode.simulator.ComputesInTime (expcom_front z) [MultiTapeTM.indicator EXPCOM z]
      (expCode.simDegree * (z.length + 2 ^ z.length + 1) ^ expCode.simDegree) := by
  classical
  by_cases hok : expcom_ok z = true
  · obtain ⟨α, x, n, rfl⟩ := (expcom_ok_iff z).mp hok
    rw [expcom_front_triple]
    have hlen : α.length + x.length ≤
        (pairEncode α (pairEncode x (List.replicate n true))).length := by
      simp only [length_pairEncode, List.length_replicate]
      omega
    have hn : n ≤ (pairEncode α (pairEncode x (List.replicate n true))).length := by
      simp only [length_pairEncode, List.length_replicate]
      omega
    have hb : expCode.simDegree * (α.length + x.length + 2 ^ n + 1) ^ expCode.simDegree ≤
        expCode.simDegree *
          ((pairEncode α (pairEncode x (List.replicate n true))).length +
            2 ^ (pairEncode α (pairEncode x (List.replicate n true))).length + 1) ^
          expCode.simDegree := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      exact Nat.add_le_add_right
        (Nat.add_le_add hlen (Nat.pow_le_pow_right (by omega) hn)) 1
    by_cases hacc : (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)
    · have hmem := (expcom_mem_triple α x n).mpr hacc
      simpa [MultiTapeTM.indicator, hmem] using
        (expCode.simulator_accepts α x (2 ^ n) hacc).mono hb
    · have hnot : pairEncode α (pairEncode x (List.replicate n true)) ∉ EXPCOM :=
        fun hmem => hacc ((expcom_mem_triple α x n).mp hmem)
      simpa [MultiTapeTM.indicator, hnot] using
        (expCode.simulator_rejects α x (2 ^ n) hacc).mono hb
  · have hnot : z ∉ EXPCOM := by
      rintro ⟨α, x, n, hz, _⟩
      exact hok ((expcom_ok_iff z).mpr ⟨α, x, n, hz⟩)
    have hzero : ¬ (expCode.decode []).toFinTM.ComputesInTime [] [true] 0 :=
      FinTM.not_computesInTime_zero _ _ _
    have hu : expCode.simulator.ComputesInTime (expcom_front z)
        [MultiTapeTM.indicator EXPCOM z] expCode.simDegree := by
      simpa [expcom_front, hok, MultiTapeTM.indicator, hnot] using
        expCode.simulator_rejects [] [] 0 hzero
    apply hu.mono
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left expCode.simDegree
      (Nat.one_le_pow expCode.simDegree (z.length + 2 ^ z.length + 1) (Nat.succ_pos _))

/-- `EXPCOM` has a decider with a linear exponential time bound.
[AB09, Example 3.6(3), the query dispatcher]

**Proof sketch.** Use the polynomial front end to validate and rebuild the
simulator input, compose with the uniform simulator only on that image, then
absorb the polynomial setup and the simulator's budget into one fixed linear
exponent. Malformed queries have already been routed to the rejecting
zero-deadline input. -/
private theorem expcom_decider :
    ∃ (D : FinTM Bool) (A B : ℕ), D.DecidesInTime EXPCOM fun m => A * 2 ^ (B * (m + 1)) := by
  obtain ⟨M, C, c, hM⟩ := expcom_front_poly
  obtain ⟨D, hD⟩ := FinTM.exists_comp_on_image M expCode.simulator expcom_front
    (fun z => [MultiTapeTM.indicator EXPCOM z]) (fun n => C * (n + 1) ^ c)
    (fun n => expCode.simDegree * (n + 2 ^ n + 1) ^ expCode.simDegree)
    hM expcom_simulator_on_image
  exact ⟨D, 2 * C + expCode.simDegree + 2, c + expCode.simDegree,
    fun z => (hD z).mono (expcom_decider_budget C c expCode.simDegree z.length)⟩

/-- A constant bound is exponential-polynomial. -/
private theorem expcom_expPoly_const (A : ℕ) : ExpPoly fun _ => A :=
  (expPoly_poly A 0).of_le fun n => by simp

/-- `A · 2^(K·(n + 1)^k)` is exponential-polynomial. -/
private theorem expcom_expPoly_mul_two_pow (A K k : ℕ) : ExpPoly fun n => A * 2 ^ (K * (n + 1) ^ k) := by
  refine ⟨A + K, k, fun n => ?_⟩
  have h1 : A < 2 ^ A := Nat.lt_two_pow_self
  have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc A * 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ A * 2 ^ (K * (n + 1) ^ k) := Nat.mul_le_mul_right _ h1.le
    _ = 2 ^ (A + K * (n + 1) ^ k) := by rw [pow_add]
    _ ≤ 2 ^ ((A + K) * (n + 1) ^ k) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- **The summit's ledger** ([AB09, Example 3.6(3)]; the P3.2 round-2 uniform ledger in
this route's shape): the bound returned by `Complexity.exists_proj_decider` around the
certificate shell, the simulated choice machine and the `EXPCOM` decider is
exponential-polynomial.

**Proof sketch.** Bound the shell's word length `g = n + C·(n + 1)^k` strictly, by
`g + 1 ≤ G = (C + 1)·(n + 1)^(k + 1)`, so that `2g + 3 ≤ 3G`. Each factor is then dominated by an
exponential-polynomial in `n`: powers of `G` are polynomials, and
`A·2^(B·(2g + 3)) ≤ A·2^(3B(C + 1)(n + 1)^(k + 1))`. `ExpPoly` is closed under products,
sums and pointwise upper bounds (`of_le`). (Maintainer, fills-6 integration.) -/
private theorem expcom_summit_budget (a' A B b e b' C k : ℕ) :
    ExpPoly fun n => b' * 2 ^ (C * (n + 1) ^ k) *
      (b * ((n + C * (n + 1) ^ k + 1) ^ e +
          a' * (2 * (n + C * (n + 1) ^ k) + 2 + 1) *
            (2 * (n + C * (n + 1) ^ k) + 2 + 1 +
              A * 2 ^ (B * (2 * (n + C * (n + 1) ^ k) + 2 + 1)))) +
        (n + C * (n + 1) ^ k + 1) ^ (k + 1)) := by
  have hG : ∀ n : ℕ, n + C * (n + 1) ^ k + 1 ≤ (C + 1) * (n + 1) ^ (k + 1) := by
    intro n
    have h1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h3 : C * (n + 1) ^ k ≤ C * (n + 1) ^ (k + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
    calc n + C * (n + 1) ^ k + 1 = (n + 1) + C * (n + 1) ^ k := by ring
      _ ≤ (n + 1) ^ (k + 1) + C * (n + 1) ^ (k + 1) := Nat.add_le_add h1 h3
      _ = (C + 1) * (n + 1) ^ (k + 1) := by ring
  have eG : ∀ d, ExpPoly fun n => ((C + 1) * (n + 1) ^ (k + 1)) ^ d := fun d =>
    (expPoly_poly ((C + 1) ^ d) ((k + 1) * d)).of_le fun n =>
      le_of_eq (by rw [mul_pow, ← pow_mul])
  have e3G : ExpPoly fun n => 3 * ((C + 1) * (n + 1) ^ (k + 1)) :=
    (expPoly_poly (3 * (C + 1)) (k + 1)).of_le fun n => le_of_eq (by ring)
  have eExp := expcom_expPoly_mul_two_pow A (3 * B * (C + 1)) (k + 1)
  refine ((expcom_expPoly_mul_two_pow b' C k).mul (((expcom_expPoly_const b).mul ((eG e).add
    (((expcom_expPoly_const a').mul e3G).mul (e3G.add eExp)))).add (eG (k + 1)))).of_le
    fun n => ?_
  have hg := hG n
  generalize hgdef : n + C * (n + 1) ^ k = g at hg ⊢
  generalize hGdef : (C + 1) * (n + 1) ^ (k + 1) = G at hg ⊢
  have h3 : 2 * g + 2 + 1 ≤ 3 * G := by omega
  have hexp : A * 2 ^ (B * (2 * g + 2 + 1)) ≤ A * 2 ^ (3 * B * (C + 1) * (n + 1) ^ (k + 1)) := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by omega)
    calc B * (2 * g + 2 + 1) ≤ B * (3 * G) := Nat.mul_le_mul_left _ h3
      _ = 3 * B * (C + 1) * (n + 1) ^ (k + 1) := by rw [← hGdef]; ring
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add _ (Nat.pow_le_pow_left hg _)
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add (Nat.pow_le_pow_left hg _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) (Nat.add_le_add h3 hexp)

/-- **The fill summit of the `EXPCOM` cluster**: `NP^EXPCOM ⊆ EXP` — a
deterministic exponential-time machine can enumerate all branches of a
polynomial-time oracle NDTM and answer its `EXPCOM` queries itself.
[AB09, Example 3.6(3), the last inclusion; summit 2 of
`AroraBarakChapters3-4Plan.md` §6, continuation budget certain]

**Proof sketch.** Let `L ∈ NP^EXPCOM`: a well-formed oracle NDTM `N` decides
`L` with oracle `EXPCOM` within `p n := c · (n^k + 1)`. The deciding plain
machine, on input `x` of length `n`:

1. **Choice-word enumeration.** Iterate over all `2^(p n)` choice words of
   length exactly `p n` as a fixed-width counter, one round per word, in the
   `Complexity.NP_subset_EXP` enumerator pattern
   (`Complexity.exists_proj_decider` / `enumLoop_run`: fixed-width carry,
   captured round verdict, reversible scratch restoration, accept-or-increment
   control).
2. **Per-step simulation.** Within a round, simulate
   `Turing.OracleNDTM.runWith` step by step under the current word — the
   step-by-step compilation invariant of the chapter-2 2B cluster
   (`ClassNP/Nondeterminism.lean`), extended by one new case: the query state.
3. **Query answering.** When the simulated state is `qQuery`, read the
   simulated query tape `z` (`Turing.OracleTM.queryString` contract), parse it
   as `pairEncode α' (pairEncode x' 1^(n'))` by aligned two-bit parsing (the
   `Turing.pairDecode` layer; `TCSlib.Complexity.TuringMachine.CodeParser`
   machine precedent) — malformed strings answer "no" — and decide
   `z ∈ EXPCOM` by running **`expCode.simulator`** on
   `⟨⟨bits 2^(n'), α'⟩, x'⟩`: its two uniform clauses make the answer the
   exact membership bit at cost `simDegree · (|α'| + |x'| + 2^(n') + 1) ^
   simDegree` — **uniform in the query's code**, which is the entire round-1
   repair (query codes vary with the branch; `Turing.timed_universal`'s
   per-code constant cannot pay for them) — with parse-uniqueness
   (`Turing.pairEncode_injective` twice, then `List.length` on the
   replicated tails) identifying the witness decomposition.
4. **Ledger.** Each branch submits queries of length at most the elapsed
   budget (`Turing.OracleTM.queryString_length_le` transferred along the
   simulation invariant), so `n' ≤ p n`, `|α'|, |x'| ≤ p n`, and one oracle call costs
   `simDegree · (3 · p n + 2^(p n) + 1) ^ simDegree = 2^(O(p n))` simulator
   steps; a round is `p n` simulated
   steps of which each costs at most one call: the total over `2^(p n)` rounds
   is `2^(O(p n) )·(2^(p n))^2 = 2^(O(n^k))`, inside `DTIME (2^(n^(k+1)))` by
   `Complexity.DTIME`'s constant absorption — so `L ∈ EXP`.
5. **Acceptance.** `x ∈ L` iff some length-`p n` branch accepts
   (`Turing.FinOracleNDTM.DecidesInTime`, with all-branch halting making every
   round's verdict defined); the enumerator's existential sweep returns exactly
   this disjunction.

Fill obligations, named for the brief: the query-dispatcher routine (parse +
clocked universal call + resume seam) and its capture discipline; the
simulation invariant tying the host's configuration coding to `runWith`; the
budget normalization into `EXP`'s `2^(n^c)` form.

**Fill appendix (B5b, the §12.10 compositional route).** The hand-built route
above is superseded by design §12.10, decision 1, and wave-1 note 42.
`exists_proj_decider` enumerates certificates around the W2-V certificate shell
(`FinTM.exists_certificateShell`). The W2-C choice-word machine
(`FinOracleNDTM.exists_choiceTM`) handles nondeterministic choices; W2-S's single
oracle-call trace (`FinOracleTM.exists_plain_simulation_of_monotone`) supplies
the per-step simulation and resume seam, from the preloaded choice word.
The private `expcom_decider` answers queries by parsing, rebuilding the canonical
simulator input, and composing `expCode.simulator` only on that front end's image;
malformed queries select a fixed rejecting zero-deadline input. The transcribed
`ExpPoly` ledger absorbs the simulator, shell and projection-enumerator budgets.
The plain oracle simulation (`FinOracleTM.exists_plain_simulation`), the canonizer
(`MachineFormat.exists_polyCanonizer`) and the uniform simulator
(`MachineFormat.exists_uniformSimulator`) are proved. -/
theorem NPOracle_EXPCOM_subset_EXP : NPOracle EXPCOM ⊆ EXP := by
  intro L hL
  obtain ⟨k, a, N, hN⟩ := Set.mem_iUnion.mp hL
  obtain ⟨Mc, jc, hMc⟩ := FinOracleNDTM.exists_choiceTM N
  obtain ⟨D, A, B, hD⟩ := expcom_decider
  have hτ : Monotone fun m => A * 2 ^ (B * (m + 1)) := fun m m' hm =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega)))
  obtain ⟨P, a', hk, hP⟩ :=
    FinOracleTM.exists_plain_simulation_of_monotone Mc D EXPCOM _ hτ hD
  let jP : Fin P.k := ⟨jc.castSucc, lt_of_lt_of_le jc.castSucc.isLt hk⟩
  have hshell : ∀ x u : List Bool, u.length = 2 * a * (x.length + 1) ^ k →
      (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) jP u))
          ((fun m => a' * (2 * m + 2 + 1) *
            (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) (x.length + u.length))).state =
          none ∧
        (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) jP u))
          ((fun m => a' * (2 * m + 2 + 1) *
            (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) (x.length + u.length))).output =
          N.choiceOut EXPCOM x u := by
    intro x u _
    obtain ⟨h1, h2⟩ := hMc EXPCOM x u
    have hw : Function.update (fun _ : Fin (Mc.k + 1) => ([] : List Bool)) jc.castSucc u
        (Fin.last Mc.k) = [] := Function.update_of_ne (Fin.castSucc_ne_last jc).symm _ _
    obtain ⟨s, hs, hs1, hs2⟩ := hP x _ hw _ h1
    rw [FinTM.prefixWords_update _ _ hk] at hs1 hs2
    have hle : s ≤ a' * (2 * (x.length + u.length) + 2 + 1) *
        (2 * (x.length + u.length) + 2 + 1 +
          A * 2 ^ (B * (2 * (x.length + u.length) + 2 + 1))) := by
      refine hs.trans ?_
      have hu : u.length ≤ x.length + u.length := Nat.le_add_left _ _
      have h3 : 2 * u.length + 2 + 1 ≤ 2 * (x.length + u.length) + 2 + 1 := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h3)
        (Nat.add_le_add h3 (hτ (by omega : 2 * u.length + 2 ≤ 2 * (x.length + u.length) + 2)))
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs1]
      exact hs1
    · dsimp only
      rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs1]
      exact hs2.trans h2
  obtain ⟨V, bV, e, hV⟩ :=
    FinTM.exists_certificateShell P jP (2 * a) k (N.choiceOut EXPCOM)
      (fun m => a' * (2 * m + 2 + 1) * (2 * m + 2 + 1 + A * 2 ^ (B * (2 * m + 2 + 1)))) hshell
  obtain ⟨b', E, hE⟩ := exists_proj_decider (2 * a) k _ _ V hV
  rw [FinTM.certificateShell_proj] at hE
  have hLeq : {x : List Bool | ∃ u, u.length = 2 * a * (x.length + 1) ^ k ∧
      N.choiceOut EXPCOM x u = [true]} = L :=
    Set.ext fun x => (FinOracleNDTM.mem_iff_exists_choiceOut hN x).symm
  rw [hLeq] at hE
  exact ExpPoly.mem_EXP (expcom_summit_budget a' A B bV e b' (2 * a) k)
    ⟨1, E, fun x => (hE x).mono (Nat.le_of_eq (Nat.one_mul _).symm)⟩

/-- **`P^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊇` is `Complexity.EXP_subset_POracle_EXPCOM`; `⊆` chains
`Complexity.POracle_subset_NPOracle` with
`Complexity.NPOracle_EXPCOM_subset_EXP`. -/
theorem POracle_EXPCOM_eq_EXP : POracle EXPCOM = EXP := by
  exact Set.Subset.antisymm
    ((POracle_subset_NPOracle EXPCOM).trans NPOracle_EXPCOM_subset_EXP)
    EXP_subset_POracle_EXPCOM

/-- **`NP^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊆` is `Complexity.NPOracle_EXPCOM_subset_EXP`; `⊇` chains
`Complexity.EXP_subset_POracle_EXPCOM` with
`Complexity.POracle_subset_NPOracle`. -/
theorem NPOracle_EXPCOM_eq_EXP : NPOracle EXPCOM = EXP := by
  apply Set.Subset.antisymm NPOracle_EXPCOM_subset_EXP
  simpa only [POracle_EXPCOM_eq_EXP] using POracle_subset_NPOracle EXPCOM

/-- **Relative to `EXPCOM`, determinism and nondeterminism coincide**:
`P^EXPCOM = NP^EXPCOM` — the `A` half of the Baker-Gill-Solovay theorem.
[AB09, Example 3.6(3), cited by the proof of Theorem 3.7]

**Proof sketch.** Chain `Complexity.POracle_EXPCOM_eq_EXP` with the inverse of
`Complexity.NPOracle_EXPCOM_eq_EXP`. -/
theorem POracle_EXPCOM_eq_NPOracle_EXPCOM : POracle EXPCOM = NPOracle EXPCOM := by
  exact POracle_EXPCOM_eq_EXP.trans NPOracle_EXPCOM_eq_EXP.symm

end Complexity
