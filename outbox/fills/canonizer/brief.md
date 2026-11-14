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
