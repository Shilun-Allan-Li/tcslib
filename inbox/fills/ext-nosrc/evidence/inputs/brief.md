# Codex fill · no efficient one-bit extractor for efficient sources (`not_isExtractor_effSources`, Theorem 183.6)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `ext-nosrc`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `not_isExtractor_effSources` of [PS10, Theorem 183.6] in `TCSlib/Cryptography/Randomness/Extraction.lean`. The
statement passed Gate 06 (prong D, chapters 5–8 statements) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/ext-nosrc` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/ext-nosrc/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill ext-nosrc: checkpoint N` and `fill ext-nosrc: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `ext-nosrc/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem not_isExtractor_effSources (Ext : List Bool → List Bool) (hExt : PolyTimeComputable Ext)
    (n : ℕ) :
    ¬ IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. There are no section variables. `effSources k n` is the set of laws `samplerLaw S n` of uniform PPT samplers that are `k(n)`-sources, `extBit Ext n` is the first output bit, and `IsExtractor` is the `ε`-closeness to `U_1` for every source of the class (`InformationTheory/Extractors.lean`).

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `samplerLaw`, `samplerLaw_apply`, `samplerLaw_prob`, `effSources_iff`, `extBit_eq` | owned file |
| `IsExtractor` and its readers, `abs_probTrue_sub_le_statDist` | `InformationTheory/Extractors.lean` |
| `FinDist.IsSource`, `isSource_uniform`, `IsSource.mono` (`Entropy.lean:154`) | `InformationTheory/Entropy.lean` |
| `FinDist` laws (`uniform`, `map`, `prob`), statistical distance | `InformationTheory/FinDist.lean`, `StatisticalDistance.lean` |
| `polyTimeComputable_ite`, `polyTimeComputable_iterateFind`; `NUPPT.ofPolyTimeUniform` and its `runAt`/uniform readers | `Complexity/ClassNP/PolyTimePairing.lean`, `Complexity/Randomized/Repetition.lean`, `Asymptotic/Adversary.lean` |
| `padFin`, `coinBlock`, `FunFamily.blocks`, `Foundations/BitLists` | `Games/BitCodec.lean`, `Asymptotic/Adversary.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the uniform witness (sketch steps 1–2).** Show that `U_n` is `samplerLaw` of the uniform PPT that outputs its coins and is an `(n − 2)`-source. If `extBit Ext n` is not `1/4`-close to `U_1` on it, conclude. Otherwise derive `q = Pr[Ext(U_n) = 1] ≥ 1/4`. Send this checkpoint.
2. **Checkpoint 2 · the rejection sampler (sketch steps 3–4).** Build the sampler with `11n` coins: try up to 10 `n`-bit blocks for `Ext(x) = 1`, else output the 11th block. Prove it is a uniform PPT, compute its law as the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)`, and show both components, hence the mixture, are `(n − 2)`-sources. Send this checkpoint.
3. **Final · the bound (sketch step 5).** `Pr[Ext(X) = 1] = 1 − (1 − q)^{11} ≥ 1 − (3/4)^{11} > 3/4`, so the distance from `U_1` exceeds `1/4`.

Check the edge cases: small `n` (`n = 0, 1, 2`, where `n − 2 ≤ 0` and `S` may be all or nothing); `q = 1`; `Ext` outputs of length `0` (`padFin 1` reads `false`); the `11n` coin split.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Randomness/Extraction.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Randomness/Extraction/`. The owned file imports them precisely and
  gets a `## Contents` list.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines and must be split before it grows. Do not add to it.
  - If a lemma belongs in an existing file, put it in your helper module and list it as a promotion request.
  - If a reader of another file's definition is missing, escalate: record the exact obligation and the reader you
    need, and push a checkpoint.
- **Parallel fills.** Four Codex fills (`ext-nosrc`, `dl-crh`, `hash-sign`, `lamport`) and one Claude fill
  (`cca2-ett`) run from the same base. Edit only your own owned file and helper directory.
- **Duplication (binding).**
  - Do not copy public lemmas: import them.
  - Do not copy private lemmas of another file. If you need one, re-derive it from published readers in your helper
    module, disclose it in `REPORT.md` as **"overlap: <file> <item>"**, and keep its statement general.
  - Any other generic probability, machine or list fact goes on your promotion list. Grep first, and report the
    searches.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global simp
  attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Add no `@[simp]`. A new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file. The owned file's
  definitions are foreign to your helpers.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (201 modules) and the narrow `roots.txt` (80), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (21 declarations in 11 modules). The only change
    must be the removal of `not_isExtractor_effSources`.
- **Axioms.**
  - Print the axioms of `not_isExtractor_effSources`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, and report every failing declaration.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. It must show no new FAIL.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests;
  - every "overlap" item;
  - the evidence.

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
