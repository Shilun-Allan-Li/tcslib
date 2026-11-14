# Codex fill · Lamport is one-time secure (`lamport_oneTimeSecure`, Theorem 137.2)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `lamport`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `lamport_oneTimeSecure` of [PS10, Theorem 137.2] in `TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/lamport` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/lamport/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill lamport: checkpoint N` and `fill lamport: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `lamport/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The section variables are `L : PolyExpr`, `f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool)`, `E`, `hE : PolyTimeComputable E` and `hfE` (`E` evaluates `f` on `advInput`). `lamportOWF L f` is `f` as a one-way collection; `StrongOneWay` is in `Asymptotic/Collections.lean`. `HashAndSign.lean` imports this file; the parallel `hash-sign` fill does not depend on this proof.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `lamportGen`, `lamportSign`, `lamportVerFun`, `lamportOWF`, the `lamport_*` field readers and the machine readers | owned file |
| `SignatureScheme`, `OneTimeSecure` and its experiment readers | `Authentication/Signatures/Defs.lean` |
| `StrongOneWay` and readers | `Asymptotic/Collections.lean`, `Asymptotic/OneWay.lean` |
| T1 `Games.exists_handlerMachine` and the `PolyHandler` readers | `Games/Efficiency.lean` |
| `NUPPT.exists_withAdvice` (bounded advice for the best position), `exists_comp`; run/coin readers; `Negligible` closure incl. polynomial factors (`mul_pow`, `const_mul`, `mono`) | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `coinBlock`, `FunFamily.blocks`, `ofFn_blocks`, `Foundations/BitLists` | `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the planted experiment (sketch steps 1–3).** Define the reduction experiment for a fixed position `(i, c)`: plant `y` at `(i, c)`, answer the query when `m_i ≠ c` and abort otherwise, and extract `σ'_i` from a forgery with `m'_i = c`. Prove the coupling with the honest run: on the jointly favourable pairs the experiments agree and extraction inverts `y`. Send this checkpoint.
2. **Checkpoint 2 · the averaging bound (sketch steps 3–4).** Count the favourable pairs (`≥ 1/(2n)`, exactly `1/2` with no query) and average over successful honest runs to get inversion probability `≥ ε(n)/(2n)` for the uniform position; then a best position per length is at least as good. Send this checkpoint.
3. **Final · the machine and negligibility (sketch step 5).** Apply T1 to the extended input `⟨y, i(n)⟩`, supply the best position with `NUPPT.exists_withAdvice`, and conclude that `ε` is negligible by one-wayness and polynomial-factor closure.

Check the edge cases: `n = 0` (finite exception); no query; a query or forgery of the wrong length; `m' = m`; malformed signatures; an abort branch reached by a successful forger.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Authentication/Signatures/Lamport.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Authentication/Signatures/Lamport/`. The owned file imports them precisely and
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

- **Bootstrap.** Bootstrap from `order.txt` (150 modules) and the narrow `roots.txt` (82), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (22 declarations in 12 modules). The only change
    must be the removal of `lamport_oneTimeSecure`.
- **Axioms.**
  - Print the axioms of `lamport_oneTimeSecure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
