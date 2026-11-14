# Codex fill · hash-and-sign is one-time secure (`hashAndSign_oneTimeSecure`, Theorem 144.1)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `hash-sign`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `hashAndSign_oneTimeSecure` of [PS10, Theorem 144.1] in `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/hash-sign` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/hash-sign/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill hash-sign: checkpoint N` and `fill hash-sign: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `hash-sign/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem hashAndSign_oneTimeSecure (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (hdom : ∀ n i x, H.inDom n i x = true)
    (hH : H.CollisionResistant) (hS : S.OneTimeSecure) :
    (hashAndSign H S hlen).OneTimeSecure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. There are no section variables. `hashAndSign H S hlen` signs `h_i(m)` with `S` (`hsSign`, `hsVerFun`, `hashAndSign_sign/_ver`); `OneTimeSecure` is in `Signatures/Defs.lean` and `CollisionResistant` in `Hashing/CollisionResistant.lean`. The file imports `Lamport.lean`, which the parallel `lamport` fill owns: do not edit it, and do not depend on its proof.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `hsSign`, `hsVerFun`, the hash-and-sign machines and readers, `hashAndSign_sign`, `hashAndSign_ver` and the other `hashAndSign_*` fields | owned file |
| `SignatureScheme`, `OneTimeSecure` and its experiment readers | `Authentication/Signatures/Defs.lean` |
| `CRH`, `CollisionResistant` and readers | `Hashing/CollisionResistant.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, the `PolyHandler`/`InteractiveHandler` readers, `fwdHandler` | `Games/Efficiency.lean`, `Games/Forwarding.lean` |
| `NUPPT.exists_comp`, `exists_withAdvice(On)`; run/coin readers; `Negligible.add`, `mono` | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the collision finder (sketch step 2).** Build `B(1^n, i)` with T1: sample `(pk, sk)`, run `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, output `(m, m')`. Show that `B` collides whenever `A` forges with `h_i(m') = h_i(m)` (`hdom` gives domain membership). Send this checkpoint.
2. **Checkpoint 2 · the forger against `S` (sketch step 3).** Build `C^{Sign_sk}(1^n, pk)` with T2 (`perCall = 1`, `finCall = 0`): sample `i`, forward `A`'s query as `h_i(m)`, output `(h_i(m'), σ')`. Show this is a valid one-time forgery against `S` when `A` made no query or `h_i(m') ≠ h_i(m)`. Send this checkpoint.
3. **Final · the union (sketch step 4).** `A`'s success is at most `B`'s plus `C`'s, so it is negligible.

Check the edge cases: no query; a query outside the domain or of the wrong length; `m' = m`; malformed signatures; the codecs' timeout outputs; `hlen` length casts.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Authentication/Signatures/HashAndSign.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Authentication/Signatures/HashAndSign/`. The owned file imports them precisely and
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
    must be the removal of `hashAndSign_oneTimeSecure`.
- **Axioms.**
  - Print the axioms of `hashAndSign_oneTimeSecure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
