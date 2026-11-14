# Codex fill · the discrete-log hash is collision-resistant (`dlHash_crh`, Theorem 142.3)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `dl-crh`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `dlHash_crh` of [PS10, Theorem 142.3] in `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/dl-crh` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/dl-crh/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill dl-crh: checkpoint N` and `fill dl-crh: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `dl-crh/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem dlHash_crh (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) (hDL : G.DLHard) :
    (dlHash H G).Compresses ∧ (dlHash H G).CollisionResistant := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The section variable is `{V : List Bool → Prop}`. `dlHash H G` is Protocol 142.2 as a `CRH` (keys `⟨i, y⟩`, domain `{(x, b) : x < m}`, range `Z_p^*`); `Compresses` and `CollisionResistant` are in `Hashing/CollisionResistant.lean`; `G.DLHard` is the discrete-log assumption (`Candidates/DiscreteLog.lean`). Read the module docstring's source notes on the domain and the full group.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `dlHashGenFun`, `dlHashEval`, `dlHashMul`, `dlHashPow` and their `_eq`/`polyTimeComputable_*`; `dlHash` and its `simps` fields | owned file |
| `CRH`, `Compresses`, `CollisionResistant` and readers | `Hashing/CollisionResistant.lean` |
| `ExpGroupGen`, `DLHard`, `expGen`, `expSampleRaw`, `expF_injective`, `statClose_sampleBelowL`, `dlP`, `dlM`, `ExpValid`, `ArithmeticFP` | `Candidates/DiscreteLog.lean` and the ch. 2–4 candidate layer |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_reparam`; run/coin readers; `Negligible` closure (`add`, `mono`, `negligible_two_pow_neg`) | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · compression and collision shape (sketch steps 1–2).** Prove `Compresses` from `G.n₀` on (valid index, `|D_i| = 2m = 2(p − 1)`, `|R_i| = p − 1`, `h` lands in the units). Prove that a collision has `b ≠ b'` (`expF_injective`). Send this checkpoint.
2. **Checkpoint 2 · the reduction (sketch step 3).** Build `B(1^n, ⟨i, g^z⟩)`: run `A` on `⟨i, g^z⟩` and output `x − x' mod m` (or `x' − x`) from a collision. Prove it is a NUPPT and that it succeeds whenever `A` collides on that key. Send this checkpoint.
3. **Final · the key distribution (sketch step 4).** `A`'s key is `g^w` with `w` from the sampler, within `2^{-n}` of uniform (`statClose_sampleBelowL`). Conclude that `A`'s collision probability is at most `B`'s DL probability plus `2^{-n}`, negligible by `hDL`.

Check the edge cases: parameters below `G.n₀` (finite exception); invalid indices; `b = b'`; `x = x'`; inputs outside `D_i` (the `inDom` guard); `y = g^w` with `w = 0`.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Hashing/FromDiscreteLog.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Hashing/FromDiscreteLog/`. The owned file imports them precisely and
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

- **Bootstrap.** Bootstrap from `order.txt` (170 modules) and the narrow `roots.txt` (87), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (22 declarations in 12 modules). The only change
    must be the removal of `dlHash_crh`.
- **Axioms.**
  - Print the axioms of `dlHash_crh`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
