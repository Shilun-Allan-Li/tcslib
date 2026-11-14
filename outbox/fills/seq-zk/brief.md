# Claude fill · sequential repetition preserves zero-knowledge and interactive proofs (the five `seqRep` theorems, Theorem 175.1)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `seq-zk`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep` of [PS10, §7.2.1, Theorem 175.1] and [Gol01, §4.3.4] in
`TCSlib/Cryptography/Composability/SequentialZK.lean`. The statements passed the prong C statement phase, Gate 03 (rulings G3-3, G3-4, G3-7d) and Gate 06,
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible: the statements passed their gates, the sketches are explicit, and the iterate hosts and hybrid lemmas exist. No dependency on an admitted target. The risk is size: the checkpoints are ordered so that each delivers whole declarations, and a final that proves only some of the five is allowed (see *Partial delivery*).

**Estimated size:** 5,000–10,000 lines in roughly 10–15 helper modules, the largest unit of this batch. For calibration, one theorem (cca2-ett) landed 5,364 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/seq-zk` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/seq-zk/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/seq-zk/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill seq-zk: checkpoint N` and `fill seq-zk: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
    ZK (π.seqRep Q) R := by
  sorry
```

```lean
theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
  sorry
```

```lean
theorem InteractiveProof.seqRep {L : Language Bool} (h : InteractiveProof π L) (Q : PolyExpr)
    (hQ : ∀ n, 1 ≤ Q.eval n) : InteractiveProof (π.seqRep Q) L := by
  sorry
```

```lean
theorem InteractiveProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ} (h : InteractiveProofErr π L s)
    (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    InteractiveProofErr (π.seqRep Q) L (fun n => s n ^ Q.eval n) := by
  sorry
```

```lean
theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
    (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
  sorry
```

They live in namespace `TCSlib.Cryptography`. The section variables are `{π : Protocol} {R : List Bool → List Bool → Prop}`.

**The construction** (owned, proved readers): `Protocol.seqProver`, `seqVerifier`, `seqRep`, with
`moverIsV_two_mul_add`, `countP_moverIsV`, `countP_not_moverIsV`, `exec_fst_length`, `exec_snd_length`,
`proverMoveIndex_exec`, `verifierMoveIndex_exec` and `Protocol.seqRep_exec_phase` (phase `j` of an honest run is a
run of `π` on coin slice `j`). Read the module docstring's deviations: filler moves, strict-PPT simulators
(G02-#4, D8), bounded prover messages (`ProverBounded`, G3-3), and at least one phase for soundness.

**Proved consumers:** `PerfectZK.seqRep` and `PerfectZKAbort.seqRep` (from `StatZK.seqRep`) in the owned file;
`Composability/ThreeColoring.lean` uses `ZK.seqRep` and `EfficientProverProofErr.seqRep` (Theorem 124.1). Their
axioms become standard with yours.

## Published interfaces

| Interface | Provider |
|---|---|
| the construction readers listed above, `seqRep_exec_phase` | owned file |
| `ZK_iff`, `StatZK`, `perfectZK_iff`, `PerfectZKAbort.statZK`, `StatZK.zk`, `NUPPT.simulate_eq`, `attempt`/`retry` readers | `ZeroKnowledge/Defs.lean` |
| `Strategy`, `efficient_iff`, `ofNUPPT_efficient`, `exec` and its readers, `viewV`, `outV`, `View.encode`, `encodeMsgs`, `ProverBounded`, `withV` and `withV_vCoinsEquiv` | `ZeroKnowledge/Interaction.lean` |
| `InteractiveProof`, `InteractiveProofErr`, `EfficientProverProof(Err)` fields | `ZeroKnowledge/InteractiveProofs.lean` |
| `exists_hybrid_gap`; `StatClose`, `distAdv_le_of_statClose` | `Foundations/Probability.lean`, `Asymptotic/Sampling.lean` |
| `coinBlock`, `FunFamily.blocks`, `distinguisherL` | `Asymptotic/Adversary.lean` |
| `polyTimeComputable_iterate`, `polyTimeComputable_iterateFind`, `polyTimeComputable_iterateEmit`; `BinArith.polyTimeComputable_iterate` | `Complexity/Randomized/Repetition.lean`, `Complexity/ClassP/BinaryArith/Iterate.lean` |
| `NUPPT.exists_comp`, `exists_withAdvice(On)` (the non-uniform hybrid reduction), `ofPolyTimeUniform`; `Negligible.mul_pow`, `const_mul`, `mono` | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `InteractiveProof.seqRep`.** Efficiency of `V_Q` (a uniform machine with coins `Q · coins`, built from the iterate hosts over the phases and `coinBlock` slices), completeness from `seqRep_exec_phase`, and soundness from phase 0 (sketch steps 1–3). Send this checkpoint.
2. **Checkpoint 2 · `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.** Soundness error `s^Q` by conditioning on the prefix and induction on the phases, with the prover strategy that hard-wires the prefix; efficiency and completeness of `P_Q`. Send this checkpoint.
3. **Checkpoint 3 · `StatZK.seqRep`.** The normalized simulator `S_Q` as a uniform strict PPT (one verifier tape, `Q(n)` calls of `S` on fresh coin blocks, the canonical normalization and fallback), the empty-history case, and the triangle inequality over the `Q(|x|)` hybrids, giving exactly `Q(|x|) · δ(|x|)`. Send this checkpoint.
4. **Final · `ZK.seqRep`.** The wrapped verifier `V*` and its efficiency, the simulator of `ZK π R` at the enlarged bound `Lz'`, the non-uniform phase reduction with advice, and the sum of the `Q(n)` gaps, `Q(n) · ε(n)`, negligible.

Check the edge cases: `k = 0` rounds; `Q(n) = 0` for the ZK statements (empty history; the proof-system statements assume `1 ≤ Q(n)`); odd `k` (three-message protocols); `verifierFirst` true and false; a cheating verifier's filler replies; malformed or non-canonical simulator outputs; the auxiliary-input bounds `Lz` and `Lz'`; the honest prover's `[]` fillers.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Composability/SequentialZK.lean` (509 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Composability/SequentialZK/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - Helpers may import modules already in the closure (the ZK layer, `Games/*`, `Complexity/*`).
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
  - **Nearest relatives here:** `PerfectZKAbort.statZK` and its retry machine (`ZeroKnowledge/Defs.lean`), the hybrid arguments of the 3-colouring and graph-isomorphism proofs (`ZeroKnowledge/ThreeColoring/*`, `ZeroKnowledge/GraphIsomorphismZK/*`), `exists_hybrid_gap`, and the repetition hosts of `Randomized/Repetition.lean`.
- **Statements.** Preserve the target statements, every other declaration, the statement prose and the global
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
  - Bootstrap from `order.txt` (237 modules) and the narrow `roots.txt` (76), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (23 declarations in 9 modules). The only change
    must be the removal of `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`.
- **Axioms.**
  - Print the axioms of `ZK.seqRep`, `StatZK.seqRep`, `InteractiveProof.seqRep`, `InteractiveProofErr.seqRep` and `EfficientProverProofErr.seqRep`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files, and of `PerfectZK.seqRep`, `PerfectZKAbort.seqRep` and the `Composability/ThreeColoring` consumers.
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
