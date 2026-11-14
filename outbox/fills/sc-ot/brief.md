# Claude fill · oblivious transfer from trapdoor permutations (`otProtocol_polyTime` and `otProtocol_simulators`, Protocol 160.4 and Proposition 161.5)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `sc-ot`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `otProtocol_polyTime` and `otProtocol_simulators` of [PS10, Protocol 160.4 and Proposition 161.5] in
`TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean`. The statements passed the prong B statement phase (ruling G3-8, applied in `587843c7`) and Gate 06B (closed PASS),
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated (plan §2.1–2.2: both statements well posed, G3-8 closed). The infrastructure is mostly present. The missing pieces are the five-move view equations, the coin-space equivalences, and an adapted `exists_pkPredictor`, which is an overlap to disclose. No dependency on an admitted target: the OT file is independent of every other secure-computation admission.

**Estimated size:** 2,000–3,400 lines (plan: `otProtocol_polyTime` 500–900, `otProtocol_simulators` 1,500–2,500), in 3–6 helper modules. `ObliviousTransfer.lean` is at 671 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/sc-ot` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-ot/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-ot/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill sc-ot: checkpoint N` and `fill sc-ot: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) := by
  sorry
```

```lean
theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA (otProtocol T H) n x y)
            (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB (otProtocol T H) n x y)
            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n := by
  sorry
```

They live in namespace `TCSlib.Cryptography.SecureComputation`. The section variable is `(T : TrapdoorCollection)`. In the section `Security` the variables are
`{h : ∀ i, T.D i → Bool}`, `(H : List Bool → List Bool)`, `(hH : PolyTimeComputable H)` and
`(henc : ∀ i x, H ⟨i, encD i x⟩ = [h i x])`. `otProtocol_simulators` also takes `hT : T.OneWay` and
`hEHC : EnhancedHardCore T h`.

**The protocol** (five messages; owned, read through its lemmas): `otSender`, `otReceiver`, `otProtocol` and their
field equations, `otMask_eq`, `otKnown_eq`, `otRaw_eq`, the simulator functions and `otSimA`/`otSimB`
(`otSimA_coins`, `otSimA_uniform`, `runAt_otSimA`, and the same for `B`), `SamplerCanonical`, and the proved
correctness `otProtocol_outV`, `otProtocol_outP`. `otProtocol_hbcSecure` (proved from the two targets) is the
consumer, and through it `YaoReal.yaoProtocol_hbcSecure`.

**G3-8 is closed.** The enhanced hard-core predicate was ruled (A) on 2026-11-05 and applied in prong B
(`587843c76f95f10056c9ddc9174da9dc8fba8b54`). `EnhancedHardCore` is already a hypothesis of the frozen
`otProtocol_simulators`, `otProtocol_hbcSecure` and `yaoProtocol_hbcSecure`, and Gate 06B closed PASS with it.
Read the module docstring's deviations: five messages, random elements, and the enhanced predicate. (No collection
in the library is yet proved to have such a predicate; that limits use of the result, not its proof.)

**Analysis.** The maintainer's analysis is `briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`,
§2.1 and §2.2. It checked both statements and found them well posed.

## Published interfaces

| Interface | Provider |
|---|---|
| the protocol and simulator readers listed above; `enhancedHardCore_iff`; `polyTimeComputable_coinSeg` and the other `polyTimeComputable_*` of the file | owned file |
| `polyTime_iff`, `hbcSecure_iff`, `realA_eq`, `realB_eq`, `idealA_eq`, `idealB_eq`, the `otFunctionality_*` readers | `SecureComputation/Defs.lean` (frozen) |
| `Collection.sample_spec`, `inv_spec`, `f_perm`, `apply_of_decD`, `eval_poly`, `SampleClose`; `runLenPoly` | `Asymptotic/Collections.lean`, `Asymptotic/CollectionsHelpers.lean` |
| `StatClose`, `distAdv_le_of_statClose`; `uprob_prod`, `uprob_comp_equiv`, `uprob_exists_le` | `Asymptotic/Sampling.lean`, `Foundations/Probability.lean` |
| `exists_pkPredictor` (the signed-predictor identity of Algorithm 104.3, stated for `f : α ≃ α` inputs) | `Encryption/PublicKey/Trapdoor.lean:337` |
| `NUPPT.ofPolyTimeUniform`, `exists_comp`, `exists_withAdvice`, `exists_split`, `polyTimeComputable_layout`, `polyTimeComputable_output`, `Computes.polyTimeComputable` | `Complexity/Randomized/{Closure,PPT}.lean` |
| `Strategy`, `efficient_iff`, `encodeMsgs`; history readers `pairSndD_encodeMsgs`; `polyTimeComputable_stateFind`; `countW` | `ZeroKnowledge/Interaction.lean`, `…/GraphIsomorphism/EfficiencyRep.lean`, `…/EncodingMachines.lean`, `Complexity/ClassP/BinaryArith/Words.lean` |
| `Negligible.add`, `const_mul`, `mono` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `otProtocol_polyTime` (plan §2.1).** Alice's and Bob's next-message functions branch only on the history length. Write each as a polynomial-time function on the raw layout (Gen, the sampler and the inverter are uniform machines, `eval` is `eval_poly`, `H` is `hH`), make it a uniform machine with `NUPPT.ofPolyTimeUniform`, and prove the message bound: the index (at most Gen's output, `runLenPoly`), two sampler outputs or evaluations, two one-bit masks, and empty fillers. Reuse the encoded-history readers; the plan estimates 500–900 lines. Send this checkpoint.
2. **Checkpoint 2 · Alice's side of `otProtocol_simulators` (sketch steps 1–2).** The view equations of the five-move execution (the pattern of `otProtocol_outV`), the coin-space equivalence between Alice's real tape and `S_A`'s, and the bound `2δ(n)` from `SampleClose` per generated index (`perm` is a bijection, `y_{1−b}` is canonical by `SamplerCanonical`) through `distAdv_le_of_statClose`. Send this checkpoint.
3. **Final · Bob's side (sketch steps 3–4).** The adapted signed predictor for `⟨i, s'⟩` challenges (disclosed, see above), the predictor machine by `NUPPT.exists_comp` with the worst of the eight triples `(b, a₀, a₁)` as advice, the bound `2 ε_EHC(n)` from `hEHC`, and one negligible `ε` covering both sides.

Check the edge cases: `b = 0` and `b = 1`; all eight `(b, a₀, a₁)`; the five-message layout and its two empty fillers; non-canonical strings (`apply_of_decD`); the inverter's fixed all-`true` tape; small `n` where `SampleClose` is only eventual; the distinguisher's advice.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean` (671 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Encryption/PublicKey/Trapdoor`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep` and `ZeroKnowledge/EncodingMachines`. None depends on the owned file (checked at the issue base); the order includes their upstream closure. `SecureComputation/Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `SpecialEncryption.lean`, `GarblingSpecial.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*` files and `Pseudorandom/*` are named frozen for this unit (with every other file).
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
- **No ℓ-output PRF.** This unit does not need the ℓ₂-output PRF machinery. Seyoon ruled that the PRF layer is generalized in a separate job, `prf-long`; do not build or copy any of it. If you find you need it, stop and escalate with the exact obligation.
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
  - **Nearest relatives here:** `exists_pkPredictor` (`Encryption/PublicKey/Trapdoor.lean:337`), the graph-isomorphism efficiency proofs (`giProver_efficient`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`), the history readers of `ZeroKnowledge/ThreeColoring/Machines.lean` (`iterate_pairSndD_encodeMsgs`), and the Algorithm 104.3 machines of `Encryption/PublicKey/Trapdoor.lean`. **Expected overlap:** the plan finds that Bob's side needs an adapted copy of `exists_pkPredictor` for `⟨i, coins⟩` challenges. State it in its general form in a helper, and disclose it as an overlap with `exists_pkPredictor` (and propose it for promotion), since `PublicKey/Trapdoor.lean` is frozen.
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
  - Bootstrap from `order.txt` (159 modules) and the narrow `roots.txt` (74), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (31 declarations in 14 modules). The only change
    must be the removal of `otProtocol_polyTime` and `otProtocol_simulators`.
- **Axioms.**
  - Print the axioms of `otProtocol_polyTime` and `otProtocol_simulators`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
