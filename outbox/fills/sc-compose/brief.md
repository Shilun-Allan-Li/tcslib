# Claude fill · the semi-honest composition theorem (`composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`, [Gol04, Theorem 7.3.3])

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `sc-compose`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorems `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose` of [Gol04, §7.3.1, Theorem 7.3.3] (used unstated by [PS10, Theorem 163.7]) in
`TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean`. The statements passed the prong B statement phase and Gate 06B (closed PASS),
and are frozen. Each docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated (plan §2.11–2.12: well posed, no false statement found). The phase lemmas exist. The missing pieces are the interleaved-slot map lemma, the efficiency extraction, a simulator-repeating NUPPT, the bad-event switch and the run-`i` coin equivalence. No dependency on an admitted target: Yao and OT meet only in `YaoReal.lean`.

**Estimated size:** 3,000–5,300 lines (plan: the efficiency pair 1,000–1,800, `hbcSecure_compose` 2,000–3,500), in 6–10 helper modules. `ComposeSecurity.lean` is at 382 lines.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/sc-compose` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-compose/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-compose/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill sc-compose: checkpoint N` and `fill sc-compose: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot`) start from the same base.
  Each edits only its own owned file and helper directory.

## Targets (frozen; quoted from the issue base)

```lean
theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeP ρ).Efficient := by
  sorry
```

```lean
theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeV ρ).Efficient := by
  sorry
```

```lean
theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
    (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
    (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
  sorry
```

They live in namespace `TCSlib.Cryptography.SecureComputation.HybridProtocol`. In the section `Efficiency` the variables are `{G : Functionality} (H : HybridProtocol G) (ρ : Protocol)`;
the two efficiency theorems take `{F}`, `hH : H.PolyTime F` and `hρ : G.PolyTime ρ`. `hbcSecure_compose` takes
`hM : ∀ n, 0 < H.main.rounds.eval n`, `H.HBCSecure F` and `HBCSecure ρ G`. Read the module docstring's
deviations (calls first, `hM` with its counterexample, uniform bounds) and the theorem's five-step sketch.

**Consumers:** `polyTime_compose` (proved from the two efficiency theorems and `compose_msg_bound`) and
`YaoReal.yaoProtocol_hbcSecure`. The proof needs neither Yao nor OT (plan §1).

**Analysis.** `briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`, §2.11 and §2.12. Both
statements were checked and found well posed.

## Published interfaces

| Interface | Provider |
|---|---|
| `exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`, `compose_msg_bound`, `polyTime_compose` | owned file |
| `compose_P`, `compose_V`, `composeP`, `composeV` and the `slotMsgs`/`runTape` readers | `SecureComputation/Compose.lean` (frozen) |
| `slotFromA_eq`, `slotFromB_eq`, `compose_transcript`, `compose_exec_runs`, `compose_exec_main`, `compose_viewP`, `compose_outV` | `SecureComputation/ComposePhases.lean` (frozen) |
| `HybridProtocol.PolyTime` (the `callA`/`callB` clauses), `HybridProtocol.HBCSecure`, `polyTime_iff`, `hbcSecure_iff`, `realA_eq`, `realB_eq`, `answersA_eq`, `answersB_eq`, `coins_eq` | `SecureComputation/Hybrid.lean` (frozen) |
| `HBCSecure`, `PolyTime`, `polyTime_iff`, `hbcSecure_iff`, `realA_eq` … `idealB_eq` | `SecureComputation/Defs.lean` (frozen) |
| `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`; `StatClose`, `distAdv_le_of_statClose` | `Foundations/Probability.lean`, `Asymptotic/Sampling.lean` |
| `polyTimeComputable_blockMap` (fixed block size), `polyTimeComputable_iterate(Find)`, `polyTimeComputable_stateFind`; `countW` | `Complexity/Randomized/Repetition.lean`, `ZeroKnowledge/EncodingMachines.lean`, `Complexity/ClassP/BinaryArith/Words.lean` |
| `Strategy.Efficient` readers (`efficient_iff`, `ofNUPPT_efficient`); `NUPPT.exists_comp`, `exists_seq`, `exists_withAdvice`, `ofPolyTimeUniform`, `Computes.polyTimeComputable`; `padFin_ofFn` | `ZeroKnowledge/Interaction.lean`, `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean` |
| `Negligible.add`, `mul_pow`, `const_mul`, `mono` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · `composeP_efficient` and `composeV_efficient` (plan §2.11).** The interleaved-slot map lemma; the extraction of a polynomial-time next-message function from `Strategy.Efficient` (`Computes.polyTimeComputable` covers uniform NUPPTs); `composeP.next` as a polynomial-time function on the raw layout: the indices from `|hist|`, the call inputs from `H.PolyTime`, the run tapes cut from `r`, one `ρ` activation or `L(n)` of them for the answers, and one `main` activation. Share the helpers between Alice and Bob. Plan estimate: 1,000–1,800 lines. Send this checkpoint.
2. **Checkpoint 2 · `hbcSecure_compose`, sketch steps 1–2.** The simulator `S_A` (and `S_B`) as a non-uniform PPT that runs `S_A^H` and then `L(n)` runs of `S_A^ρ` on blocks and assembles the view; the output clause with the worst-case inputs as advice; the statistical switch "agree off a bad event" of probability at most `2L(n)ε₁(n)`. Send this checkpoint.
3. **Final · `hbcSecure_compose`, sketch steps 3–5.** The hybrid over the runs (advice: worst `i`, inputs, `main` tapes and ideal answers; the coin-space equivalence for run `i`), the post-processing `Φ` to the hybrid model (`H.HBCSecure F`), and the total `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`.

Check the edge cases: `L(n) = 0` calls; `ρ.rounds(n) = 0`; `hM` (the statement is false without it, see the docstring); the fillers; the tape cut lengths (exact on real views, so `Φ` is the identity there); `padFin` readback; Bob's side, symmetric to Alice's.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

**Partial delivery.** If you cannot finish every target, your final payload may prove a subset. Each proved
declaration must use only the standard axioms. The others keep their `sorry` and their statements,
and `REPORT.md` says which are proved and what remains for each of the others.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean` (382 lines at the issue base):
  - replace the targets' proof bodies and edit their sketches to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/SecureComputation/ComposeSecurity/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `ZeroKnowledge/GraphIsomorphism/EfficiencyRep` and `ZeroKnowledge/EncodingMachines`. Neither depends on the owned file (checked at the issue base). `SecureComputation/Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `SpecialEncryption.lean`, `GarblingSpecial.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*` files and `Pseudorandom/*` are named frozen for this unit (with every other file).
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
  - **Nearest relatives here:** the history machines of the graph-isomorphism and 3-colouring efficiency proofs (`ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`, `ZeroKnowledge/ThreeColoring/Machines.lean`), `polyTimeComputable_blockMap`, the hybrid lemmas of `Foundations/Probability.lean`, and the ZK simulators that run a machine on coin blocks (`ZeroKnowledge/Defs.lean`, `retry`). **Expected new API:** the plan finds no lemma for mapping a polynomial-time function over the `L(n)` interleaved run slots of a history (`blockMap` needs fixed-size blocks). Write it once, generic, as a public helper shared by both efficiency theorems; search for a near relative first, disclose it, and propose it for promotion.
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
  - Bootstrap from `order.txt` (152 modules) and the narrow `roots.txt` (74), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (31 declarations in 14 modules). The only change
    must be the removal of `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`.
- **Axioms.**
  - Print the axioms of `composeP_efficient`, `composeV_efficient` and `hbcSecure_compose`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
