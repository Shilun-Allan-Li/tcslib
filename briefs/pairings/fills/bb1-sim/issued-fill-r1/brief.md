# Claude fill · bb1-sim: T2 `bb1_sim_real`, T3 `bb1_sim_random` and the two `Games/Relational` targets

**Issue base** `89a18a8225be1b76166af12a15179da291747783`, the head of #346 (T4 `bb1-machine`, branch
`land/pairings-bb1-machine`, open; fetch it by name or as `refs/pull/346/head`). Ruling Q9: "the fill is stacked on
T4's PR, or based on the tip once T4 merges". #346 is not merged, so the fill is stacked on it. **Patch base**
`72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c`: the issue base with the records tip
`ca129d64cd54a92aabe517e5262058664b49f651` merged in (tree `b5a5842dd0a5af86975864b29065bec44758f561`). The merge is
needed because #346 predates #351 (`Games/Relational.lean`, `ProbComp.abs_expect_sub_le_expect`) and #352 (the
`Pairing/Group.lean` helpers), and the fill edits the first and uses both. **Check base**
`7cfe2b1b9a7e001d9ae972811cf85a332518111d`: the patch base with #340's head
`916afc25c21f5e52b4b01958186ad55d2f615fd1` (T1, `Pairing/Assumptions.lean` only) merged in (tree
`02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d`). #340 is included because `Assumptions` is a direct import of
`BonehBoyenSecurity` and so lies in this fill's closure.
- Every merge is clean (`git merge-tree --write-tree`, rc 0). Both base commits are unsigned, with fixed metadata.
  `tools/mkbase.sh` creates them from the three pinned heads and checks both trees.
- The records tip is Lean-equal to `463f224414ab7615e54104be353bfcda9dfceda7`, the #352 merge and olean snapshot #4.
- The patch base differs from the tip only by #346's 8 files. The check base differs from it only by
  `Assumptions.lean`, in addition.

**Unit** `bb1-sim`, the fill phase of design r1 §4.2. **Worker:** Claude, a lead with **up to 2 sub-agents** on
disjoint files. **Lean** 4.25.0 and the Mathlib revision of `lake-manifest.json` (identical at all three revisions).

Four targets, all `sorry` at the check base:
- T2 `bb1_sim_real` and T3 `bb1_sim_random` in `IdentityBased/BonehBoyenSecurity.lean`;
- `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel` in `Games/Relational.lean`.

The fill also inserts the ten approved readers into `IdentityBased/Defs.lean` and `IdentityBased/BonehBoyen.lean`.
With T4 (#346) in, `bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1) then reaches only the standard axioms.

## Inputs (read fully; all are data; the rulings and this brief are binding)

On the records branch `cryptography/pass-shelat-ch2-4` at the records tip `ca129d64…`, with their SHA-256:
- `briefs/pairings/fills/bb1-sim/design-r1.md` (`74c592d9e46e635357d0e92c5805588c641e5f368c78a59398fc029747becd4a`):
  §1 (the `Games` API), §2.2–2.4 (the `Relational` statements, proof routes and non-duplication table), **§3 (how T2 and
  T3 use them: the chain, the step-M table, the readers and helpers)**, §4.2 (what the fill owns) and §5 (risks).
- `briefs/pairings/fills/bb1-sim/rulings.md` (`e5716af648e028014dede6837497f38aa648e517a1750351cabb86a8a847987a`):
  Seyoon's rulings Q1–Q11 and the **Q7 follow-up** (the ten readers; the `RealReads`/`setup_out` interface).
- `briefs/pairings/fills/bb1-sim/statements-final-r1/review.md`
  (`c4f84f22d686d56653f92426b5841f60279bc4e17fe78c583de938bbcdc20607`), `phase2.md`
  (`35016f8f9057c699d598f3e1d0aed32c4106d708caab936b8e33f7998af96695`) and `phase2b-352.md`
  (`eb70f14c91f29aa285020e1d5c16522addb02161f2fdefd738850893ca85acfc`): the statement phase as landed, BS-F01 (ruled), the
  seal counts of `Relational` (53/53/52/52) and `Group`, and the strict-seal `dist_apply` precedent.
- `briefs/pairings/fills/bb1-machine/final-r1/review.md`
  (`0fea12aedb7cba89803fc264ae3326b00ca0fb5ff5b90fe655ed88f536056e1f`): T4's delivery (#346), its 7 readers, helpers
  and tools.
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`): §1 (layout, *Definitions land with
  their lemmas*, reducible abbreviations, *Duplication*), §2 (statement prose, tags, deviations), §3 (sketches).
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`d328d0d6e844b3429c0c500b5cdaad72f947c5941d56535362176ead25df9666`).
- `PairingCryptographyPlan.md`, the decision log (`9c2ada0cc4c77f9af160a9569bb5ead8b64b27a6f362fe8fac154d3c3ea4fe00`).
- `workflow.md` on `main` (`a954201d421a61994e02e36ff3cf4b16dce53f5d`; fetch `main` by name, read with `git show`),
  §4.1 (the delivery payload) and §6.1 (merged-tree replays) (`917afe65ee154faea862905041d78a83bbb42b6738e0bcff5168a618bc7a8b83`).
- `briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py`
  (`fa81981add5de30d3a98b7e1614e73b17f149723e8be79558ac1a29b6fe67fbc`).
- The BB04 transcription (DW-7): `blueprint/src/references/boneh-boyen-2004-selective-id-ibe.md`
  (`46f8f7b187a46a5f8ff3778c4bded10d7504e89c187653e7e4412d211ef244a2`) and `.raw.md`
  (`7207217873b455fc5e392c190c66e6c1cd6cce52e457bee51728cf35995cd7e3`).

On `exchange/pass-shelat-ch5-8`:
- **The statement job's delivery** `inbox/fills/bb1-sim-statements/`, final commit `a3cb45f6a83c7308db5f2c5fcf95d25fc7f3fef9`
  ("stmt bb1-sim: final"; verify it with its top-level `SHA256SUMS`, `2964053c…`):
  - `probe/READERS-TO-INSERT.md` (`a0061b19c5a4bfcb8392bf6f13474b6f5d4715cde17a8283ab5487bea628199e`), the reader set
    Seyoon approved, with the dropped candidates and the probe's algebraic hypotheses (§4);
  - `probe/PlProbe/BB1SimReaders.lean.txt` (`1045ea4b…`) and **`probe/PlProbe/BB1SimStepM.lean.txt`**
    (`941bd4bd844b864f299995cfd8b3dc03f50630aff887044920da2259b8590655`): the consumer probe. It proves P-1 (the nine
    `sidImpl` cases at the game's types), P-2 (every step-M row) and P-3 (T3's challenge row) natively and under the
    development seals, using `RealReads`, `setup_out`, `realAt` and `RelM`. **It is your starting material for step M.**
  - `evidence/tools/`: the statement job's adapted tools (`drivers/rule10_stmt.sh`, `seal/…`, `clash/`, `insert_blocks.py`,
    `deliver.py`, `pkgcheck.py`, `widths.py`, `sweepsum.py`, `dev/sk15.py`).
- **T4's delivery** `inbox/fills/bb1-machine/` (final `f14ac810da888829d21a1bd94fef4dcd4258b863`): `evidence/tools/`
  (seal, control, scan, build and insertion tools; `insert_readers.py`, `seal/review/mkctl_bb1m_readers.py`) and T4's `REPORT.md`.

This pack (`outbox/fills/bb1-sim/`): `readers/Defs-block.lean.txt` and `readers/BonehBoyen-block.lean.txt` (the ten
readers, byte for byte), `tools/mkbase.sh`, the pin files, and `staging-probe/` (the maintainer's light probe at the
check base, below).

## Binding rulings (Seyoon; `rulings.md` and the decision log)

- **Q1–Q4 (statement phase, landed as #351).** `Games/Relational.lean` holds `ProbComp.expect_simulate_rel`,
  `prob_simulate_rel` (proved) and `expect_sample_rel`, with the inline expectation form of the per-call hypothesis.
  **This fill owns the two `sorry` bodies** (design §4.2: "the proof bodies of `expect_simulate_rel` and
  `expect_sample_rel` … Their headers and statement prose are frozen at the Phase S commit"; the statement job's brief:
  "they are the fill's"; cleanup Stage 1 lists `Relational.lean` as bb1-sim's file).
- **Q5.** No query budget.
- **Q6 (landed in #351).** The averaging bound `ProbComp.abs_expect_sub_le_expect` is public in `Games/Probability.lean`.
  T2's bad-coin step uses it. **No private copy, and no edit to `Probability.lean`.** The private ETT copy is re-pointed
  in cleanup Stage 2, not here.
- **Q7 follow-up (2026-11-17).** "All ten are approved, and they land in the bb1-sim fill PR, inserted verbatim … as
  pure insertions after the anchors it names. … They are theorems proved by `rfl` or in one line; no definition
  changes." **Design point:** the fill uses the probe's `RealReads` interface and the existential `setup_out`.
- **Q8 and DW-11.** The bb1-sim gate (after Gate 44) audits the reader insertions and this fill. #351 and #352 are
  audited separately, in the combined small-items gate DW-11.
- **Q9.** Stacked on T4's PR, or based on the tip once T4 merges (*Rebase*).
- **Q10 (landed as #352) and BS-F01.** `BilinearGroup.pow_val_add`, `pow_val_neg` and `pow_val_bijective_of_ne_one` are
  in `Pairing/Group.lean`. `natCast_inj_of_lt` was **dropped** (LE-grp1): use Mathlib's `CharP.natCast_injOn_Iio` (with
  `ZMod.charP`) for identity injectivity on good coins. `Group.lean` is frozen in this fill.
- **Q11.** [BGZ09] and [Sho04] are ingested and already cited in `Relational.lean`; this fill adds no tag for them.
- **DW-10 Q3 (2026-11-17).** The `FinDist` coercion is **notation**, as `PolyExpr.eval` is: record strict-only failures
  that it causes (as `ProbComp.dist_apply` in `Probability`'s strict seals), but do not count them as failures and do not fix them.

## Feasibility and size (maintainer's assessment)

One job, feasible in one long session. About **1,000–1,700 Lean lines**:
- the ten readers, 131 lines, verbatim;
- the two `Relational` bodies, about 10–30 lines (design §2.3's outlines);
- helper modules under `IdentityBased/BonehBoyenSecurity/`, about 900–1,500 lines:
  - the lazy handlers with their readers and the eager steps (about 250–400);
  - the real side (`RealReads`, `setup_out`, R1, E-h; about 250–400);
  - step M (about 400–650, much of it ported from the probe's 586-line consumer);
  - T3's comparison (about 100–250);
- T2's and T3's assembly in `BonehBoyenSecurity.lean` (about 80–200, with the refreshed sketches).

The plan's estimate was T2 at 400–800 lines and T3 at 150–350. The probe has already settled the reading problem,
which was the main risk.

The long steps are mechanical:
- the bootstrap of the 193-module order;
- the sweep (13 modules plus the helpers; about 2 minutes on the maintainer's tree);
- the canonical seals of 4 changed owners plus the helpers in four variants, base seals of 4 owners, and the controls.

All of it runs one Lean process at a time. Suggested split: the lead takes `Relational`, the lazy handlers, T3 and the
integration; sub-agent A takes step M; sub-agent B takes the real side and the bad-coin bound.

## Bases, branches, rebase and delivery

- **Checkout.** In your own clone, fetch by name `cryptography/pass-shelat-ch2-4`, `land/pairings-bb1-machine` and
  `fill/pairings-pair-bdh`, and check `git rev-parse` of each:
  - the records tip `ca129d64…` or a descendant;
  - #346's head `89a18a82…`;
  - #340's head `916afc25…`.

  Run `bash <pack>/tools/mkbase.sh` in the clone. It prints `PATCH_BASE 72c0498a…` and `CHECK_BASE 7cfe2b1b…` with
  their trees, and stops if a tree differs. Record its output.
- **The branch** `fill/bb1-sim`, from the patch base (`git checkout -b fill/bb1-sim 72c0498a…`). Suggested commits,
  each compiling at the check tree:
  1. `fill bb1-sim: the ten approved readers in Defs and BonehBoyen (Q7 follow-up)`;
  2. `fill bb1-sim: prove expect_simulate_rel and expect_sample_rel`;
  3. `fill bb1-sim: helper modules (lazy handlers, real side, step M)`, split as you like;
  4. `fill bb1-sim: prove bb1_sim_real and bb1_sim_random (T2, T3)`.

  Commit with `git -c commit.gpgsign=false`. Keep every branch local.
- **The check branch** (local only, never delivered): `git checkout -b check/bb1-sim-merged 7cfe2b1b…`, with the fill
  commits applied on top (`git cherry-pick` or `git merge` of the branch head). Every build, sweep, seal, axiom print
  and control runs here.
  - At the end, `git merge-tree --write-tree 916afc25… <fill head>` must equal the check head's tree. Record both.
  - The evidence is then the maintainer's merged-tree replay (`workflow.md` §6.1).
- **Rebase (Q9).** Before each checkpoint and before the final, `git fetch` the records branch. **If #346 has merged**
  (`git merge-base --is-ancestor 89a18a82… origin/cryptography/pass-shelat-ch2-4`), move the fill onto the new tip
  `T'` before you deliver:
  1. List the Lean changes the tip brought besides #346:
     `git diff --name-only 72c0498a… T' -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean`.
  2. `git rebase --onto T' 72c0498a… fill/bb1-sim`.
     - Expect no conflict: `Defs.lean`, `BonehBoyen.lean`, `BonehBoyenSecurity.lean` and `Relational.lean` must be
       unchanged between `72c0498a…` and `T'` (check their SHA-256 against *Scope*).
     - If any of them changed, or a conflict appears, stop with **E-BASE**.
  3. Rebuild the new check base and the oleans:
     - The new check base is `T'` itself if #340 has merged too.
     - Otherwise it is `git merge-tree --write-tree T' 916afc25…`, made a commit with `git commit-tree --no-gpg-sign`
       and `mkbase.sh`'s identity and dates, with parents `T'` and `916afc25…`.
     - Rebuild every module whose source changed, and its downstream. Then re-run every check at the new head.
  4. The patches are then `git format-patch T'..fill/bb1-sim`; decls2 and the insertion check run against `T'`.
     `REPORT.md` records both bases and the reason.

  If only #340 merges, keep the patch base and make the tip the check base in the same way. If the tip moves without
  #346 merging, stay on your bases and say so; the maintainer re-replays at landing.
- **Deliver** every checkpoint and the final only under `inbox/fills/bb1-sim/` on `exchange/pass-shelat-ch5-8`, in the
  standard payload (`workflow.md` §4.1):
  - `REPORT.md` (*Report*);
  - `patches/`: `git format-patch <patch base>..fill/bb1-sim`, with `COMMITS.tsv`. It has one row per commit: hash;
    author name, email and date; committer name, email and date; and its **signing** (`none` or the format). `git am`
    at the patch base must reproduce every hash. Check the reproduction in a scratch clone before you push, and say so.
    The patch base itself comes from `mkbase.sh`: name it in `REPORT.md`, and do not deliver it as a patch;
  - `src/`: every new or changed file at the branch head, under its repository path;
  - `evidence/`, with its manifest `evidence/SHA256SUMS`;
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- **Exchange commits.** Commit on the exchange as `fill bb1-sim: checkpoint N` and `fill bb1-sim: final`, also with
  `git -c commit.gpgsign=false` (BS-F08: an earlier worker's exchange commit was signed by the platform key). Pull
  with rebase before pushing, push only your path, and never force-push. Never touch another path: other fills, gates,
  `outbox/`, `arora-barak-ch3-4/`, `lwe-sis-constructions/`. **Never push a campaign branch.** If a push is refused,
  keep the commit and say so.

## The targets (frozen headers and statement prose; quoted from the check base)

`TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (170 lines). The T2 docstring is lines
73–88; its `**Proof sketch.**` runs from line 78, the header from line 89, and the `sorry` is at line 92. The T3
docstring is lines 94–103; its sketch runs from line 98, the header from line 104, and the `sorry` is at line 106.
The file's `variable (G : BilinearGen) (ℓ : PolyExpr)` applies.

```lean
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
  sorry

theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
  sorry
```

`TCSlib/Cryptography/Games/Relational.lean` (134 lines). `namespace TCSlib.Cryptography.Games` / `namespace ProbComp`
apply, with `variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}`. The `expect_simulate_rel` docstring is lines
55–84 (sketch from line 80), the header from line 85, and the `sorry` is at line 93. The `expect_sample_rel` docstring
is lines 116–123 (sketch from line 122), the header from line 124, and the `sorry` is at line 130.

```lean
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  sorry

theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  sorry
```

`bb1_sidSecure` (lines 108–168: docstring, header and proof) is frozen **whole**. It uses T2, T3 and T4 as they are.
`prob_simulate_rel` (lines 95–114) is frozen whole.

## The ten approved readers (insert verbatim)

The source is this pack's `readers/`:
- `Defs-block.lean.txt`: 86 lines, SHA-256 `d6f8faf16bd8b121fbccba9541225ca9761a2ee90b4eda3bf12dead62eaaa239`;
- `BonehBoyen-block.lean.txt`: 45 lines, SHA-256 `967f2a303484228d42be74c446cf4a8c2a92fb46ad705ec1a60f24b54427f226`.

Each is byte-identical to the statement job's `evidence/subagents/probe/insertion/*-block.lean.txt` at `a3cb45f6` and
`8899115b`, and to `READERS-TO-INSERT.md` §2. Insert each block **byte for byte**, preceded by one blank line, after
its anchor line. The blank line and the docstring after the anchor stay unchanged. Add no import, `open`, attribute
or other line, and leave the module docstrings alone (T4's precedent).

| File (at the patch base) | Anchor | Readers (in order) | After insertion |
|---|---|---|---|
| `IdentityBased/Defs.lean`: 476 lines, SHA-256 `4e220eadd4bf71ea62372bc371a3e2062b9f213acc696dbb66994c1f64069dfd` | after line 430, `  (OracleComp.bind_pure _).symm`, the last line of `oracleImpl_two_onSpec`; before the `sidCodec` docstring; inside `namespace IBEScheme` | `IBEScheme.sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec`, `sidImpl_challenge_fresh_onSpec` | 563 lines, `97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0` |
| `IdentityBased/BonehBoyen.lean`: 714 lines, `da875140806706f26c4cdbb5cf765f522144f3a5a885c5156a58b8c611cd25f4` | after line 412, `  exists_congr fun _ => List.ofFn_inj.symm`, the last line of `bb1Scheme_msgSpace_iff`; before the `bb1_correct` docstring | `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT` | 760 lines, `88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26` |

These are the pins of the Q7 follow-up ruling. The maintainer reproduced both hashes at #346's head, whose two files
equal T4's delivered head `c90273fa` (the probe's base). The staging probe compiled both owners with the blocks
at the check base: rc 0, 0 errors, standard axioms (*Staging probe*). Lines are at most 100 characters (`Defs` block)
and 99 (`BonehBoyen` block).

**Reader discipline (Rule 10).** These ten are the only additions to `Defs.lean` and `BonehBoyen.lean`. If the route
needs another reader, an import, or any other change to a frozen file, that is **E-SCOPE**: ask Seyoon and do not
work around it. The dropped candidates and their failure logs (`READERS-TO-INSERT.md` §3) are not to be revived. That
includes `sidImpl_eq_oracleImpl`, the Q7(B) form, `bb1Scheme_keyGen_mk`/`_enc_mk` and the `congrArg` comparison
without `ofFn_bb1Scheme_encCT`.

## The `RealReads` / `setup_out` interface (ruled design point)

A consumer cannot name the real parameters `⟨d, (g, g^α, g_2, h)⟩ : (bb1Scheme G ℓ).PP κ`: anonymous constructors and
`Σ`-typed instances do not elaborate under the seals (T4's report; the probe's `scratch/explore*`). The fill therefore
reads the real setup's output exactly as the probe does (`BB1SimStepM.lean.txt`, section `Setup`):
- **`RealReads G ℓ κ d g α Y h k`**, a `Prop`-valued structure over `k : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ`.
  Its four fields say what the real handler reads from `k`:
  - `encPP`: the encoded parameters are the padded word `d ‖ g ‖ g^α ‖ Y ‖ h`;
  - `msgSpace`: the message space is the encodings of `G_T`;
  - `keyGen`: `KeyGen`, encoded and then `f`, draws a uniform `r` and gives the word `Y^α F(ID)^r ‖ g^r`;
  - `enc`: `Encrypt`, encoded and then `f`, draws a uniform `s` and gives the word
    `M · e(g^α, Y)^s ‖ g^s ‖ F(ID)^s`, with the message read at the width of `G_T`.
- **`setup_out`**: `∃ o, (∀ F, ((bb1Scheme G ℓ).setup κ).bind F = (sample r).bind … (sample g ∈ G^*) … (sample α) …
  (sample h) … (sample g2) … F (o r g α h g2)) ∧ ∀ r g α h g2, RealReads … (G.desc κ r) g.1 α g2 h (o r g α h g2)`.
  It is proved from `bb1Scheme_setup_eq`, `BB1.setup_eq`, `ofFn_bb1Scheme_encPP`, `bb1Scheme_msgSpace_iff`,
  `bb1Scheme_keyGen_bind`, `BB1.keyGen_eq`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_enc_bind`, `BB1.encrypt_eq` and
  `ofFn_bb1Scheme_encCT`, with `o` found by unification.
- The real-side handlers (`bb1RealAt`, `bb1RealLazy`; the probe's `realAt`) take the map `o` (or `o h`) as a
  **parameter**, as design §3.3 asks. They are instantiated from `setup_out` at the use site in T2, and they never
  construct a `PP` or `MSK` value.

Land `RealReads` and `setup_out` in a helper module, with the probe's statements. You may change the namespace, binder
names, docstrings and proofs. You may change a statement only to a form that is equal or more general, and you must
disclose it. `RealReads` is a definition: give it what policy §1 and lint check 8 require. Its fields are its
projections; if check 8 lists it, add an `_iff` reader and disclose it.

## Route (design r1 §3, refined by the probe; you may improve it, the targets are fixed)

**`expect_simulate_rel`** (design §2.3, L1): induction on `c` (`OracleComp`'s recursor), generalizing `s`, `t` and
`hst`. Use `simulate_pure`/`simulate_query` (`Games/Simulate.lean:93`, `:97`) and `expect_pure`/`expect_bind`
(`Games/Probability.lean:117`, `:128`), the shape of `expect_simulate_congr` (`Games/Hopping.lean:384`).
**`expect_sample_rel`** (L3): `expect_bind`, `expect_pure` and `expect_sample_equiv` (`Probability.lean:304`), then a
pointwise comparison. Both owners read foreign definitions only through these published lemmas. Refresh a
`**Proof sketch.**` only if your proof differs from it.

**T2** (design §3.1). With `S := bb1Scheme G ℓ` and `c := A.toComp (S.sidCodec κ) κ q ρ`, condition on the generator
coins `r`. The chain is:
1. Move the setup's `h` inside (`expect_sample_comm`, `expect_expect_sample`).
2. **R1**: `expect_simulate_rel` from `S.sidImpl b κ (o …)` to `bb1RealAt` (the stored-`h` handler), with
   `R_h s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
3. **E-h**: `Games.expect_simulate_eager` (`Games/Hopping.lean:494`; not `ChallengeSim.expect_simulate_eager`), which
   moves `h` to the first `Init`.
4. `g₂ ↦ g^{b'}` along `Z_p ≃ G`: `Equiv.ofBijective` of `BilinearGroup.pow_val_bijective_of_ne_one`, with
   `nonempty_ne_one`.
5. **Step M**: `expect_simulate_rel` with design §3.1's `R` (the probe's `RelM`). The per-call hypothesis comes from
   P-1/P-2: deterministic rows give equal `pure` answers; sampling rows go through `expect_sample_rel`, along `e ID`,
   `Equiv.addRight (b'/(ID − ID*))` and `Equiv.refl`. This step needs good coins.
6. **E-c**: `Games.expect_simulate_eager` for the challenge coin `c`, with one lazy handler `bb1SimLazy` generic in
   `zt : U → G × G_T`.
7. Reorder, merge the coins (`Bridge.expect_sample_pair`) and drop the unused `T` (`expect_const`).

**Bad coins.** `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]` pointwise, then `ProbComp.abs_expect_sub_le_expect`
(`Probability.lean:409`), `Bridge.prob_sample_eq_uprob` (`Games/Bridges/Experiments.lean:65`) and
`BilinearGen.inst_eq` (`Pairing/Group.lean:309`).

**The probe's algebraic hypotheses** (`READERS-TO-INSERT.md` §4) become lemmas of the fill:
- `e` and `he`, from `pow_val_bijective_of_ne_one` and `Equiv.mulLeft`;
- `hinj`, from **`CharP.natCast_injOn_Iio`** (BS-F01), `bitsToNat_lt` and `bitsToNat_injective`
  (`Asymptotic/Sampling.lean:412`, `:417`) and `2^ℓ ≤ p`;
- `hkey`, BB04's key identity: `pow_val_add`, `pow_val_neg`, `pow_val_mul`, and field arithmetic in `ZMod p`;
- `hF`, from `pow_val_add`/`pow_val_neg`;
- `hT`, from `bilinear_pow` and `pow_val_mul_GT`.

**T3** (design §3.2). **E-T**: `Games.expect_simulate_eager` moves `T` to the first valid challenge (`bb1SimLazy` with
`zt := fun T => (Z, T)`). Then `ProbComp.expect_simulate_congr` compares `bb1SimLazy false` and `bb1SimLazy true`. At
the first valid challenge it uses `expect_sample_rel` with `R := Eq` along `T ↦ decodeT(M₁)⁻¹ · decodeT(M₀) · T`,
which is the probe's P-3: T4's readers suffice. Conclude with `advantage_eq`.

**Sketch refresh (docstring only).** T2's and T3's `**Proof sketch.**` paragraphs describe the delivered proof.
- T2's names `ProbComp.expect_simulate_rel` and both eager steps. It drops the frozen sketch's
  `Games.expect_simulate_congr`, which has the wrong namespace and the wrong lemma (design §5, risk 3).
- T3's names `expect_simulate_eager` and `expect_simulate_congr`.
- The statement prose before each `**Proof sketch.**` stays byte-identical.

**Published interfaces (reuse first; search before writing any lemma).**
- `Games`: `simulate_*`, `expect_*`, `prob_eq_expect`, `expect_simulate_congr`, `Games.expect_simulate_eager`,
  `expect_sample_equiv`, `expect_sample_comm`, `expect_expect_sample`, `ProbComp.expect_const`, `abs_expect_sub_le`,
  `abs_expect_sub_le_expect`, `advantage_eq`, `accept_eq`, `Bridge.expect_sample_pair`, `Bridge.prob_sample_eq_uprob`,
  `castImpl_eq`, `bitSpec_dom`/`_rng`.
- IBE: the ten readers; T4's seven (`oracleImpl_{zero,one,two}_onSpec`, `ofFn_bb1Scheme_encPP`/`_encSK`,
  `bb1Scheme_msgSpace_iff`, `ofFn_bb1SimCt`); `sidImpl_*`, `sidSpec_eq`, `inLens_*`, `outLens_*`, `sidGame_eq`,
  `sidSecure_iff`; `bb1SimImpl_eq`, `bb1SimGame_eq`, `bb1SimInit_*`, `bb1SimKeyQ_*`, `bb1SimChal_*`, `bb1SimParams_eq`,
  `bb1SimKey_eq`, `bb1SimCt_eq`, `BB1.F_eq`, `BB1.setup_eq`, `BB1.keyGen_eq`, `BB1.encrypt_eq` and `BB1.idToZ_eq`.
- `Pairing`: `pow_val_mul(_GT)`, `pow_val_add`, `pow_val_neg`, `pow_val_bijective(_of_ne_one)`, `bilinear_pow`,
  `nonempty_ne_one`, `BilinearGen.inst_eq`.
- T4's helpers (`BB1Machine.*`) where they apply. They are frozen, so import them and do not copy them.

## Scope

| File | Permitted change |
|---|---|
| `Games/Relational.lean` (134 lines, SHA-256 `804a4c875318f9173da80d3e3275f309258c50ed72e0aaf9928b65849fa05ae8`) | the bodies of `expect_simulate_rel` (line 93) and `expect_sample_rel` (line 130); each one's `**Proof sketch.**` paragraph only if the proof differs from it. No new declaration, import, `open` or attribute |
| `IdentityBased/Defs.lean` (476, `4e220ead…`) | the six reader insertions, verbatim, and nothing else |
| `IdentityBased/BonehBoyen.lean` (714, `da875140…`) | the four reader insertions, verbatim, and nothing else |
| `IdentityBased/BonehBoyenSecurity.lean` (170, `30f906581b0ec205fb3566bfb89405864d616b4982d06ac8ac3fd96919630571`) | T2's and T3's bodies and `**Proof sketch.**` paragraphs; one `import` line per new helper module, after line 8; a `## Contents` section in the module docstring that lists the helpers (T4's precedent in `BonehBoyenMachine.lean`). Nothing else |
| new helper modules under `IdentityBased/BonehBoyenSecurity/` | the lazy handlers, real side, step M and T3 glue, each with a module docstring (title, `## Main definitions`, `## Main results`, `## References`) |

**Helper modules.**
- A helper imports only modules of `order.txt` (for example `Games.Relational`, `Games.Hopping`,
  `IdentityBased.BonehBoyen`, `BonehBoyenMachine`) and earlier helpers. It is imported only by
  `BonehBoyenSecurity.lean` or a later helper.
- Insert each new module into your order before `BonehBoyenSecurity` and after its imports.
- Each helper stays at most 1000 lines (policy target 150–600).
- Every public definition lands with its readers (policy §1; lint check 8). No `@[simp]` and no global attribute.
- Use a clash-free namespace, for example `…IdentityBased.BB1Sim`.

**Frozen:** everything else. Among those files:
- `Games/Probability.lean` (Q6 is done by #351; the rulings allow no further change here); `Games/Hopping.lean`,
  `Games/Simulate.lean`, the `Games.lean` facade and the rest of `Games/`;
- `Pairing/*`, including `Group.lean` (Q10 is done by #352) and `Assumptions.lean` (#340's);
- T4's files `BonehBoyenMachine.lean` and `BonehBoyenMachine/*` (#346);
- the facades `IdentityBased.lean`, `AdvancedEncryption.lean` and `TCSlib.lean`;
- `EncryptThenTag/Forgery.lean` (its DL-40 re-point belongs to cleanup Stage 2);
- **cleanup Stage 1's homes**, which a running job owns:
  - `Complexity/Randomized/PPT`, `Complexity/Randomized/Build/IterateFindHost`;
  - `InformationTheory/FinDist`, `InformationTheory/Entropy`, `InformationTheory/Samples`;
  - `Foundations/BitLists`, `Asymptotic/Sampling`, `Asymptotic/Adversary`;
  - `Games/Bridges/Experiments`, `Games/Machines`, `Games/Efficiency/Strings`, the `Games` facade;
  - `Pseudorandom/Functions/Asymptotic/Defs`, `Encryption/PrivateKey/EnsembleSecurity`,
    `Encryption/PublicKey/Trapdoor`, `Authentication/Encoding`;
  - `ZeroKnowledge/EncodingMachines`, `ZeroKnowledge/Interaction`, the `ZeroKnowledge` facade;
  - its new `Games/Tapes` and `ZeroKnowledge/InteractionWords`;
- the GSW files (`AdvancedEncryption/Homomorphic/**`), every other campaign's files (`Complexity/**`, Yao, the
  Arora–Barak and Ladner material), `blueprint/` and `audits/`.

**Scope requests.** If the route needs any other change to a frozen file (a reader, an import, a promotion, a
`Probability` lemma), stop that line of work. Ask Seyoon in your session, giving the file, the diff and the reason, and
go ahead only on his approval. Record the request and his answer verbatim under `evidence/scope-request/` and in
`REPORT.md`. Seyoon prefers routes with no frozen-file edit. A lemma that belongs in a shared file goes into a helper
module, with a promotion request.

**What you may not do.**
- Change a target's header or statement prose, its name, its module or its position; change `bb1_sidSecure` or
  `prob_simulate_rel`.
- Add an admission (`sorry`, `admit`, `native_decide`, `axiom`), or weaken or alter any statement or definition.
- Copy a private lemma silently, or leave any duplicate undisclosed (a second copy of the averaging bound, of
  `Games.expect_simulate_eager` (the DL-33 precedent), or of a Mathlib `ZMod`/`orderOf` fact).
- Push anything but your delivery path.

## Sources and citations

- T2's, T3's and `bb1_sidSecure`'s tags ([BB04, proof of Theorem 4.1, …], [BB04, Theorem 4.1]) are frozen.
- A new helper is glue (policy §2: say so in one line) or carries a tag whose passage is in the DW-7 BB04
  transcription: `[BB04, proof of Theorem 4.1]` for the simulator's computations, `[BB04, §4.2]`. Quote and locate
  only what that transcription contains.
- The `Relational` docstrings already carry the review-§4 strings for [BGZ09] and [Sho04]; add no tag there.
- **Never fabricate** a quotation, location or anchor.
- Add no reference file, do not edit `blueprint/` and do not run `scripts/sources.py`.
- Identifiers use the Greek `μ` (U+03BC), never the micro sign.

## Proof discipline

- **Rule 10 (readers only; policy §1).** Read other files' definitions only through published lemmas and readers,
  including generated matchers and projections. Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show`
  step, but are never passed to `simp`, `rw` or `unfold`. Each owner reads its own definitions directly: that is why
  only `Defs.lean` and `BonehBoyen.lean` prove the ten readers, by `rfl` or in one line. The helper modules are foreign
  to each other and to `BonehBoyenSecurity.lean`.
  - **Type-level Rule 10.** Reach the cast equations (`(S.sidSpec κ).dom i = …`, `.rng i = …`) only from `sidSpec_eq`,
    `bitSpec_dom`/`_rng`, `inLens_*` and `outLens_*`, as the probe does (`dom_zero` … `rng_two`, `zeroBits_eq_cast`).
  - **Notation, never sealed:** reducible abbreviations (`QueryImpl`, `ProbComp`, `IBEScheme.sidSpec`,
    `IBEScheme.SidState`, `BB1SimState`, and new `abbrev`s such as the probe's `RealState`); `PolyExpr.eval`; projection
    coercions; and the `FinDist` coercion (DW-10 Q3).
- **Sizes and widths.** Every line at most 100 characters (Python `len`), and every file at most 1000 lines. Check both
  with a `python3 -I` script before each push and keep its output in `evidence/`.
- **Docstrings.** Every new public declaration has a docstring that states it in words and gives its formula, with its
  arguments in the Lean order, and a tag or a glue note. Every proof of 15 lines or more has a `**Proof sketch.**`,
  with step comments in long proofs (policy §3). Sketches name the steps that the formal proof makes visible as `have`s
  or lemmas.
- **Duplication (binding).** Search first: TCSlib, core and Mathlib, by name, by `exact?`/`apply?` on the statement in
  a scratch probe, and by grep for the conclusion's shape. Undisclosed copies of public lemmas are majors. Disclose every
  overlap in `REPORT.md` § *Overlap and reuse*:
  - carry design §2.4's table, confirming or correcting each row;
  - add the probe's lemmas as you port them;
  - give each helper's nearest relatives, `path:line`, among them `PRFGame.expect_lazyImpl`,
    `ETTGame.expect_ettImpl_lazy`, `ETTGame.expect_simulate_abs(_inv)`, `simulate_eq_of_abs`, the T4 helpers and the
    Mathlib `ZMod`/`orderOf` API;
  - list the searches you ran.

## Multi-agent work (up to 2 sub-agents)

- **The lead owns the job:** the branch `fill/bb1-sim`, every commit, the check branch, the integration, the final
  sweep and checks, the delivery and `REPORT.md`. Only the lead commits on `fill/bb1-sim`, runs `lake`, fetches the
  cache and pushes.
- **Suggested split** (disjoint files; record any other split):
  - lead: the reader insertions, `Relational.lean`, the lazy handlers and eager steps, T3, and `BonehBoyenSecurity.lean`;
  - sub-agent A: step M (the coupling module, ported from the probe), with its group-algebra lemmas;
  - sub-agent B: the real side (`RealReads`, `setup_out`, `bb1RealAt`, `bb1RealLazy`, R1, E-h) and the bad-coin
    bound; or, if the real side is small, the evidence tooling (insertion and frozen checks with controls, control
    rows, clash and shadow scans, reuse searches).
- Each sub-agent works in its own git worktree with its own TCSlib olean tree and `.lake/packages` linked to the lead's,
  and hands its files to the lead as patches. **One Lean process at a time on the host**, for all agents, through one
  lock (`flock <clone>/.lean.lock …`), released between modules. A file is reassigned only through the lead, after its
  owner has stopped. Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md` records who wrote what.

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; check one module at a time
with `scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log, and keep every raw log. Tools: adapt the statement job's `evidence/tools/` and T4's (*Inputs*). Copy what you use
into `evidence/tools/`, change host paths, and record each change in the tool's header.

1. **Bootstrap and sweep** (at the check tree).
   - Bootstrap `order.txt` (193 modules) at the check base: rc 0, 0 errors, and exactly the `sorry` warnings of
     `base-sorries.txt` (22 declarations in 10 modules).
   - **Sweep at the check head:** rebuild every module whose source differs from its olean's source, then its
     downstream, in order. Then check the new helper modules (at their positions) and every module of `closures.txt`'s
     `DOWN` (13, root excluded), each with rc 0 and 0 errors in both forms. Bind every checked source to
     `git show HEAD` (`evidence/build/summary.txt`: module, rc, errors in both forms, `sorry` warnings, source hash).
   - The root `TCSlib` is not built. Neither `audits/*/Checks` is downstream of a changed module. The maintainer
     replays the root at landing.
   - Record `git merge-tree --write-tree 916afc25… <fill head>` and the check head's tree; they must be equal.
2. **Admissions.** At the check head: exactly `base-sorries.txt` minus the four targets, which is **18 declarations in
   8 modules**. There may be no `sorry` in any new or changed file. Checkpoint 1 may keep `sorry` in helper proofs and
   targets; list every one.
3. **Statements.**
   - `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <patch base> <new and changed files>` on the
     branch head gives **ADDED** exactly the ten readers plus the helper declarations you declared at checkpoint 1 (any
     later addition listed), with **0 CHANGED and 0 REMOVED**.
   - A `StmtDump` probe prints every new constant, the four targets and `bb1_sidSecure` with full names and types.
   - **Frozen-header check** (a `python3 -I` script): the four targets' headers (keyword through `:= by`) and their
     statement prose are byte-identical to the patch base, and so are `bb1_sidSecure` and `prob_simulate_rel` whole.
     The rest of `Relational.lean` and `BonehBoyenSecurity.lean` is unchanged, except for the bodies, the sketches and
     the permitted imports and `## Contents` section.
     - Each of these controls must FAIL: an edit that spills from a sketch into the statement prose; a one-character
       header change; an unpermitted import; an edit to `bb1_sidSecure`; a `## Contents` change outside the section;
       an edit to `prob_simulate_rel`.
     - The unchanged file must PASS.
4. **Reader insertion check** (a `python3 -I` script under `evidence/headers/`):
   - removing the two blocks restores `4e220ead…` and `da875140…` byte for byte;
   - each block equals `readers/*-block.lean.txt` byte for byte at its anchor;
   - the final hashes are `97ecb6e0…` and `88454d6f…`.

   Each control must give the stated result:
   - one character changed inside a reader: FAIL, exactly one difference;
   - one reader deleted: FAIL, exactly one removal;
   - one extra line elsewhere in either file: FAIL;
   - a reader moved: FAIL;
   - a reader's docstring edited: FAIL.
5. **Axioms.**
   - `#print axioms` of every new constant, the four targets, `prob_simulate_rel`, `bb1_sidSecure`,
     `exists_bb1_distinguisher` and the ten readers: `propext`, `Classical.choice` and `Quot.sound` only, or a subset.
   - A census of every stored constant of the changed owners and helpers: 0 non-standard.
   - A **dependency trace**: a probe that walks the constant closure and lists every constant whose own value uses
     `sorryAx`. It must be empty for `bb1_sidSecure` (with T4 in) and for the four targets. The staging probe's
     `#sorry_trace` (`staging-probe/Stmt.lean.txt`) is a ready form.
6. **Rule 10.**
   - **Canonical seals** A and B, strict and coe (the coe-variant seal A canonical), with `-DmaxErrors=0`, over the
     full TCSlib import closure, of **every changed owner** at the check head: `Relational`, `Defs`, `BonehBoyen`,
     `BonehBoyenSecurity` and each new helper. Run **base seals** of the four existing owners at the check base.
     - Report each seal's request count and every failing declaration. Attribute every difference from the base by its
       raw log.
     - The readers and the new code may add **no failing declaration**. Strict-only failures caused by the `FinDist`
       coercion are notation (DW-10 Q3): list them and do not count them.
     - The `Relational` precedent at #351 is 53/53/52/52 with 0 errors in all four variants.
   - **Paired controls.** Adapt T4's `seal/review/mkctl_bb1m_readers.py` (its seven reader rows) and the statement
     job's `seal/review/mkctl_bb1s.py`, with new rows:
     - for each of the ten readers, a negative (the unfolding the reader replaces, stated in a consumer's context) and
       a positive (the reader);
     - for each new helper definition foreign to a later module, a negative and a positive through its reader.

     Each sealed negative fails exactly once, each positive passes, and all pass unsealed (pretest first). Strict and
     coe must both be `ALL_OK True`. `Relational` and `BonehBoyenSecurity` define nothing: no pair, and the report says
     so.
   - **The explicit-unfold scan** over the changed and new files: 0 foreign.
7. **Frozen-file check.** `git diff --stat <patch base>` lists only the files of *Scope*.
8. **Lint.**
   - `python3 -I scripts/style_lint.py <new and changed files>`: no finding that is not already at the base on the
     same declaration.
   - `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at the check base and the check head.
     The maintainer's baseline at the check base is **92 FAIL / 104 WARN over 524 files**. Diff the line sets: no new
     FAIL or WARN line (check 8: no new definition without a lemma), except one you disclose and justify.
   - Run `dev/sk15.py` on the new code.
9. **Sizes and widths** of every new and changed file at the head. `BonehBoyen.lean` reaches 760 lines with the
   readers, approved and under the cap.
10. **Docstrings and sketches** as in *Proof discipline*. The module docstrings of the helpers are complete, and
    `BonehBoyenSecurity.lean`'s `## Contents` lists every helper.
11. **Name-clash and shadow scans.**
    - (a) No new full name, public or private, already exists in `TCSlib/` or `audits/` at the check base.
    - (b) List every new short name that exists elsewhere (namespaces resolved).
    - (c) Show that no unqualified use in a module of `DOWN` changes its resolution.
12. **Reuse and overlap** (*Proof discipline*; `REPORT.md` § *Overlap and reuse*).

## Checkpoints

- **Checkpoint 1**, as soon as it is ready:
  - the ten readers inserted, with the insertion check (4);
  - every helper module's statements elaborating at the check tree (proofs may be `sorry` at the checkpoint only);
  - the decls2 list and `StmtDump` of the helpers (3);
  - the clash scan (11);
  - an **outline**: T2's and T3's chain, each step mapped to the helper lemma that proves it, and each `expect_simulate_rel`
    and `expect_simulate_eager` instance with its handlers and relation.

  It lets the maintainer check the helper API early.
- **The final** has everything, with no `sorry` in any new or changed file.

## Report

`REPORT.md` gives:
- the issue base, the patch base and the check base (with `mkbase.sh`'s output), the records tip used, any rebase
  (*Rebase*), the check head's tree with the `merge-tree` equality, the branch head and every commit;
- who wrote what;
- the changed files with their lines at base and head;
- § *The new declarations*: a table of full name, home, kind and readers;
- § *Statement changes*: none, or each with the reason;
- the checks: builds and admissions (1–2), statements and headers (3), the reader insertion check (4), axioms and
  the trace (5), Rule 10 seals, base seals, controls and the scan (6), the frozen check (7), lint, sizes and
  docstrings (8–10), and the clash and shadow scans (11);
- § *Overlap and reuse* (12);
- § *Scope requests*: none, or each with Seyoon's answer;
- questions for Seyoon, if any, numbered `BS-W1`, … with the recommended option first;
- the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered:
- seal and control sources, manifests and request records;
- the frozen-header and insertion checks with their outputs and controls;
- the decls2 output and the `StmtDump`;
- the axiom prints and the trace;
- the clash and shadow scans and the reuse searches;
- every raw log and `results.jsonl`;
- the sub-agents' logs;
- the tools used.

If the evidence is too large for one commit, deliver it in several commits or numbered ZIP parts, each with an entry
list. Leave nothing out for size. Check before each push that the delivered paths are exactly the manifests' (top
level and `evidence/`), with no leading `./`.

## Staging probe (maintainer, at the check base; `staging-probe/`)

The probe ran on a hard-linked copy of olean snapshot #4. It rebuilt the 15 modules downstream of the check base's
changes, with the ten readers inserted (root excluded), and then ran `T23Probe/Stmt`.
- **16/16 rc 0**, with 0 `error:`/`error(`.
- `BonehBoyenSecurity` has exactly the two `sorry` warnings (T2, T3).
- T1, T4 and the ten readers use the standard axioms.
- `bb1_sidSecure` reaches exactly `bb1_sim_real` and `bb1_sim_random`, and `prob_simulate_rel` reaches exactly
  `expect_simulate_rel`.
- The snapshot rehashed 0/0/0 before and after.

This is evidence that the targets and readers elaborate at the check base. It does not replace your bootstrap and
checks.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-BASE.** `mkbase.sh` fails, or a rebase meets a conflict or a changed owner file (*Rebase*). Stop, keep your
  work, and report the trees and the diff.
- **E-SCOPE (frozen files).** Any of these is an E-SCOPE:
  - a reader does not elaborate verbatim at its anchor, or fails its owner's seal;
  - the route needs another reader, an import outside the order, or any other frozen-file change.

  Stop that line of work and ask Seyoon in your session (*Scope*).
- **E-ROUTE (proof).** The integrated proof fails in a way that no change inside the owned files fixes, or a target
  looks false as stated. Stop and state the exact obligation, with the failing goal or a counterexample.
- **How to report.** Push a checkpoint `fill bb1-sim: checkpoint N (blocked: <code>)` whose `REPORT.md` opens with the
  blocker, the exact obligation or request, and the logs. Keep everything that already passes. Never work around a
  blocker by weakening a statement, adding a hypothesis, editing a frozen file without approval, or using a private
  stand-in.

**Ready to dispatch**
