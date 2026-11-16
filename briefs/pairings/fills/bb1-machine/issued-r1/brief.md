# Claude fill · BB1 reduction machine, finish of T4 (`bb1-machine`)

**Issue base** `7c0a55e0239c14786612d0cd4462e64238543ca1`, the tip of branch `fill/pairings-bb1-machine` (pushed): the
in-house fill's three signed checkpoint commits on `9e7a96481785d6cac4dea3b2e990c49ac278b060`, the head of draft PR
#331 (`stmt/pairings`; Gate 40 CLOSED, round 2 CLEAR). **Unit** `bb1-machine`: target T4 `exists_bb1_distinguisher`
(step 3 of [BB04, Theorem 4.1]; `PairingCryptographyPlan.md`). **Worker** Claude, a lead with **up to 1 sub-agent**
(Seyoon's ruling, 2026-11-16: external Claude jobs for parallelism). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

The in-house fill built the whole Gate 40 route for T4 in four helper modules and stopped at a scope request: one glue
step needs seven readers in two frozen files. Seyoon approved them. This job inserts them verbatim, moves the ready glue
into a helper module, proves T4 and re-runs the full evidence. **T4 is the only target.**

## The ruling (Seyoon, 2026-11-16; decision log of `PairingCryptographyPlan.md`)

> (1) **T4 scope request approved, minimal form**: the 7 readers (`oracleImpl_{zero,one,two}_onSpec` in
> `IdentityBased/Defs.lean`; `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff`, `ofFn_bb1SimCt`
> in `BonehBoyen.lean`) land **in the T4 PR** as pure insertions with `rfl`/one-line proofs and formula docstrings, as
> with sc-yao's SY-3 readers. #331 is unchanged; Gate 44 checks they are insertions only.

- The **13-reader variant** (`scope-request/BB1Readers.lean.txt`, which adds six `sidSpec_dom_*`/`sidSpec_rng_*` type
  equations) is **not approved**. Derive the type equations of the casts from the published `IBEScheme.sidSpec_eq`,
  `bitSpec_dom`, `bitSpec_rng`, `inLens_*` and `outLens_*`, as `MachineProbeMin` does.
- No other frozen-file change is approved.

## Feasibility and size (maintainer's assessment)

Feasible: the proof exists. `scope-request/MachineProbeMin.lean.txt` states T4 verbatim and proves it from the seven
readers, published readers and the checkpoint's helper modules. The in-house fill checked it natively and under its
development seals A and B (2289 and 2290 definitions sealed): rc 0, 0 errors, and `#print axioms
exists_bb1_distinguisher` = `[propext, Classical.choice, Quot.sound]`. What remains is integration and evidence: the
readers in their owners instead of a probe module, the glue in a helper module, T4's body and sketch, and the canonical
checks on every changed owner.

**Estimated size.** Exactly +43 lines in `Defs.lean` (433 → 476) and +37 in `BonehBoyen.lean` (677 → 714), the
approved text; about 280 lines of glue (`MachineProbeMin.lean.txt` lines 15–294); about 30 lines of T4 body
(lines 296–323); the rewritten sketch. Four lines of the probe are longer than 100 characters (34, 40, 216, 246) and
must be rewrapped.

## Checkout and delivery

- Fetch `fill/pairings-bb1-machine` (or the commit). Start a local branch `fill/bb1-machine` at the exact issue base,
  check `git rev-parse HEAD`, and record the base in `REPORT.md`. Keep the proof branch local.
- **Deliver a series on top of the base.** Do not rewrite, squash, reorder or re-sign the three checkpoint commits
  `c158b66e49bf69cf77e0edc8a523df14332a0616`, `8dc69cdae7a8a6541d4ebe3297272847c7b318b4` and
  `7c0a55e0239c14786612d0cd4462e64238543ca1`. They carry SSH signatures; verifying them needs an allowed-signers file,
  which is not required here.
- Read `policy.md`, the attached environment addendum, `README.md` and the checkpoint's `REPORT.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/bb1-machine/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base (`7c0a55e0…..fill/bb1-machine`; the checkpoint
    commits are the base and are not in it);
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at the base
    reproduces every hash. Commit with `git -c commit.gpgsign=false`; if a commit is signed anyway, say so in its row
    and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in `REPORT.md`;
  - `src/`: the changed and new files under their repository paths;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/bb1-machine/` except itself. The
    delivered paths must **equal** the manifest's paths exactly: nothing missing, nothing extra, and no leading
    `./`. Check this before each push.
- Commit on the exchange as `fill bb1-machine: checkpoint N` and `fill bb1-machine: final`.
- Pull with rebase before pushing. Push only your delivery path, never force-push, and never touch another path
  (other fills, gates, the `arora-barak-ch3-4/` and `lwe-sis-constructions/` folders). Never push a campaign branch,
  `fill/bb1-machine` included. If a push is refused, keep the commit and say so. Campaign changes land by a maintainer
  PR for Seyoon's approval.

## The checkpoint (what is already done)

Read the in-house `REPORT.md` first. In short:
- **Changes against `9e7a9648`** (5 files, +2240 lines). `BonehBoyenMachine.lean` gained the four helper imports and a
  `## Contents` section; T4's header, prose, `**Proof sketch.**` and `sorry` are byte-identical to #331. New helper
  modules under `IdentityBased/BonehBoyenMachine/`, imported only by `BonehBoyenMachine.lean`: `Draws.lean` (451
  lines), `Words.lean` (632), `Handler.lean` (899) and `Reduction.lean` (243). They hold 166 public declarations, each
  with a formula docstring.
- **Route** (Gate 40, G40-03 and its T4 section): exponents drawn from coin blocks of `n = κ + wG(κ) + 1` bits
  (`draw`, `statClose_draw`); the handler on encodings (`Ops`, `ArithmeticFP`, `xgcdStr` inverse with `0 ↦ 0`);
  `simulate_handler`; T1's machine (`expect_handlerMachine`); ideal exponents (`expect_castImpl_freshImpl`); the error
  `q·(1/2)^n ≤ (q + 1)·2^{−κ}` (`abs_expect_runAccept_sub_le`). Everything is built except the per-call identity
  `bb1SimImpl` = `castImpl (freshImpl drawStep)` (`expect_bb1SimImpl` in the probe), which needs the readers.
- **Checks at the checkpoint:** native build of the four helpers, the owned file, `BonehBoyenSecurity`, the facades and
  the root, rc 0, 0 errors both forms; admissions unchanged; seals strict and coe A/B 20/20 on the five changed owners,
  0 errors; controls strict and coe `ALL_OK True`; explicit-unfold scan 0 foreign; lint line set unchanged.

**Where to read it.**
- Records branch `cryptography/pass-shelat-ch2-4` at `99eae2c1550ee0b0485f115bca76b254dae25064` (or any later tip),
  folder `briefs/pairings/fills/bb1-machine/inhouse-r1/`:
  - `REPORT.md` (SHA-256 `3ee4835db10a876c540cad7ccd05564170cdda4ed3aa7296335e483de59a4e5e`);
  - `fill-bb1-machine-evidence.zip` (`eeaa5c787187c977adb91617c577bb6d98987714138f282453590659b50a2580`, 457 entries,
    about 227 MB unpacked). Its seal, control, scan, statement and build records are the base record of the helper
    modules. Unpack it into its own empty directory outside your clone, and treat it as data;
  - `scope-request/` (`BB1ReadersMin.lean.txt`, `MachineProbeMin.lean.txt`, and the unapproved `BB1Readers.lean.txt`).
- On the exchange, this pack's `checkpoint/` folder holds copies, manifested by `checkpoint/SHA256SUMS`. Each copy's
  hash equals its entry in the evidence zip's or `inhouse-r1/`'s manifest. It holds:
  - `REPORT.md`;
  - `scope-request/BB1ReadersMin.lean.txt` and `scope-request/MachineProbeMin.lean.txt`;
  - `tools/`, the zip's `tools-used/` verbatim;
  - `tools/drivers/`: `rule10_bb1m.sh`, `run-checks.sh`, `run-dev-build.sh` and `run-scope-min.sh`;
  - `tools/probes/Axioms.lean.txt`.

**The tools are the maintainer's; adapt them.**
- They hard-code the maintainer's host: the scratch path `$SP`, the worktree `wt-fill-bb1-machine`, the olean tree
  `dl-oleans`, `/home/user/tcslib/.lake/packages` (in `seal/runner_full.py`) and the base `9e7a9648` (in the drivers).
  Copy what you use into `evidence/tools/`, change the paths, record each change in the tool's header, and deliver
  the modified copies.
- The main tools:
  - builds: `review/runner.py`, through `scripts/lean_check_tree.sh`;
  - probes: `seal/runner_full.py` (`lean -DmaxErrors=0`, no `-o`);
  - seals and controls: `seal/rule10_b.sh` with `seal/review/{mkcollect,mkseals_ab,mkseals_coe,mkctl_bb1m,ctlcheck2,sealsum}.py`
    and `seal/review/archived-gate10-tools/`;
  - the unfold scan: `seal/scan1_g40.py`, `seal/scan2.py`;
  - statements: `seal/decls2.py`, `seal/review/touched.py`;
  - the frozen check: `frozen_check_bb1m.py`, `frozen_controls_bb1m.py`;
  - sketches: `dev/sk15.py`;
  - per-module tables: `permod.py`.
- Not needed on a private clone: the shared-tree backup and restore tools `backup_cum.py`, `backup_g40m.py`,
  `restore_derand.sh`, `restoreplan.py`, `snapshot.py`, `stateplan.py`, `seal/backup.py`, `seal/restore.py` and
  `seal/snapshot.py`.
- `dev/devseal.py` and `dev/dct.sh` are development aids. Their output is not evidence.

## Target and approved readers

### T4 (frozen; quoted from the issue base)

`TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (100 lines at the base): docstring lines
71–93, its `**Proof sketch.**` paragraph from line 78, the declaration at line 94, `sorry` at line 98.

```lean
theorem exists_bb1_distinguisher (H : Candidates.ArithmeticFP) (O : G.Ops) (A : NUPPT)
    (q : PolyExpr) :
    ∃ D : Bool → NUPPT, ∃ σ : ℕ → ℝ, Negligible σ ∧ ∀ (b real : Bool) (κ : ℕ),
      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by
  sorry
```

### The seven readers (approved; insert verbatim)

The source is `scope-request/BB1ReadersMin.lean.txt` (SHA-256
`8644e7228ee7acd4d00c10adb004dca4fe0f94429a18a426e361406d5783420d`), lines 27–68 and 74–109. Insert them **byte for
byte**: the same docstrings, binders, statements, proofs and line breaks. Line numbers below are at the issue base.

1. **`IdentityBased/Defs.lean`** (433 lines). The readers go inside `namespace IBEScheme`, whose
   `variable (S : IBEScheme)` they use. Line 387 is the last line of `oracleImpl_two`:
   `    S.oracleImpl κ init key chal 2 x s = chal x s := rfl`. After it, insert one blank line and approved lines 27–68:
   the three readers in the order `zero`, `one`, `two`, with one blank line between them. The blank line and the
   docstring of `sidCodec` follow unchanged.
   - Result: 476 lines, SHA-256 `4e220eadd4bf71ea62372bc371a3e2062b9f213acc696dbb66994c1f64069dfd`.
2. **`IdentityBased/BonehBoyen.lean`** (677 lines):
   1. Line 387 is the second line of `attribute [simps …] bb1Scheme`:
      `  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme`. After it, insert one blank line and approved
      lines 74–97 (`ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff`). They come before the
      docstring of `bb1_correct`.
   2. Line 551 is the last line of `bb1SimCt_eq`. After it, insert one blank line and approved lines 99–109
      (`ofFn_bb1SimCt`). It comes before `open Classical in`.
      - This block is inside `section Simulator`. Its explicit binders `(G : BilinearGen) (ℓ : PolyExpr)` shadow the
        section variables of the same names and give the same signature (`G ℓ κ d Z T α₁ m`). Keep them verbatim.
   - Result: 714 lines, SHA-256 `da875140806706f26c4cdbb5cf765f522144f3a5a885c5156a58b8c611cd25f4`.
3. **Nothing else changes in these two files.** Add no import, `open`, attribute or other declaration, and leave the
   module docstrings and their `## Main results` alone. With the seven blocks and their leading blank lines removed,
   each file must equal the issue base byte for byte. The base SHA-256s are
   `9af4b7738f041d2b7f166df6b6ef7c35cf1fcf41c891e04317b50bdff06cf4a8` (`Defs.lean`) and
   `22caae4f61102c6c31b242fbc37f486939442960049b5e6e4c54790fca96ecd6` (`BonehBoyen.lean`).
4. **If a reader fails**, either to elaborate verbatim at its position or under its owner's canonical seal, stop that
   line of work and escalate (E-SCOPE). Do not reword, re-prove or move it.

The text to insert into `Defs.lean` (approved lines 27–68):

```lean
/-- **Oracle `0` of `oracleImpl` on the game's query type**: the handler `init` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_zero_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 0) (s : σ) :
    S.oracleImpl κ init key chal 0 x s =
      (init (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of `oracleImpl` on the game's query type**: the handler `key` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_one_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 1) (s : σ) :
    S.oracleImpl κ init key chal 1 x s =
      (key (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of `oracleImpl` on the game's query type**: the handler `chal` on the query read
as two messages, its answer read back on the game's answer type. -/
theorem oracleImpl_two_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 2) (s : σ) :
    S.oracleImpl κ init key chal 2 x s =
      (chal (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
        from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm
```

The text to insert into `BonehBoyen.lean` after the `simps` attribute (approved lines 74–97):

```lean
/-- **The parameter encoding as a word**: `⟦encPP ⟨d, pp⟩⟧` is the padded word
`d ‖ g ‖ g_1 ‖ g_2 ‖ h` (`ppLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encPP (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encPP κ ⟨d, pp⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ppLen.eval κ) (d ++ List.ofFn ((G.group κ d).encG pp.g) ++
        List.ofFn ((G.group κ d).encG pp.g1) ++ List.ofFn ((G.group κ d).encG pp.g2) ++
        List.ofFn ((G.group κ d).encG pp.h))) := rfl

/-- **The key encoding as a word**: `⟦encSK ⟨d, k⟩⟧` is the padded word `d_0 ‖ d_1`
(`skLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encSK (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (k : BB1.Key (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encSK κ ⟨d, k⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).skLen.eval κ) (List.ofFn ((G.group κ d).encG k.d0) ++
        List.ofFn ((G.group κ d).encG k.d1))) := rfl

/-- **The message space as words**: a `msgLen(κ)`-bit message is in the message space of
`⟨d, pp⟩` iff its word is the word of the encoding of an element of `G_T`. -/
theorem bb1Scheme_msgSpace_iff (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    (bb1Scheme G ℓ).MsgSpace κ ⟨d, pp⟩ m ↔
      ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m :=
  exists_congr fun _ => List.ofFn_inj.symm
```

The text to insert into `BonehBoyen.lean` after `bb1SimCt_eq` (approved lines 99–109):

```lean
/-- **The simulated challenge as a word**: `⟦bb1SimCt … m⟧` is the padded word
`decodeT(m) · T ‖ Z ‖ Z^{α_1.val}` (`ctLen(κ)` bits), the message read at the width of `G_T`. -/
theorem ofFn_bb1SimCt (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (Z : (G.group κ d).G) (T : (G.group κ d).GT) (α₁ : ZMod (G.group κ d).order)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    List.ofFn (bb1SimCt G ℓ κ d Z T α₁ m) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
        (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)) * T)) ++
          List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val)))) := by
  rw [padFin_ofFn]
  rfl
```

## Remaining work, route and checkpoints

1. **Readers.** Insert the seven readers as above. Check `Defs.lean`, `BonehBoyen.lean` and every module of the order
   downstream of them. Commit them alone, as `bb1-machine: approved readers (scope request, Seyoon 2026-11-16)`.
2. **Glue into a helper module.**
   - Move the glue from `MachineProbeMin.lean.txt` into a helper module under `IdentityBased/BonehBoyenMachine/`. The
     glue is section `Glue` (`expect_bb1SimImpl`), `abs_inner_le`, and the private lemmas they use: `cast_eq_padFin`,
     `ofFn_padFin_ofFn`, `ofFn_decAnswer_some`, `sidSpec_rng_one'` and `sidSpec_rng_two'`.
   - Where it goes:
     - either append it to `Reduction.lean` (243 lines; about 520 after);
     - or put it in a new module that imports `Reduction` and is imported only by `BonehBoyenMachine.lean`.
   - No new import is needed. The probe's extra `Asymptotic.EnsemblesLemmas` is already upstream of `Reduction` and
     of `BonehBoyenMachine.lean`.
   - **Visibility.** T4 calls `abs_inner_le` from another module, so that lemma becomes public, and
     `expect_bb1SimImpl` may.
     - Each public lemma: namespace `BB1Machine`, a descriptive name that clashes with nothing, a formula docstring, a
       `**Proof sketch.**` if its proof is 15 lines or more, and an entry under the helper's `## Main results`.
     - Keep the one-line helpers private where you can. Check each against the published lemmas (*Overlap and
       reuse*).
   - Rewrap the probe's four lines over 100 characters.
   - **Rule 10.** The glue reads `bb1SimImpl` through `bb1SimImpl_eq`, `castImpl` through `castImpl_eq`, the drawn
     handler through the `drawStep_*` case lemmas, and the lengths through `qLen_*`, `aLen_*`, `inLens_*` and
     `outLens_*`, as in the probe. In `Reduction.lean`, the definitions of `Draws`, `Words` and `Handler` are foreign:
     read them through their readers only.
3. **T4.** Replace the `sorry` at line 98 with the probe's proof (lines 296–323), calling the moved lemma by its new
   name. T4's header does not change.
4. **T4's sketch.**
   - Rewrite only the `**Proof sketch.**` paragraph (from `**Proof sketch.**` on line 78 to the end of the docstring),
     so that it describes the delivered proof:
     - the machines `D_b` of T1 from `Games.exists_toCompOn_of_toComp` and `Games.exists_handlerMachine`;
     - `σ(κ) = (q(κ) + 1)·2^{−κ}`;
     - the four `ProbComp.abs_expect_sub_le` steps down to one tuple;
     - the per-call identity of `bb1SimImpl` with fresh drawn exponents (the readers);
     - the draws' bound `q·(1/2)^n ≤ σ(κ)`.
   - Keep G40-03's parameters right (`n = κ + wG(κ) + 1`, `sampleBelowL p (Nat.size p) n n`). The sketch may name the
     helpers.
   - These stay byte-identical: everything before `**Proof sketch.**` in T4's docstring (lines 71–77: the title, the
     tag and the statement prose), the header (lines 94–97), and the rest of the file. The one exception is a new
     helper module's import line and `## Contents` bullet.
5. **Evidence.** Run every check under *Checks and report*.

**Checkpoints.** Each delivers whole proved declarations; at least one mid-way checkpoint is required.
1. **Checkpoint 1: readers and T4.** Steps 1–4, with the native build of the changed modules and everything downstream
   of them, the axioms of T4 and of the readers, and the reader-insertion check. Send it.
2. **Final.** The full evidence below.

**If the proof breaks.** If the probe's proof fails on the integrated tree (a renamed lemma, elaboration
differences), fix it inside the owned files. If T4 cannot be proved without a further frozen-file change, stop that
line of work and escalate. **Do not weaken any statement**, add a hypothesis or change a definition. A partial final is
allowed only with T4 named unproved and its exact remaining obligation stated.

## Base and parallel work

- **#331 is unchanged** and merges first. The T4 PR is the whole series `9e7a9648..` your head: the three checkpoint
  commits and yours, stacked on #331. The maintainer rebases it onto the records tip at landing. If #331 or anything
  else changes or merges during the fill, **stay on the issue base**.
- **T1 is proved in #340, but not on this base.** #340 is `fill/pairings-pair-bdh` at
  `916afc25c21f5e52b4b01958186ad55d2f615fd1`. `bdhAssumption_of_dbdhAssumption` stays `sorry` here. Nothing in T4's
  route uses it. Do not cherry-pick or import #340.
- **`bb1-sim` (T2, T3) is out of scope.**
  - `BonehBoyenSecurity.lean` is frozen.
  - The design of `bb1-sim` is a separate, gated job: a shared relational simulation lemma in `Games` (ruling of
    2026-11-16).
  - At the final, `bb1_sidSecure` still reaches `sorryAx`, through T2 and T3 only.
- **Gate 44** (Codex) audits the T4 PR. It checks that the readers are insertions only.

## Published interfaces (reuse first)

Read other files' definitions **only** through readers (Rule 10). The list comes from the probe. It is a start, not a
limit: search before writing any lemma.

| Interface | Provider |
|---|---|
| the seven readers (this job), `IBEScheme.oracleImpl_zero`/`_one`/`_two`, `sidSpec_eq`, `inLens_*`, `outLens_*`, `sidCodec_eq` | `IdentityBased/Defs.lean` |
| `bb1SimImpl_eq`, `bb1SimGame_eq`, `bb1SimCt_eq`, `BB1.F_eq`, `bb1_encPP_inj` …, the `bb1Scheme_*` `simps` lemmas | `IdentityBased/BonehBoyen.lean` |
| `BB1Machine.qLen_*`, `aLen_*`, `blockLen_eval`, `drawStep_zero`, `drawStep_one_{none,target,key}`, `drawStep_two_{none,repeat,fresh,invalid}` | `BonehBoyenMachine/Draws.lean` |
| `BB1Machine.runAccept`, `expect_handlerMachine`, `expect_castImpl_freshImpl`, `abs_expect_runAccept_sub_le` | `BonehBoyenMachine/Reduction.lean` |
| `BilinearGen.dbdhGame_eq`, `inst_eq`, `length_desc` | `Pairing/Assumptions.lean`, `Pairing/Group.lean` |
| `Games.castImpl_eq`, `bitSpec_dom`, `bitSpec_rng`, `exists_toCompOn_of_toComp`, `exists_handlerMachine`, `advantage_eq`, `accept_eq` | `Games/` (search for the exact provider) |
| `ETTGame.freshImpl_apply`, `FixedLengthScheme.decAnswer_some`, `ofFn_splitHalf_fst`/`_snd` | `Encryption/PrivateKey/…` (search) |
| `ProbComp.expect_simulate_congr`, `expect_sample_equiv`, `abs_expect_sub_le`, `prob_eq_expect`, `expect_bind`, `expect_pure`, `expect_const` | `Games/Hopping.lean` and the probability layer (search) |
| `padFin_ofFn`, `ofFn_padFin_of_length` | the `padFin` layer (search) |
| `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg` | `Asymptotic/EnsemblesLemmas.lean`, `Foundations/Negligible.lean` |

## Scope

**Owned files and what may change in them** (paths under `TCSlib/Cryptography/AdvancedEncryption/IdentityBased/`):

| File | Permitted changes |
|---|---|
| `BonehBoyenMachine.lean` | T4's body; T4's `**Proof sketch.**` paragraph; for a new helper module only, one `import` line of it and one `## Contents` bullet |
| `BonehBoyenMachine/{Draws,Words,Handler,Reduction}.lean` (the checkpoint's) | new declarations before their first use, and their `## Main results` entries. Existing declarations stay unchanged (`decls2` against the base: 0 CHANGED, 0 REMOVED). Any unavoidable change is listed and justified in `REPORT.md` |
| a new helper module under `BonehBoyenMachine/` (optional) | the glue, with a module docstring: title, Main results, References |
| `Defs.lean`, `BonehBoyen.lean` | the seven reader insertions, verbatim, and nothing else |

**Helper modules.**
- A helper module imports only modules of `order.txt` and earlier helpers, never a module downstream of itself. It is
  imported only by `BonehBoyenMachine.lean` or a later helper.
- It stays at most 1000 lines (policy target 150–600). `Handler.lean` (899) and `Words.lean` (632) are already over
  the target: do not grow them.
- Insert a new module into your order before its consumer.

**Frozen files.** Everything else, among them:
- `BonehBoyenSecurity.lean` (T2, T3, `bb1_sidSecure`);
- `Pairing/*`, `Games/*`, `Candidates/*`;
- the facades `IdentityBased.lean`, `AdvancedEncryption.lean` and `TCSlib.lean`.

**Scope requests.** If the route needs any other change to a frozen file (a reader, an import, a promotion), stop that
line of work.
- Ask Seyoon in your session, giving the exact file, the diff and the reason. Go ahead only on his approval.
- Record the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*.
- Seyoon prefers a route with no frozen-file edit.
- A lemma that belongs in an existing file goes in your helper module, with a promotion request.

**The frozen-statement rule (binding; checked).** In `BonehBoyenMachine.lean`, these stay byte-identical:
- T4's header: attributes and modifiers, keyword, name, binders and type, up to the `:= by`;
- its statement prose;
- the module title and the rest of the module docstring (except the permitted `## Contents` bullet);
- every other line except T4's body and sketch.

Delete nothing. Keep every `variable`, `section`, `open` and `set_option`.

**What you may not do.**
- Change a frozen file beyond the seven insertions.
- Change T4's header or statement prose, its name, its module or its position.
- Add an admission (`sorry`, `admit`, `native_decide`, `axiom`), or weaken or alter any statement or definition.
- Leave a duplicate of a public or private lemma undisclosed.
- Import a module outside `order.txt` without a scope request.
- Add `@[simp]` or any global attribute.
- Push anything but your delivery path.

## Sources and citations

- You may rely on:
  - the frozen docstrings' tags ([BB04, §4.2], the algorithm `B` in the proof of Theorem 4.1; [PS10, Definition 26.8]);
  - the BB04 transcription (DW-7) on the records branch, added after the base: it is not in your checkout's tree;
    read it at the records commit above:
    - `blueprint/src/references/boneh-boyen-2004-selective-id-ibe.md` (SHA-256
      `46f8f7b187a46a5f8ff3778c4bded10d7504e89c187653e7e4412d211ef244a2`);
    - `blueprint/src/references/boneh-boyen-2004-selective-id-ibe.raw.md`
      (`7207217873b455fc5e392c190c66e6c1cd6cce52e457bee51728cf35995cd7e3`);
  - the Gate 40 findings, `briefs/pairings/gates/40-pairings-statements/findings/`.
- **Never fabricate a source excerpt, quotation or location.** A new declaration either is glue (no tag) or carries a
  tag whose passage is in those materials.
- Do not add reference files, edit `blueprint/` or run `scripts/sources.py`.
- BB04 writes the Decision BDH advantage with an absolute value (§3.1; LE-doc-abs). Keep the sketch consistent with
  that.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), every file at most 1000 lines. Check both
  with a short `python3 -I` script before each push and put its output in `evidence/`.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Undisclosed copies of public lemmas are majors.** The majors that held Gates 23, 24, 29, 32 and 34 were
    undisclosed duplicates (for example G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`; G32-01, `getD`/`headD`-of-`List.ofFn` copies).
  - **Nearest relatives of the glue:**
    - `ofFn_padFin_of_length` and `padFin_ofFn`, for `ofFn_padFin_ofFn` and `cast_eq_padFin`;
    - `FixedLengthScheme.decAnswer_some`, for `ofFn_decAnswer_some`;
    - `IBEScheme.sidSpec_eq`, `bitSpec_rng` and `outLens_*`, for `sidSpec_rng_one'`/`_two'`;
    - `ProbComp.expect_simulate_congr`, for the per-call step;
    - the checkpoint's private `expect_sample_eq_uprob` and `ite_ofFn_one`;
    - `bb1SimInit_*`, `bb1SimKeyQ_*` and `bb1SimChal_*`, against `drawStep`'s case lemmas.
  - **The readers' relatives,** to disclose: `oracleImpl_zero`/`_one`/`_two`, stated at the handlers' types (the new
    readers are their forms at the game's query types); the `simps` lemmas `bb1Scheme_encPP`, `bb1Scheme_encSK` and
    `bb1Scheme_MsgSpace`; `bb1SimCt_eq`.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**.
    - Carry forward the checkpoint's items 1–7.
    - For every new declaration, and every inline `have` re-proof, that restates, specializes or re-proves existing
      material (public or private, TCSlib or Mathlib), give its nearest relative (`path:line`), the relation, and why
      it is not reused.
    - List the searches you ran.
- **Docstrings and sketches.**
  - Every new public declaration has a docstring that states its formula, with its arguments in the Lean order, and a
    source tag only as *Sources and citations* allows.
  - Every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments (policy
    §3). T4's sketch describes the delivered proof.
  - New definitions are not expected. A new public `def` lands with its `_eq` reader (lint check 8).
  - Add no `@[simp]` and no global attribute.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections. Core and
    Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`, `rw` or
    `unfold`; use their equation lemmas.
  - Each owner may read **its own** definitions directly. `Defs.lean` and `BonehBoyen.lean` prove the seven readers
    this way, which is why only they may.
  - The helper modules are foreign to each other and to `BonehBoyenMachine.lean`.
  - **Notation, never sealed:**
    - reducible abbreviations (here `IBEScheme.sidSpec`, `IBEScheme.SidState`, `BB1SimState`; also `QueryImpl`-style
      abbrevs);
    - `PolyExpr.eval`;
    - projection coercions (Seyoon, 2026-11-14).
  - **Type-level Rule 10.** Never reach the type equations of the casts (`(S.sidSpec κ).dom i = …`, `.rng i = …`) by
    unfolding `inLens` or `outLens`. Derive them from `sidSpec_eq`, `bitSpec_dom`, `bitSpec_rng`, `inLens_*` and
    `outLens_*`.
  - Identifiers use the Greek `μ` (U+03BC); never the micro sign `µ` (U+00B5).

## Multi-agent work (ruling: up to 1 sub-agent)

- **The lead owns the job:** the brief, the branch `fill/bb1-machine`, every commit, the final sweep and checks, the
  delivery and `REPORT.md`. Only the lead commits on `fill/bb1-machine` and pushes.
- **At most 1 sub-agent.** A suggested split:
  - the lead does the Lean work (steps 1–4);
  - the sub-agent prepares the evidence tooling: the adapted tools, the reader-insertion check and its controls, the
    new control rows of `mkctl_bb1m.py`, the extended frozen check, the name-clash scan, and the overlap searches.
  - Another split is fine if the two agents edit disjoint files and you record it. A file is reassigned only through
    the lead, and only after its owner has stopped.
- **Worktrees and olean trees.** The sub-agent has its own git worktree of the lead's clone and, if it runs Lean, its
  own TCSlib olean tree (`TCSLIB_OLEANS`). Its `.lake/packages` is a symlink to the lead's: read-only Mathlib, the
  same pins.
  - Only the lead runs `lake` and fetches the cache.
  - The lead may seed the sub-agent's olean tree by copying its own bootstrapped **TCSlib** olean tree. Copying
    Mathlib or other package trees stays forbidden (addendum, Part 1, item 2).
- **One Lean process at a time on the host** (addendum), shared by both agents. Serialize every `lean`, `lake` and
  `scripts/lean_check_tree.sh` call through one lock (for example `flock <clone>/.lean.lock …`). Do not hold the lock
  across modules.
- **The record.** `REPORT.md` records who did what. Sub-agent logs go under `evidence/subagents/<name>/` and are
  covered by the evidence-completeness rule.

## Checks and report

- **Bootstrap.** From `order.txt` (188 modules) and the narrow `roots.txt` (94), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, one Lean process at a time on the host.
  - Seal, control, scan and axiom probes may run through the adapted `seal/runner_full.py` (`lean -DmaxErrors=0
    <probe>.lean`, no `-o`, nothing written to the olean tree), as LE-gate40 and the checkpoint did.
  - **Never run `lake build`** or an unfiltered `lake exe cache get`. Run Python as `python3 -I`.
- **The root.** `TCSlib.lean` imports the whole library (1301 modules at the base), outside the narrowed bootstrap, so
  do not bootstrap it. The name-clash scan below covers its main risk. The maintainer checks `TCSlib` and
  `audits/*/Checks` on the full-library tree at landing, as for every fill of this campaign.
- **Native build.**
  - Check each changed module after each change.
  - Before each delivery, sweep the whole order (with any new helper) with rc 0 and 0 errors in both forms. That
    includes the owners, `BonehBoyenSecurity` and the facades `IdentityBased` and `AdvancedEncryption`.
  - Bind each checked source to `git show HEAD`.
- **Admissions.** Compare the `sorry` warnings with `base-sorries.txt` (57 declarations in 18 modules). The only
  change is the removal of T4: 56 remain in 17 modules, including T1, T2 and T3. A checkpoint states which it
  removed.
- **Axioms.**
  - Census every stored constant of the changed owners: `Defs`, `BonehBoyen`, the helpers, `BonehBoyenMachine`.
    Expect only `propext`, `Classical.choice` and `Quot.sound`; in particular `#print axioms exists_bb1_distinguisher`
    and the seven readers.
  - Run a **dependency trace**: a probe that walks the constant closure and lists every sorried constant reached.
    - T4 reaches none.
    - `bb1_sidSecure` reaches exactly `bb1_sim_real` and `bb1_sim_random`.
- **Headers and insertions, each with mutation controls.**
  - **`BonehBoyenMachine.lean`.** Adapt `frozen_check_bb1m.py`: permit a new helper's import and its `## Contents`
    bullet, if you add one. It must PASS with T4's body and sketch replaced. Keep its eight controls, and add:
    - an edit that spills from the sketch into the statement prose;
    - an unpermitted `## Contents` change.

    Each control must FAIL.
  - **`Defs.lean` and `BonehBoyen.lean`.** Write a `python3 -I` insertion check:
    - removing the seven blocks restores the base byte for byte;
    - each block equals the approved text byte for byte, at its position;
    - the final hashes are those above.

    Controls, each giving the stated result:
    - one character changed inside a reader: FAIL, exactly one difference;
    - one reader deleted: exactly one removal;
    - one extra line elsewhere in either file: FAIL;
    - a reader moved: FAIL;
    - a reader's docstring edited: FAIL.

  Deliver the scripts, their outputs and the controls under `evidence/headers/`.
- **Statements.** Run `decls2.py` over the PR's files:
  - against `9e7a9648`: only ADDED (the checkpoint's 166, the seven readers, your new declarations), 0 CHANGED,
    0 REMOVED;
  - against `7c0a55e0`: ADDED is exactly the seven readers and your new declarations, 0 CHANGED, 0 REMOVED.

  Run `touched.py` too: T4's header must be UNCHANGED.
- **Rule 10 evidence.**
  - **Seals.** Whole-file canonical seals A and B, in both the **strict** and the **coe** variant, of **every changed
    owner** at the final: `Defs`, `BonehBoyen`, `Draws`, `Words`, `Handler`, `Reduction`, any new helper, and
    `BonehBoyenMachine`. Each runs over its full TCSlib import closure with **`-DmaxErrors=0`**. **The coe-variant
    seal A is canonical.**
  - **Base seals.**
    - Run `Defs` and `BonehBoyen` at the issue base too. Their #331 record is LE-gate40's merged-tree supplement,
      `briefs/pairings/gates/40-pairings-statements/seals-merged/`: 0 errors.
    - For the helpers and `BonehBoyenMachine`, the checkpoint's seals (the zip's `rule10/`) are the base record.
  - **Reporting.** Report every failing declaration in each seal, and attribute every difference from the base by
    reading its raw log. The readers and the glue may add no failing declaration.
  - **Paired controls.** Run `mkctl_bb1m.py` plus new rows:
    - for each of the seven readers, a negative (the unfolding the reader replaces, stated in a consumer's context)
      and a positive (the reader);
    - for each new helper definition foreign to a later module, if any.

    Each sealed negative fails exactly once, each positive passes, and all pass unsealed (pretest the new rows
    unsealed). Strict and coe both `ALL_OK True`.
  - **The explicit-unfold scan** over the changed files: 0 foreign.
  - **Error counts (G26-N1), both forms.** Count both `error:` and `error(…)`, for example with
    `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at the base and at the final.
  - The baseline at the issue base is **92 FAIL / 103 WARN over 400 files** (the checkpoint's
    `lint/campaign-head.txt`).
  - Diff the line sets, not only the counts. There may be no new FAIL line, and no new WARN line except one you
    disclose and justify.
  - Also run `scripts/style_lint.py` on the changed files and `dev/sk15.py`.
- **Name-clash scan.** No new name (public or private, namespaces resolved) may already be declared in `TCSlib/` or
  `audits/` at the issue base. Deliver the script and its output under `evidence/clash/`.
- **Report.** `REPORT.md` gives:
  - the base and the status of T4;
  - who did what;
  - the changed files, with their lines at the base and at the final, and the sketch edit;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - promotion requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered:
  - the seal and control sources, manifests and request records;
  - the header and insertion checks, their outputs and controls;
  - the clash scan and the dependency trace;
  - every raw log and `results.jsonl`;
  - the sub-agent's logs;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers, as the addendum
  says. It is an environment report, not a failed fill.
- **E-SCOPE (frozen files).** Any of these is an E-SCOPE:
  - a reader does not elaborate verbatim at its position;
  - a reader fails its owner's seal;
  - the proof needs any other frozen-file change or an import outside the order.

  Stop that line of work and ask Seyoon in your session (*Scope requests*). Continue only on his approval, and record
  it.
- **E-ROUTE (proof).** The integrated proof fails in a way that no change inside the owned files fixes, or T4 looks
  false as stated. Stop and state the exact obligation, with the failing goal or the counterexample.
- **How to report.**
  - Push a checkpoint, `fill bb1-machine: checkpoint N (blocked: <code>)`, whose `REPORT.md` opens with the blocker:
    its code, the exact obligation or request, and the logs.
  - Keep everything that already passes.
  - Never work around a blocker by weakening a statement, adding a hypothesis, editing a frozen file without
    approval, or using a private stand-in.

**Ready to dispatch**
