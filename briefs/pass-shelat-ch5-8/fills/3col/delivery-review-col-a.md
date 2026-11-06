# Delivery review: fill unit col-a (`R3COL_witnessRelation`'s decider, `colRep_efficientProverProof`)

- **Delivery:** `inbox/fills/col-a/` on `exchange/pass-shelat-ch5-8` at
  `29171e5ca183009254d1b35840b3d0cebab10f5b` (REPORT.md, 3 patches, `src/`, `evidence/` with
  `evidence/seal/`). The exchange checkout was fetched to `3c7c68ce`; the folder is unchanged
  since `29171e5c` (empty `git diff --stat`). The checkout's branch was not moved.
- **Worker branch:** `fill/col-a`, three commits (`ec6d3e6a`, `14458924`, `c0436253` in the
  REPORT), base `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit, the head of #210).
- **Brief:** `brief-issued.md`, unit col-a, with `review.md`. **Notes:** `NOTES-2026-11-07.md`.
  **Policy:** `policy.md`.
- **Reviewed:** 2026-11-06, as an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean ran against this review's own olean copy (below), one process at a time, never
    `lake build` or `lake exe cache get`;
  - the seal names were collected from the elaborated terms of every new constant, not taken
    from the worker's list.

## Verdict: **land after edits**

Both targets are filled and sorry-free:
- the `decidable` clause of `R3COL_witnessRelation` is `exact ColRep.R3COL_decidable`;
- `colRep_efficientProverProof` is a `where` structure over eight private `colRep_*` lemmas, one
  private definition, and the helper `ColRepSound.lean`.

`R3COL_witnessRelation`, `colRep_efficientProverProof` and `colRep_interactiveProof` print
`[propext, Classical.choice, Quot.sound]`. In `col_zeroKnowledgeProof` and the `NP.lean`
wrappers, the only `sorryAx` comes from col-b's `col_zk`.

The other checks pass:
- the statements and docstrings are frozen;
- `Protocol.lean`, both helpers, everything downstream and `audits/pass-shelat/Checks`
  elaborate;
- all 95 new constants use only the standard axioms;
- the rule-10 seal holds under this review's own name list, which is wider than the worker's.

The series also applies on top of #210's next round (`msgAt_eq` beside `msgAt`).

There are **no blockers and no majors**. The edits are minor or nits:
- **E1** is the facade edit;
- **E2** and **E4** replace two undisclosed copies of upstream library code:
  `StateLoop.xor_poly`, and `EnsembleLemmas.blocks`, which is `FunFamily.blocks`;
- **E3** replaces a disclosed two-line copy of core's `bne_eq_false_iff_eq`;
- **E5** refreshes `R3COL_witnessRelation`'s proof sketch, which no longer describes the proof
  (docstring only, under the standing ruling);
- **E6** and **E7** are optional sketch and module-docstring syncs.

The disclosure ledger is amended (**D1**).

## Checks

| # | Check | Result |
|---|---|---|
| 0 | Olean tree | `$SP/fill-rsa-oleans` was copied to `$SP/rev-cola-oleans`. **The copy did not cover col-a's order list.** It had no olean for 32 order-list modules: every `ZeroKnowledge` module from `EncodingMachines` on (GI, GIZK, Commitment, all of `ThreeColoring/`, `NP`, the facades). Outside the order list, the `NumberTheory` facade, which `Checks` needs, was also missing. The tree was also being written while it was copied: the RSA worker rebuilt `Candidates/RSA` and the modules after it at 15:14–15:15. **Provenance of the modules present** (`tools/provenance.py`, `provenance-checks-closure.log`, over the 420-module import closure of `Checks`): 381 are consistent. Each olean is newer than the last commit touching its source at or before `16a7d02d` and newer than the oleans it imports. The order list has no `Candidates` module, and its present modules import none. Three were flagged: `Interaction` and `InteractiveProofs`, whose oleans were older than an import's, and the `Complexity/Randomized` facade. In the copy, `Interaction` and `InteractiveProofs` were rebuilt from base sources and are **byte-identical** to the copied oleans (`olean-cmp.log`). This also shows the build is deterministic. **Rebuilt in the copy, in order** (`$SP/tools/ladder-ol.sh`, `build-order.txt`, `ladder.log`): the 32 missing modules, with the two helpers before `Protocol`. Then, for `Checks`, the `NumberTheory` facade and, from base sources, `Candidates/{RSA, Rabin, DiscreteLog, DiscreteLogHardcore, ElGamal}`, the `Candidates` facade and the `Randomized` facade. This replaced the RSA-fill oleans that had entered the copy. All 45 runs exit 0 (the two byte-compare rebuilds included). `fill-rsa-oleans` was only read. |
| 1 | Integrity | `git am` of the 3 patches onto `16a7d02d` in the fresh worktree `$SP/wt-rev-cola` (`.lake/packages` linked): clean (`am.log` empty), tree `582c4cd0`. All three files match `src/` byte for byte (`cmp`). **Files changed** (`diffstat.txt`): `ThreeColoring/Protocol.lean` (+352 −3), `ThreeColoring/ColRepWitness.lean` (new, 333 lines), `ThreeColoring/ColRepSound.lean` (new, 248 lines). That is `3 files changed, 930 insertions(+), 3 deletions(-)`. The three deleted lines are the two `sorry`s and the `:= by` header line of `colRep_efficientProverProof`. |
| 2 | Statement freeze and scope | `declfreeze.log`: all 58 base declarations are present, with headers and docstrings unchanged. Two lines are script artefacts. "PROOF-CHANGED `col_efficientProverProofErr`" is the new section header inserted after that theorem, at a declaration boundary. "HDR-CHANGED `colRep_efficientProverProof`" comes from the `:= by` → `where` split. `target-stmt.log` compares the statement text up to `:= by` and `where`: **equal**. The docstrings of both targets and of `colRep_interactiveProof` are unchanged. Sorries: base 2, head 0. **New in `Protocol.lean` (10):** all `private`, all prefixed `colRep_` (9 theorems and the definition `colRep_challenge`), in one block between `col_efficientProverProofErr` and `colRep_efficientProverProof`. **Helpers:** both are in namespace `TCSlib.Cryptography.ColRep`, between 150 and 600 lines, with the full policy §1 header. They hold 18 public declarations and 12 private ones. The 12 privates are all in `ColRepWitness`; only one of them carries the `colRep_` prefix, which the brief requires only in the owned file. Neither helper names `colProverRep`, `colVerifierRep`, `colProtocolRep`, `colProver`, `colVerifier`, `colCoinSlice` or `colIterations`. Everything that names them is in `Protocol.lean`. There is no `@[simp]`, no new `attribute`, and no shadow definition. **Notes item 5:** there is no declaration named `msgAt_eq` or `edgeIdxOfMsg_eq`, and no hunk touches `msgAt`'s block (base line 105; the hunks are at 7–11, 916–919, 963+ and 988+). `apply-after-210.log`: on a scratch repository at base, plus stubs of exactly #210's next-round lemmas (`msgAt_eq` after `msgAt`, `edgeIdxOfMsg_eq` after `edgeIdxOfMsg`; col-b review's `frontier-stubs-scratch.diff`), the three patches apply with plain `git am`. |
| 3 | Elaboration | `module-checks.log` (`scripts/lean_check_tree.sh`, `TCSLIB_OLEANS=$SP/rev-cola-oleans`): `ColRepWitness` 4 s, `ColRepSound` 3 s, `Protocol` 8 s, `Simulator` 5 s, facade `ThreeColoring` 2 s, `NP` 10 s, facade `ZeroKnowledge` 2 s, `audits/pass-shelat/Checks` 120 s. All exit 0, with 0 errors. The helpers and `Protocol.lean` have **0 warnings**. The only `sorry` warning is `Simulator.lean:778`, col-b's `col_zk`. The downstream set (`downstream.txt`) is `SimulatorLemmas`, `SimulatorNumeric`, `SimulatorMachine`, `Simulator`, `ThreeColoring`, `NP`, `ZeroKnowledge` and `Checks`; the ladder elaborated all of them (`ladder.log`). |
| 3 | Axioms | `axioms.log` (`probe/Axioms.lean`): `R3COL_witnessRelation`, `colRep_efficientProverProof`, `colRep_interactiveProof` and the public `ColRep` headlines (`R3COL_decidable`, `r3colTest_iff`, `r3colTest_poly`, `decGraph_fst`, `exec_four_mul`, `statClose_edgeBlocks`, `pushesUniform_blockRead`, `mul_edgeCount_le`) print `[propext, Classical.choice, Quot.sound]`; `drop_take_ofFn_blockRead` and `chView_congr` print `[propext, Quot.sound]`. A `collectAxioms` sweep over all **95** new constants finds **0** non-standard. The 95 are both helpers, the `colRep_*` privates and their auxiliaries, the two targets, and `colRep_interactiveProof`. `col_zk`, `col_hvzk`, `col_zeroKnowledgeProof`, `zk_proof_of_levinReduction`, `zk_proof_of_owp_levinReduction`, `exists_commitment_zk_proof_of_owp_levinReduction`, `zk_proof_of_witnessRelation(_of_owp)` and `zk_proof_of_mem_NP(_of_owp)` print `sorryAx`. In each, the only declaration in the closure whose own term mentions `sorryAx` is `col_zk` (`SORRYSRC` lines). `Checks` prints the same lines (`checks-out.log`, lines 348–360 and 467–472). |
| 3 | Facade | E1 was checked as part of the edited chain (`edits/edited-checks.log`): `ColRepWitness`, `ColRepSound`, `Protocol`, the four `Simulator*` modules, the facade, `NPLemmas`, `NP`, `Encryption`, the facade `ZeroKnowledge` and `Checks` all exit 0. `campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge` gives 11 FAIL / 27 WARN at the head and 9 FAIL / 27 WARN with E1–E7. The 9 are the base's: six `ThreeColoring.lean` facade FAILs and three GI/GIZK ones. |
| 4 | Rule 10 | See finding 9. |
| 5 | Routes and sketches | See findings 7, 8 and 10. |
| 6 | Duplication | See findings 4–6 and 11. |
| 6 | Lint and size | `style_lint.py` on the three files gives one finding, the size of `Protocol.lean` (`style-lint-head.log`); with E1–E7, the same single finding (`edits/style-lint-edited.log`). Every proof over 20 lines has a **Proof sketch.** (`prooflen.log`): `colRep_accept_le` 93 lines, `colRep_sound` 52, `exec_four_mul` 40, `enc_iff` 37, `proper_iff` 33, `colRep_outV_honest` 28. **Sizes** (`wc -l`): `Protocol.lean` 1345 (999 at the base; 1354 with E5–E7; style_lint counts one more line), `ColRepWitness.lean` 333 (320 with E2–E3), `ColRepSound.lean` 248 (245 with E4). The size exception for `Protocol.lean` is approved. The campaign lint's check 8 lists the same three base names for `Protocol.lean` and none for the helpers. |

## Findings

1. **note: integrity.** The replay is clean and equals `src/`. The diff touches only the owned
   file and the two new helper modules, as the REPORT says.

2. **note: statement freeze, scope and notes item 5 are confirmed** (check 2).
   - The `where` body has the six fields of `EfficientProverProof`:
     - `efficientV` and `efficientP` come from `colVerifierRep_efficient` and
       `colProverRep_efficient`;
     - `complete` uses the second component of `colProtocol_proverBounded` with
       `Protocol.proverBounded_iff`;
     - `sound` uses the brief's strict-clause `ε`, with `N² (1/2)^N` written
       `N² 2⁻¹^N`;
     - `boundedP` and `completeWitness`.
   - Every witness destructuring goes through `R3COL_iff`.
   - The series does not conflict with #210's next round. col-b's E7 frontier needs only
     `msgAt_eq`'s statement.

3. **note: elaboration and axioms** (check 3). The REPORT's sweep and axiom prints are
   reproduced. The REPORT's attribution is confirmed: in every consumer, the `sorryAx` comes
   from `col_zk` alone.

4. **minor: an undisclosed copy of an upstream lemma (edit E2).**
   - **The copy.** `ColRepWitness`' private `colRep_xor_poly` is
     `Complexity.StateLoop.xor_poly` (`Complexity/Randomized/Build/StateLoop.lean:138`,
     order-list line 34). That lemma is in `ColRepWitness`' import closure
     (`closure-ColRepWitness.txt`). The statement is the same up to notation (`xor` and `^^`
     are the same core function), and so is the proof (`polyTimeComputable_ite` with
     `not_poly`).
   - **What the REPORT says.** It discloses the copy as one of
     `Complexity.polyTimeComputable_xor` (`ClassP/BinaryArith/Basic.lean`, outside the order
     list) and asks for that lemma to be moved upstream (R-1).
   - **The fix.** No move is needed. **E2** deletes `colRep_xor_poly` and cites
     `StateLoop.xor_poly`, and **R-1 is withdrawn**. Notes item 4 asked for exactly this
     search.

5. **minor: an undisclosed inline copy of `FunFamily.blocks` (edit E4).**
   - **The copy.** `pushesUniform_blockRead` builds `let e := (Equiv.arrowCongr
     finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)` and proves its apply
     form by `rfl`. Mathlib has no such equivalence. The same construction is TCSlib's
     `FunFamily.blocks` (`Asymptotic/OneWay.lean`), `HardCoreLoops.blocksEquiv`, and the
     public `EnsembleLemmas.blocks` (`Asymptotic/EnsemblesLemmas.lean:366`, in the closure).
     `EnsembleLemmas.blocks` comes with the published `blocks_apply` (`blocks q ℓ w i j = w
     (finProdFinEquiv (i, j))`) and `take_drop_ofFn_blocks`.
   - **The REPORT's alternatives.** It names only `GIZK.tapeBlock` and `GI.blocksEquiv` as near
     duplicates. Notes item 4 named `FunFamily.blocks` as a copy found before.
   - **The fix.** **E4** uses `EnsembleLemmas.blocks K b` with `EnsembleLemmas.blocks_apply`.
     `EnsembleLemmas.blocks` is then a new foreign reading, and the edited seal includes it.
   - **R-4 is superseded.** `EnsembleLemmas.blocks`, `blocks_apply` and
     `take_drop_ofFn_blocks` are the published interface R-4 asks for.
     `drop_take_ofFn_blockRead` is the castLE (`C ≥ K b`) form of `take_drop_ofFn_blocks`,
     and it goes in the ledger (D1).

6. **nit: a disclosed two-line copy of a core lemma (edit E3).** `eq_of_xor_eq_false` is core's
   `bne_eq_false_iff_eq.1` (`xor` is an abbreviation of `bne`), as the REPORT says. **E3**
   deletes it and uses `bne_eq_false_iff_eq.1` at both call sites.

7. **minor: `R3COL_witnessRelation`'s frozen proof sketch no longer describes the proof (edit
   E5).**
   - **What is stale.** The sketch says the decider is polynomial-time "by
     `polyTimeComputable_pairEq` on the re-encodings (`polyTimeComputable_blockMap`,
     `polyTimeComputable_iterateEmit`) and a scan … (`polyTimeComputable_iterate` with an
     accumulated conjunction)". The proof uses none of these. It uses the scan form with two
     `EncodingMachines.firstIdx` searches (finding 10).
   - **The policy.** §3 says: "A sketch that describes a proof the code no longer performs is
     worse than no sketch".
   - **The fix.** **E5** rewrites the sketch paragraph only. It names
     `ColRep.R3COL_decidable`, the test `ColRep.r3colTest`, the three scan conditions with
     their published lemmas, and the `firstIdx` search. The statement line of the docstring
     ("decided in polynomial time by re-encoding the decoded graph and colouring and checking
     every edge") still describes `T` and is kept. The standing ruling allows this edit.

8. **nit: `colRep_efficientProverProof`'s sketch is still true but can name the route (edits E6
   and E7, optional).**
   - **What still holds.** The sketch's "`StatClose.prod` iterated" is what
     `OneWay.statClose_pi` does, and "a function of the earlier challenges through `exec`"
     holds.
   - **What it omits.** The outright rejection for ill-formed `x` or `n < 2`, and the two
     generic lemmas.
   - **E6** adds them: `ColRep.exec_four_mul`, `ColRep.chView`, `OneWay.statClose_pi`,
     `ColRep.statClose_edgeBlocks`, and the outright-rejection clause. It is docstring only.
   - **E7** adds the two helpers to `Protocol.lean`'s module docstring, beside `Machines`,
     `Parties` and `ProtocolProofs`.

9. **note: rule 10 under this review's seal; the new code reads no foreign definition.**
   - **Collection** (`probe/Collect.lean`, `collect.log`). The probe ran over the 94 new
     constants; the sweep's 95 also count the base `colRep_interactiveProof`. It takes the
     TCSlib definitions of other modules that occur in their elaborated types and values,
     without reducible ones or instances. It widens the set with the statements of every
     constant used and the bodies of own-module definitions used.
   - **Matchers.** There is **no foreign compiler-generated matcher** and no foreign auxiliary
     constant. No collected name is a `@[simp]` definition.
   - **The lists.**
     - **`ColRepWitness` (15):** `PolyTimeComputable`, `pairFstD`, `pairSndD`, `colorVal`,
       `divNum`, `firstIdx`, `modNum`, `ProperColoring`, `R3COL`, `decColoring`, `decGraph`,
       `decGraphAt`, `encColoring`, `encGraph`, `Turing.pairEncode`.
     - **`ColRepSound` (7; 8 with E4):** `countTrue`, `PushesUniform`, `StatClose`,
       `encGraph`, `exec`, `moverIsV`, `sampleEdgeIdx`, and, with E4,
       `EnsembleLemmas.blocks`.
     - **`Protocol` (36, without `PolyExpr.eval`):** these include `ColRep.chView` and
       `ColRep.blockRead`, `exec`, `Protocol.outV/withV/ProverBounded`, `Strategy.coinLen`,
       `Strategy.Efficient`, `uprob`, `StatClose`, `Negligible`, `L3COL`, `R3COL`,
       `ThreeColorable`, `edgeIdxOfMsg`, `edgeMsg`, `edgeOf`, `edgeAt`, `sampleEdgeIdx`,
       `samplePerm3`, `padColor`, `encColor`, `decColor` and `multiCom` (`seal/mine.txt`).
   - **How it was sealed** (`seal/mkseal.py`, `seal/names-*-all.txt`). Each list was united
     with the worker's 35 names, which adds `instDecidableProperColoring`. `PolyExpr.eval` was
     left unsealed (ruling Q1).
     - In the helpers, the seal covers the whole file.
     - In `Protocol.lean` there are two sections: `revSealA` around `R3COL_witnessRelation`,
       and `revSealB` from the "parties unfolded" header through `colRep_efficientProverProof`.
   - **Results.**
     - All three files elaborate sealed with only the controls as errors
       (`RevSealed*.out`), and unsealed with none (`RevControl*.out`). The edited files
       behave the same (`RevSealedEdited*.out`).
     - Sealing `PolyExpr.eval` as well changes nothing (`RevSealedEval*.out`).
     - **Controls:** `colorVal` by `rfl` and `R3COL` destructured (`ColRepWitness`);
       `moverIsV` and `exec … 0` by `rfl` (`ColRepSound`); `edgeIdxOfMsg` and `ColRep.chView`
       by `rfl` and `R3COL` destructured (each `Protocol` section). Each closes unsealed and
       fails sealed.
   - **One base reading surfaced.** In `revSealA`, line 919 fails sealed. That is the **base**
     `bounded` clause of `R3COL_witnessRelation` (`rintro x y ⟨n, G, c, rfl, rfl, -⟩`), which
     destructures `R3COL` by its body. It is not col-a's line, so it is not a finding against
     the delivery. The published replacement is `R3COL_iff` (P1); see D1. col-a's clause on
     the next line elaborates sealed.
   - **Explicit readings** (`rwids.txt`, `probe/RwIds.lean`, `rwids.log`). All 138
     identifiers that the new code passes to `rw`, `simp`, `simpa` or `unfold` resolve to
     theorems, local hypotheses or col-a's own privates (`badVertex`, `badEntry`, `scanTest`
     and the like). No TCSlib, core or Mathlib definition is among them.
     - The one new bare `simp` (`simp [hm]` in `colRep_outV_honest`) is
       `simp only [hm, length_encGraph, List.getD_eq_getElem?_getD, true_or, and_self,
       decide_true]` (`simpq.log`).
     - Every `show` and `of_decide_eq_true` reads an owned definition: `colVerifierRep`,
       `colProverRep`, `colProtocolRep`'s rounds, `colWellFormed`, `colRep_challenge`, the
       local `Φ`.
   - **Against the worker's evidence.**
     - The worker's scan was not widened, so its 35 names omit `Strategy.Efficient`,
       `decColor`, `encColor`, `edgeAt`, `multiCom` and `padColor`. These are reached through
       statements and the owned `colVerify`'s body.
     - The worker's copies were sealed in a separate namespace. This review sealed in place.
     - Both reach the same result.
   - **Remaining readings: none in the new code.** The derived workaround `ColRep.decGraph_fst`
     uses only the **statement** of the public `GIZK.decGraph_eq_of_sqrt`, and passes with
     `decGraph` and `decGraphAt` sealed. That lemma's own proof is `rfl` on `decGraph` inside
     `GraphIsomorphismZK/Simulator.lean`, a pre-existing base reading. **R-2 is endorsed**
     (finding 11).

10. **note: routes.**
    - **The decider is sound and polynomial-time through published lemmas.**
      - `r3colTest` is the brief's test verbatim, and `r3colTest_iff` uses `R3COL_iff`,
        `decGraph_encGraph` and `decColoring_encColoring`.
      - Polynomial time follows from the pointwise agreement with the scan form
        (`scanTest_iff`), which has three parts:
        - `|x| = n²` (`wf_iff`, from `ColMachines.encGraph_decGraph_eq_take`);
        - `|y| = 2n` with no badly encoded vertex (`enc_iff`, from P3 and
          `ColMachines.decColoring_val`);
        - no monochromatic set entry (`proper_iff`, from P2 and
          `ColMachines.decGraph_apply`).
      - Each "no" is `EncodingMachines.firstIdx`. That is a public bounded-search host with
        published contract lemmas (`firstIdx_eq_iff`, `polyTimeComputable_firstIdx`). Policy
        §1's "hosts come first" is met.
      - The tests use `getBit_poly`, `colorVal_poly`, `divNum_poly`/`modNum_poly` (through
        `divNum_eq`/`modNum_eq`), `unarySqrt_poly` and `eqTest_poly`.
      - The departure from the suggested `blockMap`/`iterate` machine is a simplification
        and is sound. The seal confirms that `firstIdx`, `colorVal`, `divNum` and `modNum`
        are read only through these lemmas.
    - **`ColRep.exec_four_mul` is sound.** Its hypotheses `hodd`/`hmid` are discharged in
      `colRep_views` by the owned unfoldings `colRep_verifierRep_next_odd/even`.
    - **It is in part a copy of `GI.exec_repViews`.** The induction step's four `moverIsV`
      facts and the `rw [show 4 * (i + 1) = …, exec_succ ×4]; simp only [h0, h1, h2, h3, …]`
      block are `GI.exec_repViews`'s proof text (`SoundnessRepGI.lean:72–91`, the `rw`/`simp only` lines at 88–91). The `getD`
      bookkeeping follows `GI.getD_Vs_even/odd`.
    - **The REPORT's reason for not citing `GI.exec_repViews` is correct.** That lemma only
      rewrites `exec` into `GI.repViews`. `GI.repViews` and `GI.Vs` have no published
      equations: `repViews_snd/fst` are specialized to `giVerifierRep`. Reading them would mean
      `simp only [repViews]`, a rule-10 violation. So the generic lemma is needed, and **R-3
      is endorsed**: promote `ColRep.exec_four_mul` as the shared form.
    - **Disclosure.** The REPORT discloses the lemma as "combines and generalizes". It does not
      say that the four-step block is copied text. This goes in the ledger (D1).
    - **`chView`** is `GI.PsOf` generalized, with `PsOf b = chView (fun i => [b i])`; this
      is disclosed.

11. **note: the REPORT's §4 requests.**
    - **R-1:** withdrawn (finding 4).
    - **R-2:** endorsed. `Encoding.lean` publishes no equation for `(decGraph x).1`. Three base
      places read it through other files' `rfl`s: `GIZK.decGraph_eq_of_sqrt` (and its twin in
      `GraphIsomorphism/Proofs.lean`), `ColMachines.decGraph_apply`, and `SimulatorNumeric`'s
      inline `rfl`.
    - **R-3:** endorsed (finding 10).
    - **R-4:** superseded by `EnsembleLemmas.blocks` (finding 5).
    - **R-5:** endorsed: `ColProofs.two_le_of_edge`, `ColProofs.sampleEdgeIdx_ofFn_castLE` and
      `GIZK.pushesUniform_castLE`.
      - Both `ColProofs` lemmas are about the original definitions, not shadows. Nothing is
        transferred by `rfl`, and the seal passes with `ProperColoring`, `edgeCount` and
        `sampleEdgeIdx` sealed.
      - The three `pushesUniform_castLE` copies are col-b review finding 6's. If the dedup
        queue retires `ProtocolProofs.lean`, the two `ColProofs` lemmas move first.
    - **Cross-unit.**
      - col-b's `ColZK.pushesUniform_offsetTable` and `ColZK.ofFn_drop_take` (in
        `$SP/wt-fill-col-b`) are offset-`a` forms of `pushesUniform_blockRead` and
        `drop_take_ofFn_blockRead`, so one shared tape-window layer would retire all four.
      - The single-block step of `statClose_edgeBlocks` repeats the inline argument of the
        private `colProtocol_sound`; this is disclosed.
    - **No Mathlib copy was found** for the remaining helpers: `mul_edgeCount_le`, `wf_iff`,
      `enc_iff`, `proper_iff`, `scanTest*` and `colRep_*`.

12. **nit: REPORT figures.**
    - The REPORT gives `Protocol.lean` as 1346 lines (+347). `wc -l` gives 1345 (+346), and
      `style_lint.py` counts 1346.
    - The REPORT's seal list is the narrower one (finding 9).
    - Everything else agrees with this review's runs:
      - the targets' status, the 10 private `Protocol.lean` declarations and the helper
        tables;
      - the sweep;
      - the axiom prints and the `sorryAx` source;
      - the lint lines (style_lint 1 finding; campaign lint 9 FAIL / 26 WARN at the base and
        11 / 27 at the head);
      - no new Mathlib roots (the helpers import TCSlib modules only).

## Landing edits (exact)

All diffs are under `$SP/review-cola/edits/`. They touch no statement and no base proof. E5–E7
change docstrings only.
- **`landing-edits.diff` (E1–E7).** It touches `ThreeColoring.lean`, `ColRepWitness.lean`,
  `ColRepSound.lean` and `Protocol.lean`. It is split into **`E1-facade.diff`** and
  **`E2-E7.diff`**.
- **`apply-check.log`.** `git apply --check` is clean on the col-a head, also on top of the
  #210 next-round stubs.
- **`facade-after-colb.diff`.** If col-b's E1 lands first, this replaces `E1-facade.diff`; it
  applies cleanly on the facade with col-b's E1. The base E1 does not apply there: both edit the
  same import lines.
- **`edited-checks.log`.** Unsealed, the edited `ColRepWitness`, `ColRepSound`, `Protocol`,
  `SimulatorLemmas`, `SimulatorNumeric`, `SimulatorMachine`, `Simulator`, `ThreeColoring`,
  `NPLemmas`, `NP`, `Encryption`, `ZeroKnowledge` and `Checks` all exit 0 with 0 errors; the
  only warning is `col_zk`'s `sorry`.
- **Sealed** (`seal/RevSealedEdited*.out`): only the controls fail, plus the base line of
  finding 9.
- **Axioms** (`axioms-edited.log`): 93 constants, 0 non-standard; the targets print the
  standard three. **Collection** (`collect-edited.log`): the only new name is
  `EnsembleLemmas.blocks`, which is sealed.
- **Lint:** style_lint reports the size line only, and campaign lint 9 FAIL, all of them the
  base's.

**E1** (facade). In `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean`, after
`import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol` insert

```lean
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepWitness
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound
```

and in `## Contents`, after the `Protocol` item (ending `(Prop-127.6).`), insert

```
* `ColRepWitness` — the decider of `R_3COL` (Def-124.f): the test of `R3COL_witnessRelation`'s
  sketch, its correctness, and its polynomial time through a scan of bounded searches.
* `ColRepSound` — generic lemmas of the `n|E|`-fold protocol (Prot-127.5, Prop-127.6): the
  views of four-move iterations against a challenge verifier, the blocks of a uniform tape,
  and `K` edge samplers close to uniform.
```

With col-b's E1 already applied, use `facade-after-colb.diff`, which inserts the same lines
before col-b's.

**E2** (finding 4). In `ColRepWitness.lean`, delete `colRep_xor_poly` with its docstring. In
`badVertex_poly`, replace both `colRep_xor_poly` by `StateLoop.xor_poly`. In its docstring,
extend the lemma list to
``(`getBit_poly`, `colorVal_poly`, `divNum_poly`, `modNum_poly`, `eqTest_poly`,
`StateLoop.xor_poly`)``.

**E3** (finding 6). In `ColRepWitness.lean`, delete `eq_of_xor_eq_false` with its docstring. In
`enc_iff`, replace `exact eq_of_xor_eq_false hb.1` and `exact eq_of_xor_eq_false hb.2` by
`exact bne_eq_false_iff_eq.1 hb.1` and `exact bne_eq_false_iff_eq.1 hb.2`.

**E4** (finding 5). In `ColRepSound.lean`, replace the docstring and the first seven tactic lines
of `pushesUniform_blockRead` (the statement is unchanged) by

```lean
/-- **The blocks of a uniform tape are independent and uniform**: `blockRead` is the restriction
to the first `K b` bits (`GIZK.pushesUniform_castLE`) followed by the blockwise bijection
`EnsembleLemmas.blocks K b : (Fin (K b) → Bool) ≃ (Fin K → Fin b → Bool)`
(`EnsembleLemmas.blocks_apply`). -/
theorem pushesUniform_blockRead (b K C : ℕ) (h : K * b ≤ C) :
    HardcoreBit.PushesUniform (blockRead b K C h) := by
  have hc := (GIZK.pushesUniform_castLE (B := Bool) h).comp
    (HardcoreBit.pushesUniform_equiv (EnsembleLemmas.blocks K b))
  convert hc using 1
  funext r t j
  rw [EnsembleLemmas.blocks_apply, blockRead_eq]
```

The last four lines (`congr 1` … `ring`) stay.

**E5** (finding 7; docstring only). In `Protocol.lean`, replace the `**Proof sketch.**` paragraph
of `R3COL_witnessRelation` by

```
**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` is `ColRep.R3COL_decidable`
(`ThreeColoring/ColRepWitness.lean`) with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))` (`ColRep.r3colTest`), correct by `R3COL_iff`,
`decGraph_encGraph` and `decColoring_encColoring`. It is polynomial-time because it agrees with a
scan form, with `n = √|x|` (`ColRep.decGraph_fst`): `|x| = n²`
(`ColMachines.encGraph_decGraph_eq_take`); `|y| = 2n` and no vertex `i < n` whose bits `2i`,
`2i + 1` differ from those of its colour value (`getD_encColoring_two_mul`,
`getD_encColoring_two_mul_add_one`, `ColMachines.decColoring_val`); no set entry `j < n²` whose
endpoints `j / n`, `j % n` have equal colour values (`ProperColoring_iff`,
`ColMachines.decGraph_apply`). Each "no" is a bounded search `EncodingMachines.firstIdx` that
finds nothing (`firstIdx_eq_iff`, `polyTimeComputable_firstIdx`), over tests built from
`getBit_poly`, `ColMachines.colorVal_poly` and unary arithmetic. -/
```

**E6** (finding 8; optional, docstring only). In the sketch of `colRep_efficientProverProof`:
- after "`exec_succ`" insert ", through the generic `ColRep.exec_four_mul`";
- after "(strict clause):" insert "if `x` is ill formed, or `n < 2`, the verdict is `[false]`
  on every tape;";
- replace "`StatClose.prod` iterated," by "`OneWay.statClose_pi` over the coin blocks:
  `ColRep.statClose_edgeBlocks`;";
- replace "through `exec`)" by "through `exec`, `ColRep.exec_four_mul` and `ColRep.chView`)".

The exact rewrapped text is in `E2-E7.diff`.

**E7** (finding 8; optional). In `Protocol.lean`'s module docstring, after
"`ThreeColoring/ProtocolProofs.lean`" replace the period by
"; the decider of `R_3COL` is `ThreeColoring/ColRepWitness.lean`, and the generic lemmas of the
`n|E|`-fold protocol are `ThreeColoring/ColRepSound.lean`."

**D1** (findings 5, 9, 10, 11; ledger, no code). Add to the integration ledger for
`ThreeColoring/{Protocol,ColRepWitness,ColRepSound}.lean`:
- **R-1 is withdrawn** (`StateLoop.xor_poly`). If E2 does not land, record `colRep_xor_poly` as
  a copy of `StateLoop.xor_poly`.
- **Promotion requests:**
  - `ColRep.exec_four_mul` as the shared form of four-move iterations (R-3). Its induction step
    is `GI.exec_repViews`'s proof text. `GI.repViews_snd/fst` could later be re-derived from
    it.
  - `decGraph_fst`, or an equation of `decGraph`, in `Encoding.lean` (R-2).
- **R-4 is superseded** by `EnsembleLemmas.blocks`, `blocks_apply` and `take_drop_ofFn_blocks`.
  `drop_take_ofFn_blockRead` is the castLE form of `take_drop_ofFn_blocks`.
- **Near-duplicates:**
  - cross-unit: `pushesUniform_blockRead` and `drop_take_ofFn_blockRead` against col-b's
    `ColZK.pushesUniform_offsetTable` and `ColZK.ofFn_drop_take`;
  - `chView` against `GI.PsOf`;
  - `statClose_edgeBlocks`'s single block against the private `colProtocol_sound`'s inline
    step.
- **R-5:** move `ColProofs.two_le_of_edge`, `ColProofs.sampleEdgeIdx_ofFn_castLE` and the
  `pushesUniform_castLE` copies to `Language.lean` / `Sampling.lean` before the dedup queue
  retires `ProtocolProofs.lean`.
- **Base readings surfaced by this review's seal** (not col-a's):
  - `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL`. Replace it with
    `(R3COL_iff x y).1`;
  - `GIZK.decGraph_eq_of_sqrt` and `ColMachines.decGraph_apply` are `rfl` on `decGraph` in
    other files.

## Not verified

- The real #210 next-round lemmas. Only the patch application on top of stubs was checked; col-a
  does not use those lemmas.
- The facade with both units' E1 (`ThreeColoring.both.lean`): `facade-after-colb.diff` applies,
  but col-b's helpers have no olean in this copy, so the combined facade was not elaborated.
- The root `TCSlib.lean`, which is not in the order list.
- The intermediate commits of the series, one by one.
- The worker's environment logs (preflight, cache, bootstrap), which were not re-run.

## Logs (`$SP/review-cola/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- **Olean copy:**
  - `provenance-fill-rsa.log`, `provenance-checks-closure.log` (`tools/provenance.py`);
  - `checks-closure.txt`, `olean-cmp.log`, `oldolean/`;
  - `build-order.txt`, `ladder.log`.
- **Replay and freeze:**
  - `delivery/` (`git archive` of the folder), `am.log` (empty: clean), `commits.txt`,
    `diffstat.txt`, `cola.diff`;
  - `Protocol.base.lean`, `Protocol.head.lean`;
  - `tools/declfreeze_rev.py`, `declfreeze.log`, `target-stmt.log`;
  - `apply-after-210.log` (with `applytest/`).
- **Elaboration and axioms:**
  - `run-checks.sh`, `module-checks.log`, `checks-out.log`;
  - `tools/downstream.py`, `downstream.txt`;
  - `axioms.log` (`probe/Axioms.lean`).
- **Rule 10:**
  - `probe/Collect.lean`, `collect.log`, `seal/mine.txt`, `seal/worker.txt`;
  - `seal/mkseal.py`, `seal/names-{Protocol,ColRepWitness,ColRepSound}-{all,eval,edited}.txt`;
  - `seal/RevSealed*`, `seal/RevControl*`, `seal/RevSealedEval*`, `seal/RevSealedEdited*`
    (`.lean`/`.out`);
  - `tools/rwids.py`, `rwids.txt`, `probe/RwIds.lean`, `rwids.log`;
  - `probe/SimpQProtocol.lean`, `simpq.log`.
- **Duplication:** `closure-ColRepWitness.txt`, `closure-ColRepSound.txt`.
- **Lint:** `style-lint-head.log`, `campaign-lint-head.log`, `tools/prooflen.py`,
  `prooflen.log`.
- **`edits/`:**
  - the diffs `landing-edits.diff`, `E1-facade.diff`, `E2-E7.diff` and
    `facade-after-colb.diff`;
  - `apply_edits.py`, `apply-check.log`, `edited-checks.log`;
  - `style-lint-edited.log`, `campaign-lint-edited.log`;
  - `collect-edited.log`, `sealrows-edited.txt`, `axioms-edited.log`;
  - the edited files `{Protocol,ColRepWitness,ColRepSound,ThreeColoring}.edited.lean` and
    `ThreeColoring.both.lean`.

The olean copy `$SP/rev-cola-oleans` was deleted after the runs; it held the col-a head with
E1–E7. To replay, copy `$SP/fill-rsa-oleans` again and rebuild `build-order.txt` with
`tools/ladder-ol.sh`. Check first that the RSA worker is not still writing to it. The scratch
worktree `$SP/wt-rev-cola` was removed.
