# Fill col-a: REPORT (final)

**Unit:** col-a. Owned file: `ThreeColoring/Protocol.lean`. New helper modules:
`ThreeColoring/ColRepWitness.lean` and `ThreeColoring/ColRepSound.lean`. Here `ThreeColoring/`
means `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/`.

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, the head of PR #210 (branch
  `cryptography/pass-shelat-ch2-4-eqlemmas`). I worked on the local branch `fill/col-a`, which was
  never pushed and never rebased. `patches/` is `git format-patch 16a7d02d..fill/col-a`, three
  commits: `ec6d3e6a`, `14458924`, `c0436253`.
- **Exchange:** I started from `3f4e04cff265acc6681a2dc4694bebabe5448d95`. The checkpoints are
  `b3d467f` (checkpoint 1, after the decider) and `6295c7b` (checkpoint 2, after
  `colRep_efficientProverProof`). The final push carries the message `fill col-a: final`.

## 1. Targets

| Target | Status | How |
|---|---|---|
| `R3COL_witnessRelation`, `decidable` clause | **filled** | `exact ColRep.R3COL_decidable` (`ColRepWitness.lean`) |
| `colRep_efficientProverProof` | **filled** | `where` structure: private `colRep_*` lemmas in `Protocol.lean` plus `ColRepSound.lean` |

- **Checks.** `Protocol.lean` and both helpers check with zero errors and zero warnings. The
  `sorry` warning count of `Protocol.lean` went from 2 to 0.
- **Statement freeze.** No definition and no existing statement or docstring changed. The diff
  of `Protocol.lean` has three parts:
  - two `import` lines;
  - the decidable clause's `sorry`, replaced by one `exact`;
  - new private `colRep_*` lemmas and one private definition, inserted before the docstring of
    `colRep_efficientProverProof`, whose `:= by sorry` became `where …`.
- **Notes item 5.** I added no declaration named `msgAt_eq` or `edgeIdxOfMsg_eq`, and I did not
  touch `msgAt`'s block. The new code is far from it in the file (lines 10–11, 921 and 968 onward).

### 1.1 The decider (follows the sketch, with a different machine)

- **The decider.** `T = ColRep.r3colTest` is the sketch's test exactly:
  `decide (x = encGraph G ∧ y = encColoring (decColoring n y) ∧ ProperColoring G (decColoring n y))`,
  with `⟨n, G⟩ = decGraph x`.
- **Correctness** (`r3colTest_iff`) uses `R3COL_iff` (P1), `decGraph_encGraph` and
  `decColoring_encColoring`.
- **Polynomial time: deviation from the suggested machine.** I did not use
  `blockMap`/`iterateEmit`/`iterate`. `r3colTest` is pointwise equal (`scanTest_iff`) to a scan
  form built from unary tests and two bounded searches (`EncodingMachines.firstIdx`, through
  `firstIdx_eq_iff` and `polyTimeComputable_firstIdx`), with `n = √|x|`:
  - `|x| = n²`. This is the well-formedness test, through `ColMachines.encGraph_decGraph_eq_take`.
  - `|y| = 2n`, and no vertex `i < n` whose bits `2i`, `2i + 1` differ from the bits of
    `ColMachines.colorVal y i`. This uses P3 (`getD_encColoring_two_mul`,
    `getD_encColoring_two_mul_add_one`), `length_encColoring` and `ColMachines.decColoring_val`.
  - No set matrix position `j < n²` with `colorVal y (j / n) = colorVal y (j % n)`. This uses P2
    (`ProperColoring_iff`) and `ColMachines.decGraph_apply`.
- **Reason for the deviation.** Each condition is one search, so no re-encoding loop and no
  accumulated conjunction is needed. Both are a single machine over published lemmas.
- **Vertex count.** `(decGraph x).1 = √|x|` is `ColRep.decGraph_fst`. It is derived from the
  published lemma `GIZK.decGraph_eq_of_sqrt` (`GraphIsomorphismZK/Simulator.lean`, upstream in the
  order list), because `Encoding.lean` publishes no equation for `(decGraph x).1` (§4,
  request R-2).

### 1.2 `colRep_efficientProverProof` (follows the docstring sketch)

- **Verdict against any `P'`** (`colRep_outV`): `Protocol.outV_withV` after
  `rw [Protocol.withV_self] at h` (probes A1/A5), then `PolyExpr.eval_*` on the rounds.
- **Transcript.** Generic lemma `ColRep.exec_four_mul` (see §4 for why it replaces
  `GI.exec_repViews`). The verifier answers odd histories of `2t + 1` messages with the
  challenge `ch t`, and even histories shorter than `2|x|²` with `[]`. Then, after `4i` moves,
  message `2j` received by the verifier is `P'(chView ch j)` and message `2j + 1` is
  `P'(chView ch j ++ [ch j])`. The challenges are the private `colRep_challenge`: the edge
  sampled from coin block `t` for `t < n|E|`, `[]` afterwards.
- **Completeness** (`colRep_outV_honest`, every tape), iteration by iteration:
  - `colRep_proverRep_next`, then `colProver_next_nil` / `colProver_next_cons` (P10, public
    forms);
  - `edgeIdxOfMsg_edgeMsg`, `ColMachines.edgeAt_eq_some_of_pos`, `colVerify_honest`;
  - when `E ≠ ∅`, `n ≥ 2` comes from `ColProofs.two_le_of_edge`.
- **Soundness** (`colRep_accept_le`, `colRep_sound`) uses the brief's strict-clause error
  `ε N = e^{-√N} + N² 2^{-N} + 2^{-N}`. The brief's `N² (1/2)^N` is written `N² 2⁻¹^N`.
  - **Rejected outright:** `x` is ill formed, or `n < 2` (then `E ≠ ∅`). The verdict is
    `[false]` on every tape.
  - **Otherwise:**
    - fix the prover's coins (`Protocol.exists_proverCoins_le`);
    - write acceptance as a test of the `K = n|E|` sampled edges `Φ rV`, through `ColRep.blockRead`
      and `ColRep.drop_take_ofFn_blockRead` (with `colCoinSlice_eq`);
    - those edges are `K (1/2)^{|x|}`-close to uniform (`ColRep.statClose_edgeBlocks`):
      `statClose_sampleEdgeIdx` per block, `OneWay.statClose_pi`, and
      `StatClose.comp_pushesUniform` with `ColRep.pushesUniform_blockRead`;
    - transfer the bound with `StatClose.abs_uprob_sub_le_prod` (`ρ = Unit`,
      `HardcoreBit.pushesUniform_fst`);
    - apply `uprob_col_cheat_le` with `k = K`, `W = Unit`. Its `comF`/`opnF` rebuild the
      prover's view from the earlier challenges (`ColRep.chView_congr`);
    - finally `(1 − 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`), `n = √|x|`
      (`length_encGraph`, `Nat.sqrt_eq`), and `K ≤ |x|²` (`ColRep.mul_edgeCount_le`).
  - **Strictness** comes from the term `2^{-|x|} > 0`.
  - **Bound used:** `Pr[accept] ≤ (1 − 1/|E|)^{n|E|} + n|E| (1/2)^{|x|} ≤ e^{-√|x|} + |x|² 2^{-|x|}`.
- **Negligibility:**
  - `negligible_exp_neg_sqrt_div (C := 1)`, through `Nat.div_one`;
  - `negligible_two_pow_neg.mul_pow 2`;
  - `negligible_two_pow_neg`;
  - combined with `Negligible.add`.
- **Other fields:**
  - `colProverRep_efficient` and `colVerifierRep_efficient` (from `hC.easy`);
  - `boundedP` and the completeness bound: the second component of
    `colProtocol_proverBounded`;
  - the coin length: `Strategy.coinLen_eq` (P4).
- **Witness destructuring** goes through `R3COL_iff` everywhere in the new code.

## 2. New declarations

### 2.1 `ThreeColoring/ColRepWitness.lean` (333 lines; namespace `TCSlib.Cryptography.ColRep`)

**Role:** the decider of `R_3COL`.

| Declaration | Kind | Lines | Role |
|---|---|---|---|
| `decGraph_fst` | public theorem | 5 | `(decGraph x).1 = √|x|` |
| `r3colTest` | public def | 5 | the decider (the sketch's `T`) |
| `r3colTest_eq` | public theorem (`rfl`) | 9 | its defining equation (policy §1) |
| `r3colTest_iff` | public theorem | 16 | correctness |
| `r3colTest_poly` | public theorem | 5 | polynomial time |
| `R3COL_decidable` | public theorem | 6 | the decider clause, used by `Protocol.lean` |
| `badVertex`, `badEntry`, `scanTest` | private defs | 4, 3, 7 | the scan form |
| `colRep_xor_poly` | private theorem | 6 | XOR of two tests is poly-time (copy, §4) |
| `eq_of_xor_eq_false` | private theorem | 4 | `a ^^ b = false → a = b` |
| `wf_iff`, `enc_iff`, `proper_iff`, `scanTest_iff` | private theorems | 15, 43, 37, 13 | scan form ↔ the sketch's test |
| `badVertex_poly`, `badEntry_poly`, `scanTest_poly` | private theorems | 15, 14, 19 | poly-time of the scan form |

### 2.2 `ThreeColoring/ColRepSound.lean` (248 lines; namespace `TCSlib.Cryptography.ColRep`)

**Role:** generic lemmas for the repeated protocol. None of them names a party.

| Declaration | Kind | Lines | Role |
|---|---|---|---|
| `chView` | public def | 4 | the prover's view `[ch 0, [], …, ch (i-1), []]` |
| `chView_zero`, `chView_succ` | public theorems (`rfl`) | 2, 3 | its case equations (policy §1) |
| `length_chView`, `chView_congr` | public theorems | 6, 12 | its length; it depends only on earlier challenges |
| `exec_four_mul` | public theorem | 59 | the views after `4i` moves against a challenge verifier |
| `blockRead` | public def | 7 | the first `K` blocks of `b` bits of a tape |
| `blockRead_eq` | public theorem (`rfl`) | 7 | its defining equation |
| `pushesUniform_blockRead` | public theorem | 16 | the blocks of a uniform tape are uniform |
| `drop_take_ofFn_blockRead` | public theorem | 19 | the list slice of a block |
| `statClose_edgeBlocks` | public theorem | 16 | `K` edge samplers are `K (1/2)^T`-close to uniform |
| `mul_edgeCount_le` | public theorem | 11 | `n |E| ≤ |x|²` on an encoded graph |

### 2.3 `Protocol.lean` (all private; prefix `colRep_`)

| Declaration | Lines | Role |
|---|---|---|
| `colRep_outV` | 12 | the verdict in published form |
| `colRep_challenge` (def) | 4 | the challenge of iteration `t` |
| `colRep_verifierRep_next_odd`, `_even`, `_end` | 12, 7, 16 | the repeated verifier unfolded (owned definition) |
| `colRep_proverRep_next` | 10 | the repeated prover unfolded (owned definition) |
| `colRep_views` | 22 | `exec_four_mul` for `colVerifierRep` |
| `colRep_outV_honest` | 40 | completeness on every tape |
| `colRep_accept_le` | 107 | the acceptance bound |
| `colRep_sound` | 67 | the strict soundness clause |

All new public names are under `ColRep`. They have docstrings with `[PS10, …]` tags and a proof
sketch where nontrivial. No new declaration carries `@[simp]`.

### 2.4 File sizes

- **`Protocol.lean`: 1346 lines** (999 at the base, +347).
- It passes 1000 under the user's size exception of 2026-11-06 (no split, also not at landing).
- **Why it grows.** Everything added names `colProverRep`, `colVerifierRep`, `colProtocolRep`,
  `colProver`, `colCoinSlice` or `colIterations`, so the brief keeps it in `Protocol.lean`.
  The only addition that named none of them, `n|E| ≤ |x|²`, was moved to the helper
  (`ColRep.mul_edgeCount_le`).
- Both helpers are inside 150–600 lines and carry the full policy §1 header.

## 3. Error accounting

`col_zk` is col-b's target. For `colRep_efficientProverProof` I used the brief's error
`ε N = e^{-√N} + N² (1/2)^N + 2^{-N}`, unchanged in content (§1.2).

## 4. Reuse-not-copy screen and requested shared lemmas

Before writing each helper I searched TCSlib (grep across `TCSlib/`) and the pinned Mathlib/core.

### 4.1 Disclosed copies and near-duplicates

| New | Close existing lemma(s) | Why not reused / what would replace it |
|---|---|---|
| private `colRep_xor_poly` | **copy** of `Complexity.polyTimeComputable_xor` (`Complexity/ClassP/BinaryArith/Basic.lean`) | That module is not in the order list, so it cannot be imported. **Request R-1:** move `polyTimeComputable_xor` upstream, next to `polyTimeComputable_not` in `ClassNP/PolyTimeBlockLoop.lean`. |
| `ColRep.decGraph_fst` | `GIZK.decGraph_eq_of_sqrt` (derived from it); `ColMachines.nOf_ilayout` (layout form); the inline `(decGraph x).1 = nV x := rfl` of `SimulatorNumeric` | No equation for `(decGraph x).1` in `Encoding.lean`. **Request R-2:** publish `decGraph_fst` in `Encoding.lean`. |
| `ColRep.chView`, `chView_congr` | generalize `GI.PsOf`, `GI.PsOf_congr` (`SoundnessRepGI.lean`); `PsOf b = chView (fun i => [b i])` | The 3-colouring challenges are `edgeMsg e`, not bits. |
| `ColRep.exec_four_mul` | combines and generalizes `GI.exec_repViews`, `GI.repViews_snd`, `GI.repViews_fst` | The brief suggested `GI.exec_repViews`/`GI.repViews`. **But `GI.repViews` and `GI.Vs` have no published equations,** so following them would read their bodies (rule 10). `exec_four_mul` reads only `exec_succ`, `exec_zero`, `moverIsV_false`. **Request R-3:** publish `GI.repViews_succ` and `GI.Vs_succ`, or promote `ColRep.exec_four_mul` as the shared form. |
| `ColRep.blockRead`, `blockRead_eq`, `pushesUniform_blockRead`, `drop_take_ofFn_blockRead` | near-duplicate of `GIZK.tapeBlock`, `tapeBlock_bijective`, `pushesUniform_readBlocks`, `coinSlice_ofFn` (`GraphIsomorphismZK/Closeness.lean`); also `GI.blocksEquiv`, `GI.coinSlice_blocksEquiv` (`SoundnessRep.lean`) | `GIZK.tapeBlock` has no equation lemma. `coinSlice_ofFn` is about `GI.coinSlice`, which has no equation linking it to `colCoinSlice`. **Request R-4:** a `tapeBlock_eq` and a `coinSlice_eq` would make `blockRead` redundant. |
| `ColRep.statClose_edgeBlocks` | `GI.statClose_pi` (`SoundnessRep.lean`), `GIZK.statClose_pi`; its single-block step repeats the inline argument of private `colProtocol_sound` | It uses `OneWay.statClose_pi`, as the brief says. |
| `ColRep.mul_edgeCount_le` | the inline `hmx` computation of private `colProtocol_sound` | — |
| `ColRep.r3colTest*`, `R3COL_decidable` | analogues of `GI.risoTest`, `risoTest_iff`, `risoTest_poly`, `Riso_decidable` (the template) | Different relation. |
| private `wf_iff` | `ColMachines.encGraph_decGraph_eq_take` (used); the inline `hwf` of `ColMachines.verdictStr_poly` | That `hwf` tests `x = x.take (n²)` inside a proof and is not a lemma. |
| private `eq_of_xor_eq_false` | core `bne_eq_false_iff_eq` | Two lines. Replaceable if `^^` is unfolded to `!=`. |
| private `enc_iff`, `proper_iff`, `badVertex_poly`, `badEntry_poly`, `scanTest_poly` | none equivalent found; `checkStr_poly` (Parties) is the closest in style | — |
| private `colRep_outV`, `colRep_verifierRep_next_*`, `colRep_proverRep_next`, `colRep_outV_honest`, `colRep_accept_le`, `colRep_sound` | repeated analogues of private `colProtocol_outV`, `colVerifier_next_*_of`, `colProtocol_outV_honest`, `colProtocol_sound` (this file), and of `GI.giVerifierRep_next_*`, `GI.giRep_complete`, `GI.giRep_accept_le` | They are about different definitions. No proof text was copied, except the final completeness steps, which repeat `colProtocol_outV_honest`'s last four lines. |

### 4.2 Other notes

- **Generic lemmas from the shadow module.** I cite two public lemmas of the shadow module
  `ProtocolProofs.lean` that are generic and not about shadows: `ColProofs.two_le_of_edge` and
  `ColProofs.sampleEdgeIdx_ofFn_castLE`. I also cite `GIZK.pushesUniform_castLE`, which is generic
  in `B`. **Request R-5:** these belong in `Language.lean` / `Sampling.lean`. No private
  declaration of another file is cited (rule 11).
- **Not used by col-a.** The brief's two-parameter coin transport is col-b's item.

## 5. Rule-10 seal (`evidence/logs/seal.log`, sources in `evidence/seal/`)

### 5.1 How the seal was built

- **Scan (`SealScan.lean`).** I took every constant in the type and value of every new
  declaration, 95 in all, including their auxiliary and private declarations. I kept the
  TCSlib definitions of other modules, which gave 49. The scan finds no compiler-generated
  matcher of a foreign definition.
- **Sealed (35):**
  - `PolyExpr.normal`, `PolyTimeComputable`, `pairFstD`, `pairSndD`, `pairEncode`;
  - `ColMachines.colorVal`, `ColMachines.countTrue`;
  - `EncodingMachines.divNum`, `firstIdx`, `modNum`;
  - `HardcoreBit.PushesUniform`, `StatClose`, `Negligible`, `uprob`;
  - `L3COL`, `R3COL`, `ProperColoring`, `instDecidableProperColoring`, `ThreeColorable`;
  - `Protocol.ProverBounded`, `Protocol.outV`, `Protocol.withV`, `Strategy.coinLen`, `exec`,
    `moverIsV`;
  - `decColoring`, `decGraph`, `decGraphAt`, `encColoring`, `encGraph`;
  - `edgeIdxOfMsg`, `edgeMsg`, `edgeOf`, `sampleEdgeIdx`, `samplePerm3`.

  For the copy of the `Protocol.lean` code I also sealed the helper definitions `ColRep.chView`
  and `ColRep.blockRead`, which are foreign to `Protocol.lean`.
- **Unsealed.**
  - Reducible abbreviations and projections are notation and cannot be sealed: `Graph`,
    `edgeCount`, `Strategy.Coins`, `Protocol.ExecCoins`, and the projections `Protocol.P`, `.V`,
    `.rounds`, `.verifierFirst`, `Strategy.coins`, `.next`.
  - **`PolyExpr.eval` is left unsealed, per notes item 2.** The new code does not unfold it; it
    reads it only through `PolyExpr.eval_mul/const/var/normal`.
- **Owned definitions, unsealed.** The definitions of `Protocol.lean` itself are the owned
  file's, and the new code reads them by `show`/`rfl`: `colVerifierRep`, `colProverRep`, the
  fields of `colProtocolRep`, the coin polynomial of `colVerifierRep`, `colWellFormed` (via
  `of_decide_eq_true`), `challengesBefore`/`challengesUpTo`, and the private `colRep_challenge`.
  `colIterations` and `colCoinSlice` are read through `colIterations_eq` and `colCoinSlice_eq`.

### 5.2 Results

1. **Sealed copies.** Verbatim copies of both helper modules (`SealColAHelpers.lean`) and of the
   new `Protocol.lean` code with both filled proofs (`SealColAProtocol.lean`) **elaborate with no
   error and no warning (rc=0).**
2. **Controls (`SealColAControls.lean`).** C1 (destructure `R3COL`), C2 (`colorVal` by `rfl`) and
   C3 (`ColRep.chView` by `rfl`) **fail sealed (lines 18, 24, 27) and pass unsealed**, so the seal
   is active.
3. **Explicit readings (`RwIds.lean`).** `irreducible` does not block `unfold`, `simp [f]` or
   `rw [f]`, so I checked every identifier the new code passes to those tactics. All 80 named
   constants are theorems; the rest are local hypotheses or col-a's own private declarations
   (`badVertex`, `badEntry`, `scanTest`). No TCSlib, core or Mathlib definition occurs.
   A grep of the new lines for the sealed names inside `simp`/`rw`/`unfold`: 0 hits.

**Readings disclosed: none of a foreign definition.** The one reading behind a published lemma
is `decGraph_fst`: it relies on `GIZK.decGraph_eq_of_sqrt`, whose own proof is `rfl` on
`decGraph`. The published lemma that would replace it is R-2.

## 6. Final checks

### 6.1 Sweep (`evidence/logs/sweep.log`)

The sweep covers the two new helpers, then order-list lines 123–142 (`Protocol.lean` and every
module downstream of it). **22/22 modules exit 0, no error.** The only `sorry` is col-b's
`col_zk` (`Simulator.lean:778`). Tail:

```
## TCSlib/Cryptography/ZeroKnowledge/Encryption: … exit 0 maxrss 2620 MiB
## TCSlib/Cryptography/ZeroKnowledge: … exit 0 maxrss 2684 MiB
SWEEP DONE
```

### 6.2 Axiom prints (`evidence/logs/axioms.log`)

```
R3COL_witnessRelation          : [propext, Classical.choice, Quot.sound]
colRep_efficientProverProof    : [propext, Classical.choice, Quot.sound]
colRep_interactiveProof        : [propext, Classical.choice, Quot.sound]
col_zeroKnowledgeProof, zk_proof_of_levinReduction, zk_proof_of_owp_levinReduction,
exists_commitment_zk_proof_of_owp_levinReduction, zk_proof_of_witnessRelation(_of_owp),
zk_proof_of_mem_NP(_of_owp)    : [propext, sorryAx, Classical.choice, Quot.sound]
```

- **`sorryAx` comes only from col-b.** In every consumer it comes from `col_zk` alone
  (`SorrySrcColA.lean` lists each consumer's declarations whose value mentions `sorryAx`).
  That is col-b's still-open target at this base.
- **New public helpers.** Every new public `ColRep` lemma prints at most
  `[propext, Classical.choice, Quot.sound]`.

### 6.3 Lint (`evidence/logs/lint-before.log`, `lint-after.log`)

- **`style_lint.py`:**
  - before: `0 findings in 1 files` (`Protocol.lean`);
  - after: `1 findings in 3 files`, which is `Protocol.lean: 1346 lines (> 1000, must split)`.
    That is the approved size exception, as expected.
- **`campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge`:**
  - before: `9 FAIL, 26 WARN over 33 files`;
  - after: `11 FAIL, 27 WARN over 35 files`.
- **The added lines are exactly:**
  - two facade FAILs: `ThreeColoring.lean` does not import `…ThreeColoring.ColRepSound` or
    `…ThreeColoring.ColRepWitness`;
  - the size WARN of `Protocol.lean` (the same approved exception);
  - INFO lines for the new files.
- **Check-8 WARNs are unchanged** (`Protocol.lean` 3, `Simulator.lean` 17). The new public defs
  `r3colTest`, `chView` and `blockRead` all have their lemmas.
- No other FAIL in `ThreeColoring/`.

## 7. Diff scope and landing edit

- **Scope.** The diff touches only `ThreeColoring/Protocol.lean` and the two new helpers (3 files,
  930 insertions, 3 deletions).
- **Facade landing edit, for the maintainer.** In `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean`:
  - add `import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepWitness` and
    `import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound`;
  - add the `## Contents` lines:
    - `ColRepWitness` — the decider of `R_3COL`;
    - `ColRepSound` — generic lemmas for the `n|E|`-fold protocol.

  Neither unit owns that file, so I did not edit it.
- **Landing on #210's final head.** The series should apply cleanly: #210's `msgAt_eq` goes
  beside `msgAt` (line 103 at the base), away from every hunk of this diff.

## 8. Prerequisites (P1–P12) and escalations

- **Prerequisites.** All the col-a prerequisites I needed are present at `16a7d02d`:
  - P1 `R3COL_iff`;
  - P2 `ProperColoring_iff`;
  - P3 `getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one` (and the published
    `length_encColoring`);
  - P4 `Strategy.coinLen_eq`.

  The other published equations I used are `Protocol.outV_withV`, `Protocol.withV_self`,
  `exec_succ`, `exec_zero`, `PolyExpr.eval_*`, and `colProver_next_nil`/`_cons` (P10).
- **E-API:** none. **Statement escalations:** none. Both targets were provable as stated.

## 9. Environment (addendum)

1. **Preflight** (`preflight.log`):
   - `nproc` 4.
   - Memory: cgroup v1. `memory.limit_in_bytes` 14,337,302,528; in use
     `usage_in_bytes − total_cache + total_shmem = 537,587,712 − 510,181,376 + 0 = 27,406,336`;
     **headroom 13.33 GiB** (floor 4).
   - Disk: the clone and the scratch directory are on ext4 `/dev/vda` (not tmpfs), with
     **29.44 GiB free** (floor 12).
   - Result: pass.
2. **Toolchain.** `leanprover/lean4:v4.25.0` via elan, installed after the preflight, with
   `TAR_OPTIONS=--no-same-owner`. Disk re-check before the cache: 29.0 GiB free (floor 8).
3. **Cache.**
   - Store (`cache-store.log`): absent before the fetch, so there were 0 pre-existing archives.
   - Narrowed fetch (`cache-get.log`): **66 roots**, identical to `inputs/col-a/roots.txt`;
     "Attempting to download 2107 file(s)", "Decompressing 2107 file(s)",
     "Completed successfully!", exit 0, no failed download.
   - No new Mathlib roots: the helpers import only order-list modules.
4. **Packages** (`packages-check.log`): "RESULT: all present packages match the manifest".
   ABSENT: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean; no order-list module imports them.
   Zero-size oleans: 0.
5. **Probe** (`cache-probe.log`): `import Mathlib.Algebra.BigOperators.Field` elaborates, exit 0.
6. **Bootstrap** (`bootstrap.log`): I built the whole order-list prefix, lines 1–122 (through
   `ThreeColoring/ProtocolProofs`), in order, all exit 0. I then checked the helpers, then
   `Protocol.lean`, then the remaining lines 124–142 in the final sweep.
7. **Resources.**
   - One Lean process at a time, throughout. No `lake build`, no unfiltered `lake exe cache get`.
   - `/usr/bin/time` is not installed, so a `getrusage` wrapper logs each module's start and end
     time and its peak child RSS. The peak was **2,811 MiB** (`Protocol.lean`).
   - No shortage and no retry.
8. **Lint worktree.** The lint "before" ran on a detached worktree of the same clone at the base,
   with no Lean process and no `.lake`.
