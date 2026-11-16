# Gate 42 · Yao's protocol in the OT-hybrid model (`sc-yao`, U3, [PS10, Protocol 162.6, Theorem 163.7])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341) at
  `e9b03c437aca251846430ff23b40ee5ff3d3347a` (branch `land/pass-shelat-sc-yao`, tree
  `3a770d2979fc847e3948dc79ca42ba7db3f0b906`).
- **Records pin:** `f22e0f6798815b9263893e61928b4f16452f74ee` ("sc-yao review r1 final"). Every record this pack cites is
  read at the pin (the interim review at its own commit, and the rulings below at theirs). The pack's own files are filed
  by the maintainer after this pin.
- **Rulings after the pin:** records commit `67423db6c9d6448ae531b04f42c315585d00d502` (a descendant of the pin; records
  only, no Lean, lake, `audits` or `scripts` path changed) adds Seyoon's rulings of 2026-11-16 on SY-F01 to SY-F03
  (`fills/sc-yao/final-r1/rulings.md`), ledger row **DL-51** and the **DL-49 extension** in
  `briefs/pass-shelat-ch5-8/duplication-ledger.md` (and DW-4's scope in `deferred-work.md`). None of them changes #341.
  SY-F01 is confirmed; SY-F02 goes on the ledger, then is promoted (DL-51); SY-F03 puts both copies on the ledger, with
  promotion later (DL-49). Still open: SY-F05's remaining pair (ruling 10 below).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4`; its merge base is the old tip
  `f9fda8fe8d11fc68c233df2979a86d356ddfe1ab` (with #313, #318, #319, #323, #326, #332 and #333).
  - The fill was issued on `6ce4658db08a1dc2a03a149987197660db078011`, before sc-garble (#323) merged, under the
    proved-modulo rule: `yaoHybrid_simulators` cites sc-garble's frozen `yaoSeed_good_whp` and
    `sliceMultiMessageSecure_of_prfOut`. Both are proved on `f9fda8fe`, so on the landing head the targets use only the
    standard axioms.
  - Since `f9fda8fe` the branch gained #327 (seq-zk, `7d532e20`) and #324 (sc-compose,
    `201bf57a941131d1737295089ffd7477e1d7f7b9`) and records. Neither touches the PR's 70 paths, and between `201bf57a`
    and the pin no Lean, lake, `audits` or `scripts` path changes (`pack-checks/series.txt`).
  - `pr.diff.txt` is `git diff f9fda8fe..e9b03c43`, which equals the three-dot `git diff f22e0f67...e9b03c43` (GitHub's
    view) byte for byte: 70 paths, 15813 insertions, 67 deletions.
  - **Not an audit item.** The integration build of the head on the current tip (with #327 and #324, `201bf57a`) is a
    maintainer merge condition and is running separately. `git merge-tree` of the head with `201bf57a` and with the pin
    is clean, no path is shared, and no module of the PR's import closure changed between `f9fda8fe` and `201bf57a`
    (`pack-checks/mergetrees.txt`).
- **Commits:** 12, all committed by Claude and SSH-signed with the key that signs the records pin; each signature
  verifies, and a one-byte tamper control fails (`pack-checks/series.txt`).
  - The worker's 8 commits (job `sc-yao`: a lead and 3 sub-agents on Seyoon's Mac under the host addendum, ruling SY-6;
    author Seyoon Ragavan), delivered unsigned with a `COMMITS.tsv` signing column `none`. `git am` at the issue base
    reproduces all 8 hashes (`6ce4658d..6e7ef601`). They were cherry-picked onto `f9fda8fe`, author kept:
    `git range-diff` is 5/8 `=`; commit 1 lost the `DAGCircuit.isFaninTwo_iff` hunk, which the merge absorbed because it
    is byte-identical to #323's, and commits 4 and 7 differ only in the `## Main results` bullet resolution.
  - Landing edits: **LE-bullet** `13690d2e`, **LE-reuse** `81d526d8` (SY-F05), **LE-title** `bd7832d7` (optional) and
    **LE-doc** `e9b03c43` (the head; SY-F04, a separate job, fast-forwarded).
- **Scope:** a **proof audit** of two admitted, frozen statements of `SecureComputation/Yao.lean`, and of what consumes
  them:

  | Target | Line at the head | Source |
  |---|---|---|
  | `yaoHybrid_polyTime` | 863 | [PS10, Definition 155.1] (the efficiency clause, ruling of 2026-11-05), for Protocol 162.6 in the OT-hybrid model |
  | `yaoHybrid_simulators` | 1021 | [PS10, Theorem 163.7] in the OT-hybrid model; the one-active-key simulator of [LP09] |
  | `yaoHybrid_hbcSecure` (proved at the base from the two, unchanged) | 1168 | Theorem 163.7 in the OT-hybrid model |

  Both targets passed the prong statement phase and Gate 06 and are frozen; the brief quotes them. `yaoHybrid_hbcSecure`
  consumes both, and `YaoReal.lean`'s `yaoProtocol_hbcSecure` consumes it.
- **Brief:** `fills/sc-yao/issued-r1/brief.md` (SHA-256 `4785f593…`) with **rulings SY-1 to SY-6** (`ruling-SY.md`, which
  overrides the brief where they differ): one hub import line (SY-1), the `Yao.lean` cap waived to 1,200 lines (SY-2),
  the pre-approved SY-3 readers, the SY-4 hosts as public generic contracts, disclosed general copies of unmerged
  deliveries allowed (SY-5), and the multi-agent worker (SY-6). Five checkpoints; the stricter `Yao.lean` rule; the
  visibility rule (helpers state everything generically; the bodies instantiate them); Gate 27's hand-off obligations;
  the binding duplication rule with an `## Overlap and reuse` section; Rule 10 with the projection-coercion ruling and
  seals with `PolyExpr.eval` both excluded and sealed; the docstring and sketch rules; the G26-N1 error count; the
  evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`. The PR touches 70 files: 2
modified and 68 new (15813 insertions, 67 deletions). Lines are tip → head (`source-head.json`; every line at most 100
characters).

| File | Status | Lines |
|---|---|---:|
| `Yao.lean` | owned regions only (the stricter rule), shared with sc-garble | 970 → 1179 (942 at the issue base; SY-2 cap 1,200) |
| `TCSlib/Complexity/CircuitComplexity/Uniform.lean` | frozen, the seven SY-3 readers | 281 → 307 |
| `Yao/HybridProof.lean` | the hub (new; imports exactly its 67 children; `## Contents`) | 158 |
| `Yao/HybridProof/*.lean` | 67 helpers, new | 15353 together; largest `RowFromCoins` 649 |
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | frozen, **unchanged against the tip** | 730 |

`Yao/HybridProof.lean` is the only file directly under `Yao/`; `Yao.lean` imports only the hub, and the facade needs no
edit (#305).

**The proof** (REPORT § *Generic interface and concrete proof assembly*, § *Gate 27 hand-off*; the targets' sketches
were rewritten to describe the delivered proof, the statement prose is unchanged):
1. **`yaoHybrid_polyTime`** (128-line body). `HybridProtocol.PolyTime` (`polyTime_iff`) asks for efficient `main`
   strategies, polynomial-time call inputs and a message bound for any answers.
   - *Alice:* `AliceProgram.message_poly` computes the encoded `garbledTable (nestedSpecial E₁ E₂ n)` vector, her
     selected input keys and the decoding pairs, from `⟨1^n, ⟨x, r⟩⟩`, through the circuit-description decoder (host
     H-SY-decoder, `DescriptionDecoder.decodeDescription_host`, and `ChunkScanner`), `Y.uniform` with
     `encodeCircuit_eq` and `encodeMsgs_eq_encWords`, the seed readers (`keyAt_yaoSeed`, `yaoSeed_snd_fst`,
     `yaoSeed_snd_snd`, `readBits_apply`), fan-in two by `DAGCircuit.isFaninTwo_iff`, and `polyTimeComputable_spEncFun`;
     the noncomputable `Finset.univ.toList` row order is handled for an arbitrary constant enumeration.
   - *Bob:* `BobProgram.output_poly` runs `runWith`/`evalGate` of `nestedSpecial` on tables decoded from an arbitrary
     message (host H-SY-eval, `RunWithHost.exists_machine`, via `GarbledRun.garbledRunWith_poly`), then the output
     decoding.
   - Every history, malformed ones included, goes through the GI efficiency layer (`GI.efficient_of_polyTime`);
     `CallEquations.inputA_eq`/`inputB_eq` give the call inputs through `finProdFinEquiv`; the ciphertext truncation
     bounds give a message bound independent of the answers (`twoMove_message_length_le`).
2. **`yaoHybrid_simulators`** (124-line body). `S_A = AliceSimulator.simulator (yaoCoins Y)` (the copying simulator) and
   `S_B` from `FakeSimulatorFactory.exists_simulator` (the fake garbling with active keys, the real enumeration and
   shifts, the prescribed output), both uniform and chosen before `D`; one negligible `ε` after `D`, before `n`, `x`, `y`.
   - *Statistical part:* the bad event is the frozen `yaoSeed_good_whp` (with `hGE₁`, `hGE₂`, `hG₁`, `hG₂`); off it,
     `yaoHybrid_correct` gives both outputs; `AliceStatistical.distAdv_real_ideal_le` and
     `BobStatistical.statClose_real_output_switch`, with the switch lemmas of `StatisticalSwitch` (SY-F02), which
     `AliceSimulator` and `SimulationBound` use.
   - *Bob's computational part:* `BobStageZero.acceptProb_eq_stage0` (the real view is stage zero up to an exact
     permutation of the coin tape: the point-and-permute relabelling, `CoinRelabel`, `CoinSeedRelabel`,
     `RelabelGarbling`); a gate hybrid with two substeps per gate (`GateHybrids`, `GateHybridMessage`), each reduced to
     the frozen B1 statement `sliceMultiMessageSecure_of_prfOut hG₁₂` with slices `(0, n)` and `(2n, 4n + 2)`
     (`SelectedSlices`) and `7n + 2 ≤ L.eval n` for `L = .add (.add .var .var) (.add .var innerLen)`; a non-uniform
     reduction whose advice is the worst input, the stage and the whole baseline tape (`SelectedStepSecurity`,
     `SliceReduction.reconstruction_negligible`, `SelectedAdviceBounds`); polynomial-time reconstruction
     (`SliceReconstruction`); the chain over at most `2 S(n)` stages (`GateHybridChain`, `GateHybridSecurity`); and the
     last stage equal to `S_B`'s ideal view (`SamplerEndpoints.acceptProb_end_eq_ideal`).
   - *Total:* `simulators_of_output_switch` gives `δ(n) + 2 S(n) · |μ_B1(n)|` for both sides.
3. **`yaoHybrid_hbcSecure`** is unchanged; it now uses only the standard axioms (review § *Axioms*).

**Gate 27's hand-off obligations** (brief § *Proof route*; REPORT § *Gate 27 hand-off*, a declaration map): (1) the gate
and row sub-hybrids; (2) the enumeration of all occurrences of the selected key, with padding (`GateOccurrences`);
(3) the no-dependence argument (`GateOccurrences.selected_wire_lt`, `SelectedFields.stageBit_plaintext_ne_*`,
`SelectedStep.plaintext_ne`, `outs_sink`); (4) the exact coin and view sampler identities (`SelectedTables.*_reconstruct`);
(5) polynomial-time reconstruction (`SliceReconstruction.row_poly`, `tables_poly`, `rebuild_poly`).

**The SY-3 readers** (`Uniform.lean`, pure insertions, each `theorem … := rfl` with a formula docstring and no
attribute, directly after its `def`): `encodeList_nil`, `encodeList_cons`, `GateKind.encode_and`, `encode_or`,
`encode_not`, `DAGGate.encode_eq`, `DAGCircuit.encode_parts`. The worker also delivered `DAGCircuit.isFaninTwo_iff`
byte-identical to sc-garble's approved reader (SG-F01); at landing it coincided with the tip's copy, so `DAGCircuit.lean`
is unchanged.

## Rulings and records in force

1. **SY-1 to SY-6 (Seyoon, 2026-11-15, before dispatch)**, `ruling-SY.md`. In particular SY-2 (`Yao.lean` at most 1,200
   lines, recorded as a size exception) and SY-5 (disclosed general re-derivations of lemmas that existed only in the
   unmerged sc-garble, #318 and sc-compose deliveries are allowed and re-pointed proof-only after landing; copying a
   merged public lemma is still a finding).
2. **SG-F01 (Seyoon confirmed, 2026-11-15):** `DAGCircuit.isFaninTwo_iff`, `Iff.rfl`. It is on the tip from #323; the PR
   does not change `DAGCircuit.lean`.
3. **SY-F01, confirmed (Seyoon, 2026-11-16; `rulings.md` at `67423db6`):** the four helper imports outside the issued
   order, approved in the worker's session (`worker/final/evidence/scope-request/`, quoted in REPORT § *Scope
   requests*): `ZeroKnowledge/ThreeColoring/Machines`, `PrivateKey/FromPRF/ReductionMachine`,
   `PrivateKey/FromPRF/HybridLemmas` (a brief defect: its lemma was a listed interface) and `Asymptotic/BlockEncryptor`.
4. **SY-F02 and SY-F03, ruled (Seyoon, 2026-11-16; `rulings.md` at `67423db6`):**
   - SY-F02: ledger, then promote. **DL-51:** `StatisticalSwitch.statClose_of_eq_off` and `distAdv_le_of_eq_off`
     against `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`); in the cleanup `statClose_of_uprob_ne` moves to
     `Asymptotic/Sampling` and both users are re-pointed.
   - SY-F03: ledger both, promote later. **DL-49 extended** with sc-yao's `YaoHybridProof.encodeMsgs_eq_encWords`
     (`Yao/HybridProof/Lengths.lean:83`) and #327's `SequentialZK.encodeMsgs_eq_encWords`
     (`Composability/SequentialZK/Normalization.lean:40`), as the post-merge addendum proposed; one copy goes to a
     common home in the cleanup.
5. **The duplication ledger** at `67423db6`: DL-46 (the `encodeList_eq_flatMap` copies), DL-47 (the getD/headD-of-
   `List.ofFn` class, which the brief let helpers use inline through Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn`
   but not copy as a lemma), DL-49 (sc-compose's restatements, among them the `encodeMsgs` relatives, extended by SY-F03)
   and DL-51 (SY-F02). **Not a finding:** any item these rows list, provided the row matches the code.
6. **Rule 10:** `PolyExpr.eval` is notation (Q1, the user, 2026-11-07): seal **A** is canonical, seal B is run and its
   new failures attributed from the raw logs (Gate 31). A `CoeFun`/`Coe` instance whose body is a structure projection
   is notation (Seyoon, 2026-11-14); `FinDist.instCoeFunForallReal` is the only one in the environment, so **coe-A is
   the canonical variant** and the strict variant is run and attributed. Reducible abbreviations are notation
   (2026-10-26). Inside `Yao.lean` its own definitions may be read directly (`rfl`, `show`); each helper is foreign to
   the others.
7. **The facade-completeness lint fix, #305.** The baselines are 92 FAIL / 101 WARN (Cryptography) and 25 / 390
   (Complexity) at the tip.
8. **The host addendum** (`fills/codex-host-2026-11-15/host-addendum.md`, §4 for sub-agents): the review checked the
   3-slot cap from `slots.log`. The worker's shared-wrapper execution authorization
   (`scope-request/execution-authorization.md`) is information, not a finding.
9. **DW-1** (`deferred-work.md`): `HBCSecure` allows non-uniform simulators as [PS10, Definition 155.1] does; making the
   Yao simulators literally `Uniform` is deferred. SY-F11 notes that `S_A` and `S_B` are uniform already. DW-4 (the
   duplication cleanup) now spans DL-38 to DL-51 (`67423db6`).
10. **Still open: SY-F05's remaining pair.** `OTAnswerWords.length_answersB` and `answersA_nil` against #324's now
   public `HybridProtocol.length_answersB` and `length_answersA` (`ComposeSecurity/Lengths.lean:60`, `:52`). The proposed
   disposition is a ledger row, with a re-point after #341 merges; it awaits Seyoon's acknowledgement (`rulings.md`).
   **Grade that disposition.**

## What is frozen

- **The targets' statements** (headers, `include hGE₁ hGE₂ in`, and the statement prose before each `**Proof sketch.**`,
  including the simulators' *Deviation: the joint PRF hypothesis* paragraph) and **every other declaration of
  `Yao.lean`**, private ones included, with every definition body, docstring, `variable`, `section`, `open`,
  `set_option`, import and comment; sc-garble's `yaoSeed_good_whp` (proved on the tip) in full.
- **`Yao.lean` may change in exactly six regions:** the hub import after line 9, the `## Main results` bullet, the two
  sketches and the two bodies; plus **LE-title**'s title line (the brief left "(statement phase)" for the maintainer's
  landing edit). No declaration may be added to `Yao.lean`.
- **`Uniform.lean`** apart from the seven SY-3 readers; **`DAGCircuit.lean`** entirely; every other file
  (`Garbling*`, `SpecialEncryption*`, `Hybrid`, `Defs`, `YaoReal`, `ObliviousTransfer*`, `Compose*`, `Pseudorandom/*`,
  `Encryption/*`, `Games/*`, `ZeroKnowledge/*`, the circuit and complexity libraries).
- **The landing edits:** LE-bullet (one bullet), LE-reuse (proofs only), LE-title (one line), LE-doc (comments only).

## Questions for the audit

**1. Correctness against the frozen statements and [PS10, Protocol 162.6, Theorem 163.7]**
- **`yaoHybrid_polyTime`:** does the body establish all four clauses of `polyTime_iff` for `yaoHybrid Y E₁ E₂`, for
  **every** history (malformed messages, private inputs and tapes; `x.length` against `n`)? Are the two hosts
  (H-SY-decoder, H-SY-eval) correct on every canonical description and polynomial on every string, and is the constant
  enumeration of `Finset.univ.toList` handled soundly? Is the message bound independent of the answers? Do the call-input
  machines read the right coin blocks and choice bits through `finProdFinEquiv`?
- **`yaoHybrid_simulators`:** are `S_A` and `S_B` fixed before `D`, and `ε` before `n`, `x`, `y`? Is Alice's side exactly
  the statistical switch off `yaoSeed_good_whp`'s bad event, and Bob's output switch exactly `yaoHybrid_correct` off it?
  Is the stage-zero identity an exact bijection of Alice's coins (keys `k_w^b ↦ k_w^{b ⊕ v_w}`, rows `a ↦ a ⊕ v_args`,
  shifts `λ_i ↦ λ_i ⊕ v_args`), and is the last stage exactly `S_B`'s ideal view?
- **The B1 embedding:** is every row under the inactive key `ι_u`, in every gate that reads `u`, a challenge slot with
  the right shape (`(0, n)` for a second or only argument, `(2n, 4n + 2)` for a first argument), padded to `q(n) + 1`
  slots with equal messages where nothing changes? Is the interface non-adaptive (every challenge message fixed before
  any challenge ciphertext)? Is the advice (worst input, stage, baseline tape) polynomial (`SelectedAdviceBounds`), the
  reconstruction polynomial-time on every string, and the sampler identity exact? Are **Gate 27's obligations (1)–(5)**
  met by the declarations the REPORT maps them to?
- **The total:** is `δ(n) + 2 S(n) · |μ_B1(n)|` the right bound, negligible by the published polynomial-times-negligible
  theorem, with one `μ` for all neighbouring stages?
- **Against the source:** PS10's proof of Theorem 163.7 (book pages 163–164, `sources.zip` `PS10/`) simulates Bob with a
  garbled circuit that always outputs `f(x, y)` and asserts a hybrid argument; the formal proof runs in the OT-hybrid
  model (Q-5, 2026-11-05; OT composition is sc-compose's `hbcSecure_compose`) with the one-active-key simulator of
  [LP09]. Is that a faithful formalization of Protocol 162.6 and Theorem 163.7 in that model, and are the deviations
  stated?
- **Edge cases** (brief § *Edge cases*): `n = 0`; `inA`, `inB` or `outLen` zero; `|gates| = 0`; constant, one- and
  two-argument gates; output vertices that are inputs or coincide; a wire read in both argument positions (both slice
  shapes under one key); wires read by no gate and unread coin blocks; accidental equal key values.

**2. Frozen-statement integrity**
- **`Yao.lean`:** do only the six approved regions and LE-title's title line change? The pack re-check
  (`pack-checks/frozen.txt`) masks those seven spans at the tip and the head and finds the rest byte-identical (0
  violations, 0 rule breaks), every unmasked hunk inside one region on both sides, the 76 declarations in the same order
  with byte-identical headers and definitions, the two targets' statement prose byte-identical, `yaoSeed_good_whp`
  unchanged, and one added import. Its six controls (a one-character header, an extra frozen line, a second import, a
  declaration smuggled into a body, an edit inside a sketch, a doubled space in statement prose) each give the expected
  count. The review's own check (`frozen_sy.py`, `landing/frozen-check.txt` = `landing/yao-scope-vs-tip-final.txt`)
  masks only the six regions, so it reports exactly **one** violation, the LE-title line; its scope check at the issue
  base, with six controls, is `scope/yao-check.txt` and `scope/controls-results.txt`.
- **`Uniform.lean`:** is the change exactly the seven SY-3 `rfl` readers, pure insertions, each with a formula docstring,
  no attribute, directly after its `def`, and does removing them restore the tip byte for byte (`frozen.txt`,
  `landing/uniform-check.txt`)? Is each reader needed under the seal (`rule10/reader-control-recount.txt`: 8 unsealed
  `rfl` pass, 8 sealed `rfl` fail once, 8 sealed readers pass, `isFaninTwo_iff` included)?
- **`DAGCircuit.lean`:** is it unchanged against the tip, and is the delivered `isFaninTwo_iff` block byte-identical to
  the tip's (`frozen.txt`: the delivery's copy = the issue base plus exactly that block)?
- Is every other changed path a new file under the hub, and is nothing else in a frozen file changed?

**3. The landing edits** (`pack-checks/lecheck.txt`; review evidence `landing/`, `phase2/ledoc/docstrip.txt`)
- **LE-bullet `13690d2e`:** one bullet, "(proved modulo sc-garble)" → "(proved)".
- **LE-reuse `81d526d8` (SY-F05):** `CoinSeedRelabel.assignmentFold_lt_four` and `assignmentFold_injective` now read the
  public `GarblingProbability.assignmentFold_small` (`.1 a`, `.2`); headers byte-identical, no import change, two
  docstrings rewritten. Is it proof-only?
- **LE-title `bd7832d7` (optional):** the title line only.
- **LE-doc `e9b03c43` (SY-F04):** 64 helper files; each is identical after stripping comments (the re-check strips line,
  block and doc comments; 64/64; two controls); `Yao.lean`, `Uniform.lean` and `DAGCircuit.lean` untouched; widths at
  most 100. Do the new formula docstrings state the declarations' formulas correctly, in Lean argument order? (The LE-doc
  job checked one assumption, the argument order of `FakeSimulator.Data.make`, against `#check`;
  `phase2/axioms-summary.txt` shows it.)

**4. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the REPORT's `## Overlap and reuse` (line 266), the ledger rows of ruling 5 and SY-5's disclosed copies? **An
  undisclosed duplicate of a public lemma is a major.** The recent majors of this class: G23-01, G24-01, prf-mac F-01,
  learning (`uprob_eq_point`), G29-01, G29-02, sc-ot F-01, G34-01.
- **Grade SY-F01 to SY-F12** (the review's table), given the rulings (rulings 3, 4 and 10):
  - **SY-F01** (confirmed): the four helper imports; is each needed, and is the closure growth
    (`layout/external-imports.txt`) acceptable?
  - **SY-F02** (ruled: DL-51, then promote): `StatisticalSwitch.statClose_of_eq_off` and `distAdv_le_of_eq_off` against
    the public `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`), undisclosed (the REPORT never names it);
    `pack-checks/dupscan.txt` shows both texts, and `context/` holds `DDH.lean`.
  - **SY-F03** (ruled: DL-49 extended, promote later): `YaoHybridProof.encodeMsgs_eq_encWords` (`Lengths.lean:83`)
    against `ColMachines.encodeMsgs_eq_flatMap` (`ThreeColoring/Machines.lean:912`, copies in `SimulatorNumeric.lean:503`
    and sc-compose's `ComposeSecurity/Machines.lean:150`) with `BinArith.encWords_def`, undisclosed. **The post-merge
    addendum** extends it to #327's public `SequentialZK.encodeMsgs_eq_encWords` (`Composability/SequentialZK/
    Normalization.lean:40`), unledgered at the pin and now in the DL-49 extension. The pack re-check finds the two
    equal from the keyword to the end of the proof after renaming bound variables (`L`, `w` ↔ `h`, `m`), with different
    docstrings: the same statement and proof, which the addendum and the DL-49 extension call verbatim copies.
- **Check the ledger rows against the code.** Do DL-51 and the DL-49 extension (at `67423db6`) name the right
  declarations, files and lines, and describe the relation correctly? `pack-checks/dupscan.txt` (§ *ledger rows against
  the code*) finds every cited declaration at its cited line (`Lengths.lean:83`, `Normalization.lean:40`,
  `DDH.lean:145`, `ThreeColoring/Machines.lean:912`; `StatisticalSwitch.lean:46` and `:68`, which DL-51 cites by file).
  Is any further undisclosed duplicate outside these rows?
- **Grade the SY-F05 remainder's proposed disposition** (ruling 10): is a ledger row with a re-point after #341 merges
  right, or should the pair be re-pointed onto #324's public lemmas before merge?
- The fixed and informational ones: SY-F04 (LE-doc), SY-F05 (LE-reuse; the remaining `OTAnswerWords` pair is ruling 10),
  SY-F06 (near-relatives: `ChunkScanner.scan` vs `Complexity.transduce`, `RunWithHost.acc` vs `StateLoop.MajLoop.acc`,
  `SliceReduction.distAdv_fibers_le` vs `OT.statClose_prod_of_forall`, `distAdv_chain_le` vs `abs_sub_le_sum_hybrids`),
  SY-F08 (inline getD/`List.ofFn` rewrites; the review counts 14 in 10 helpers; a line count finds
  `List.getD_eq_getElem` on 29 code lines in 16 helpers, 11 followed within three lines by `List.getElem_ofFn`, and
  **no** new theorem of the DL-47 shape, `dupscan.txt`). Are these dispositions right, and is any of them in fact a
  major?
- **Name interaction with #327/#324** (`pack-checks/names.txt`): no full-name clash with any TCSlib declaration at
  `201bf57a`; four short names occur on both sides in different namespaces: the addendum's three
  (`encodeMsgs_eq_encWords`, `exists_simulator`, `length_answersB`) and `outV_eq` (`TwoMoveViews.outV_eq` against #327's
  `Composability.PaddedVerifierSpec.outV_eq`; `Protocol.outV_eq` already existed at the tip). No sc-yao private name
  clashes, and no public helper shadows one of `Yao.lean`'s four private names.
- The review's own searches: `dup/` (namespace-resolved name scan of 764 new names; normalized-statement matches against
  21,045 tip theorem headers: 0 exact, 5 loose) and the interim review § *Duplication*.

**5. Rule 10**
- **Seals** (the review's own, whole-file over the full TCSlib import closure, `-DmaxErrors=0`, both error forms,
  install and EOF records; recounted from the raw logs in `pack-checks/rule10.txt`):
  - `Yao.lean`: **seal A 0** in both variants (3046/3047 requests); **seal B 24** in both, in 9 declarations, against 15
    in 8 at the tip (sc-garble's review seal of the same `Yao.lean`, with 1985 requests over the smaller closure without
    the hub; `rule10.txt`). The 9 new errors are
    `yaoHybrid_polyTime` 2 and `yaoHybrid_simulators` 7; the review read each and attributes all to `PolyExpr.eval`
    index or type conversions or cascades from them (`phase2/yao-B-attribution.txt`; the worker's
    `subagents/final-seal-attribution/`). `pack-checks/rule10-errors.txt` lists every error with its message and
    enclosing declaration. Is that attribution right, and is none a foreign-definition unfold?
  - `Uniform.lean`: **4** errors in every variant, in `DAGCircuit.length_encode_le_of_isFaninTwo` and
    `IsPUniform.isPolySize`; the tip's `Uniform.lean` sealed with the same 135 requests gives the same 4 in the same 2
    declarations (inherited; the readers pass). `DAGCircuit.lean`: 0 requests, 0 errors.
  - **Helpers: coe-A 68/68** (the hub and 67 children) with 0 errors; the three other variants sampled on five helpers
    (`CoinSeedRelabel` after LE-reuse, `Lengths` with its `nestedSpecial` match reduction, `Decryption`,
    `SliceReduction`, `GarbledRun`): 15/15 with 0 errors. The worker's own 272 helper seals (68 × 4 variants) have 0
    errors (`rule10/delivered-seal-recount.txt`). Is the sample adequate given the delivered 272?
- **Paired controls** (`mkctl_sy.py`; rows `PolyExpr.eval`, `DAGCircuit.IsFaninTwo`, the four SY-3 encodings, `spEncStr`,
  `Good`, the `FinDist` coercion, and the helper definitions `ChunkScanner.scan`, `RunWithHost.acc`,
  `CoinRelabel.keyRelabel`, `SelectedRows.offset`): coe 30 probes ALL_OK, 83 sealed negatives each failing exactly once,
  15 unsealed probes passing; strict 34 probes, 100/100 sealed negatives failing once, 17/17 unsealed passing, the only
  other failures `ctlCoeReader` in the 17 sealed probes (the harness effect of sc-ot F-09 and sc-garble).
- **Explicit-unfold scan** (Phase 1, `rule10/unfoldscan.txt`): 1512 tactic references, 28 short-name candidates, all local
  `let`/`have` names: **0 foreign**. The worker's scan and its resolution are under `worker/final/evidence/unfold/`.
  Does any proof read a foreign definition other than through a published reader, in particular `garbledTable`,
  `evalGate`, `Good`, `nestedSpecial`, `spEncStr`/`spDecStr`, `sliceEnc`, `sliceMultiEncDist`, the samplers,
  `Strategy.Efficient`, `View.encode`, `IsFaninTwo` and the circuit encodings?

**6. The rules and the evidence**
- **Docstrings:** does every new public declaration state its formula in Lean argument order, with a source tag where it
  comes from the source? The re-check (`pack-checks/docs.txt`) finds docstrings on all 739 new public declarations (the
  three attribute-placement cases included). The review's pre-LE-doc audits are `docs/docaudit.tsv`,
  `docs/docaudit2.tsv` and `docs/docclass.txt`.
- **Sketches:** every proof of 15 lines or more carries a `**Proof sketch.**` (the re-check: 64 new theorems, 0 without;
  the review's `docs/sketchaudit.txt` lists 4 long `rfl` statements as false positives). SY-F09: six proofs of 40 lines
  or more have no step comments, among them the 128-line `yaoHybrid_polyTime` body (`docs/stepcomments.txt`); graded
  info by the review. Do the two targets' sketches describe the delivered proofs?
- **Sources (no fabricated tags):** the tags are [PS10] (68 files), [LP09] (10), [BMR90] (4), [AB09] (4), [Gol04] (2) and
  [Gar26] (2) (`pack-checks/sources.txt`). There is no curated PS10 chapter-6 transcription in
  `blueprint/src/references/` at the pin (chapters 2–4 and the appendix only), so `sources.zip` `PS10/` gives §6.2 from
  the PDF at the pin (pages and text); every numbered PS10 locator used (Definition 155.1, Algorithm 157.2,
  Protocol 162.6, Theorem 163.7, §6.2.1, §6.2.3) is found there, and "Claim 157.a", "Construction 158.a", "Claim 159.a"
  are the inventory's labels for unnumbered text (`inventory-ch5-8.md`), as elsewhere in the library. [LP09], [BMR90],
  [Gol04] and [Gar26] have no transcription at the pin. Two file-level gaps found by the re-check, not recorded by the
  review: `ChunkScanner.lean` cites [AB09, §6.2] but its `## References` has no [AB09] entry, and
  `GarblingProgram.lean` cites [BMR90] but its `## References` lists only [PS10]. Is any tag or locator fabricated or
  wrong?
- **Evidence completeness** (G20-01): the delivery's `SHA256SUMS` (7597 rows) and `evidence/SHA256SUMS` (7515) verify
  against every blob of the final delivery, with exact path sets (`pack-checks/manifests.txt`); the review's ZIP has
  1511 entries = its 1510 manifest rows plus `SHA256SUMS`, all verified, its records copy equal. Is any evidence the
  claims need missing?

**7. The merge interaction (not an audit item)**
- `git merge-tree --write-tree` of the head with the pin, with `201bf57a` and with each open PR on the records branch
  (#331, #338, #339, #340) is clean and shares no path (`pack-checks/mergetrees.txt`). 145 modules are downstream of the
  PR at the head (75 outside it).
- **Pending merge condition.** The integration build of the head merged with the current tip (#327 and #324,
  `201bf57a`) is running separately; the maintainer runs it, and with #324's `hbcSecure_compose` proved,
  `yaoProtocol_hbcSecure` is expected to use only the standard axioms. Treat it as a condition on the merge. What you
  can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SY-F01** confirmed; **SY-F02** DL-51; **SY-F03** DL-49 extended (`67423db6`). **SY-F04** fixed by LE-doc;
  **SY-F05** fixed by LE-reuse (the remaining `OTAnswerWords` pair: ruling 10, open); **SY-F06** ledger note;
  **SY-F07** none (as SG-F07); **SY-F08** the DL-47 cleanup may re-point them; **SY-F09** cleanup (also the
  unnecessary `simpa` warning at `BobIO:211`); **SY-F10** the SY-4 host and promotion requests (H-SY-decoder,
  H-SY-eval, draft registry rows in REPORT § *Hosts*), a maintainer decision at the gate; **SY-F11** a note for DW-1;
  **SY-F12** the size exception (1179 ≤ 1,200, the lint's only new WARN).
- **The worker was Codex with three sub-agents** (SY-6); REPORT § *Contributions and ownership* records who proved what.
  The worker commits carry Seyoon's authorship.
- **The review's evidence ZIP is not copied into `verification.zip`** (19 MB): a pointer gives its committed path,
  size and SHA-256 at the pin, and every entry this pack cites is copied, each checked against the manifest. The ZIP's
  `landing/series/0009`–`0011` patch files are not copied (the commits themselves are on the PR branch).
- **The final review supersedes the interim review** (`9902d727`, "Phase 1 and landing prep"), which keeps the Phase 1
  detail the final review refers to (scope controls, layout, duplication, the delivered seal recount, the host log); it
  is in `verification.zip` (`records-history/`) and the bundle.
- **Counting differences:** the review counts admissions over the issued order plus the helpers (23 at the tip → 21 at
  the head); the re-check counts every TCSlib declaration with a `sorry` outside comments (550 → 548) and finds exactly
  the two targets removed and none added (`pack-checks/sorries.txt`). The review speaks of "eight SY-3 readers" for the
  delivery (`isFaninTwo_iff` and the seven in `Uniform.lean`); the PR adds seven.
- The PR description abbreviates `Complexity/CircuitComplexity/Uniform.lean` as `Circuits/Uniform.lean`.

## Also check

**Axioms** (review § *Axioms*; `landing/census-head.log` = `phase2/probe-runs/mods/ScYaoProbe_AxiomsLand.log`,
`landing/axioms-summary.txt`; built on `f9fda8fe`, before #324 merged):
- `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure` and `yaoSeed_good_whp` print
  `[propext, Classical.choice, Quot.sound]`; their closures (9168, 20202, 20475, 17757 constants) have no direct
  `sorryAx` user. `yaoProtocol_hbcSecure` reached `sorryAx` only through `HybridProtocol.hbcSecure_compose` (#324, then
  unmerged); `otProtocol_*` are standard.
- The 1492 stored constants of the 71 owners are all standard; the SY-3 readers use no axioms. No user `@[simp]`: the
  only new simp-tagged constants are the generated `FakeSimulator.Data.mk.sizeOf_spec`/`injEq`; the three `@[simps …]`
  attributes all set `isSimp := false` (`pack-checks/docs.txt`).

**Admissions:** at the head no sc-yao module has a `sorry`; `Yao.lean` has none.

**Sizes and widths:** `Yao.lean` 1179 (SY-2), every other file at most 1000 lines, every line at most 100 characters
(`source-head.json`, `pack-checks/docs.txt`).

**Build** (review Phase 2, `dl-oleans-2`, one Lean process, `scripts/lean_check_tree.sh` only): incremental from the
tree's snapshot base `eff2dcd0` by import-closure keys, **718/718 modules rc 0, 0 `error:` and 0 `error(`**, no log
containing "error"; the whole downstream of `eff2dcd0..e9b03c43` (145 downstream of sc-yao), root `TCSlib`,
`audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks` (`landing/build-summary.txt`, `landing/root-checks.jsonl`).
Whole-order state check 1356/1356 OK (`landing/tree-check-head.txt`). sc-yao's modules: no `sorry`, one linter warning.
Restore: `dl-oleans-2` back to snapshot `457ba704…`.

**Lint** (line sets, tip → head): Cryptography 92/101 → 92/102, the only new line `Yao.lean`'s size WARN (SY-2);
Complexity 25/390, `Uniform.lean`'s check-8 WARN loses `encodeList`; no new FAIL (`lint/linediff-*.txt`).

## Evidence

- **`review.md`**, **`post-merge-addendum.md`** (records pin, `fills/sc-yao/final-r1/`): the maintainer's delivery
  review, verdict ACCEPT WITH LANDING EDITS (SY-F01–SY-F12), and the addendum after #327 and #324 merged.
  **`rulings.md`** (`fills/sc-yao/final-r1/`, records commit `67423db6`): Seyoon's rulings on SY-F01 to SY-F03.
- **`verification.zip`** (249 entries): every file the pack cites, as byte-identical originals except four generated
  ones. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence-SHA256SUMS` (the review ZIP's manifest, 1510 rows) and `review-evidence-POINTER.txt` (the ZIP at
    `fills/sc-yao/final-r1/review-evidence.zip`, 1511 entries, SHA-256
    `d3f7c3da0d081acd9275e798514fffd7b538c83787a109c11c59bab4e2c3b5a8`, not copied);
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `evidence/` (141): byte copies of the ZIP entries this pack cites (integrity, landing, scope, layout, docs, dup,
    rule10, lint, host, admissions, the Phase 2 build, axioms, seals, controls and restore summaries, the frozen files'
    seal logs and probe sources except `Yao.lean`'s 3.3 MB seal logs, and the review's tools);
  - `records/` (29): the issue package `fills/sc-yao/issued-r1/`, the final review and addendum, the decision log, the
    duplication ledger, deferred work, the inventory, policy, the secure-computation plan, the S3b design notes, the
    host addendum, Gate 27's findings and resolutions, Gate 36's findings and resolutions, ruling SG-1 and
    `sources.json`, at the pin; `records-history/9902d727/`: the interim review; `records-after-pin/67423db6/`: the
    rulings, the ledger and the deferred-work register at the rulings commit;
  - `worker/final/` (40): byte copies from exchange `47c38c479e4be52654cd2c055141dfb64be975c4` (`inbox/fills/sc-yao/`):
    REPORT, `SHA256SUMS`, `COMMITS.tsv`, the worklog, the scope requests, the final header check and its controls, the
    reader manifest, the clash scan, the unfold scan and its resolution, the final seal and audit summaries, the seal
    attribution sub-agent's report and excerpts, the common-contract disclosures and the source inventory;
  - `context/` (8): `Normalization.lean`, `ComposeSecurity/Lengths.lean`, `ComposeSecurity/Machines.lean`,
    `ComposeSecurity.lean`, `Candidates/DDH.lean`, `ThreeColoring/SimulatorNumeric.lean`, `ObliviousTransfer/ViewA.lean`
    and `YaoReal.lean`, at `201bf57a`;
  - `pr/`: the PR description and the REST fields the re-checks read;
  - `pack-checks/` (20): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `47c38c47`, under `inbox/fills/sc-yao/` (7598 files).
- **`landing/`:** byte copies of evidence-ZIP entries: `build-summary.txt` (= `phase2/build-head/summary.txt`),
  `root-checks.jsonl` (= `phase2/build-head/results.jsonl`), `tree-check-head.txt` (= `phase2/build-head/statecheck.txt`),
  `census-head.log` (= `phase2/probe-runs/mods/ScYaoProbe_AxiomsLand.log`), `axioms-summary.txt`
  (= `phase2/axioms-summary.txt`), `frozen-check.txt` (= `landing/yao-scope-vs-tip-final.txt`) and `uniform-check.txt`
  (= `landing/uniform-scope-vs-tip.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `47c38c47`.
- **`pr-description.md`:** the PR #341 description, read with the GitHub MCP tools on 2026-11-16 (`.body`, raw; equal
  byte for byte to the REST API's).
- **`pr.diff.txt`:** `git diff` from the merge base to the head (70 paths, 15813 insertions, 67 deletions).
- **`source-head.json`:** the head, base and pin, and the hashes, line counts and over-width counts of the 70 files.
- **`sources.zip`:** the source closure at the head of every changed module (`TCSlib/`, 262 files), and `PS10/`: [PS10]
  §6.2 (book pages 154–164) from `Pass–Shelat.pdf` at the pin, as the PDF pages and as `pdftotext` text, with a README
  locating each cited item.
- **The bundle** has the rulings and the ledger and deferred-work register at `67423db6` (in place of the pin's), and
  adds, as context at the head: `SecureComputation/Defs`, `Hybrid`, `Garbling`, `GarblingSpecial`,
  `SpecialEncryptionMulti` (B1) and `YaoReal`; and at `201bf57a`: #327's `SequentialZK/Normalization` and #324's
  `ComposeSecurity/Lengths`.

## Findings delivery

Return `gate42-sc-yao-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside the ledger rows and rulings in force,
  a fabricated source tag, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or citation.
- **note:** anything else.

Grade SY-F01 to SY-F12 in a separate table (agree, or regrade with the reason). Report the audited head and the counts by
severity. The gate closes at zero blockers and zero majors.
