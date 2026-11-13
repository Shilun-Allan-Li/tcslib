# Gate 19 · Simulation-based and indistinguishability-based non-malleability (Theorem 174.8)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #297](https://github.com/Shilun-Allan-Li/tcslib/pull/297) at
  `5da558b4d97aca00efd6dc396a1b0f3bffff268b` (branch `land/pass-shelat-nm-sim`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base `691f30f81af5c1c28d3d2c9abaadb88dc42bd4b0`. The fill was issued on
  `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` (the merge of #294). Every commit between the two, and every later base
  commit, touches records only.
- **Commits:** the worker's 3 commits (Claude fill `nm-sim`), then one maintainer commit of landing edits.
- **Scope:** this is a proof audit. Both statements passed Gate 06 (#232) and are unchanged.

## The targets

They live in `PublicKey/NonMalleability/Simulation.lean`, namespace
`TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.

```lean
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa
```

**Source.** [PS10, Theorem 174.8]: R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010.
The statement follows [PSV07]: SIM-NME′ at one message.

**Definitions.**
- `SimNMSecure` is Definition 173.7 as SIM-NME′. For every sampler `M`, adversary `A` and polynomials `q`, `r`,
  `sl`, there is a simulator `Sim` such that every distinguisher `D` has negligible advantage between `snmReal` and
  `snmIdeal`. The simulator runs through `simCodec` at query budget 1.
- `NMSecure` is Definition 172.6, proved equivalent to IND-CCA2 at Gate 18.

With both directions, `simNMSecure_cpa_iff_nmSecure_cpa` has no admission left, and neither does the
non-malleability chapter.

## The proof (check each step independently)

The 10 helper modules are under `NonMalleability/Simulation/`, namespace `…Composability.NMSim`.

The owned file's section *The experiments on T2's lengths* first reads both experiments as strings:
- `castImpl_snmImpl`;
- `snmView_realView`, `snmView_idealView`;
- `accept_snmReal_eq`, `accept_snmIdeal_eq`: `accept snmReal = NMSim.realAcc`, `accept snmIdeal = NMSim.idealAcc`.

### 1. SIM ⇒ IND, every attack (`nmSecure_of_simNMSecure`; bound `|adv_NM| ≤ 2·adv(D') + adv(D'')`)

**The objects.**
- **Sampler `halfSamp`.** The parameter is `⟨m₀, m₁⟩`. It outputs `m_β` for its one coin `β`, with `histLen = 0`.
- **SIM adversary.** It is T2's machine of `simHandler = copyHandler`, built on `NMCCA2.fwdHandler` (seed 0,
  `finCall = 0`). It forwards `Dec`, so it covers CCA1 and CCA2.
- **The simulator.** `Sim` comes from `h M A' (q·perCall + finCall) ℓ 0`.
- **D' = `tailDist`.** It uses `D`'s coins and advice. It outputs 0 if `m₀ = m₁`, and otherwise
  `[D(tails) = 1] == [m = m₁]`. The tails drop the `COPY` flag, so a copy reads as `nmDecrypt`'s ⊥
  (`nmOutput_eq_entryTails`).
- **D'' = `halfDist`.** It tests `m₀ ≠ m₁`.

**The two gaps.**
- **Real** (`real_gap`): `2·Pr[D'] − Pr[D''] = Pr[D(NM_1)] − Pr[D(NM_0)]`.
  - `accept_nmGame_eq_rImpl` and `castImpl_indImpl_abs` (the latter for every attack) reduce it to the hybrid
    oracle.
  - While `m₀ = m₁`, the two coins agree: `expect_runB_good`, an equal-until-bad coupling.
- **Ideal** (`ideal_gap`): `2·Pr[D'] = Pr[D'']` for every simulator. With `histLen = 0` the oracle ignores `β`
  (`histImpl_coins`).

`abs_le_of_gap` combines the two gaps.

### 2. IND ⇒ SIM under CPA (`simNMSecure_of_nmSecure_cpa`)

**Hybrids.** `H_b = hybAcc … b` runs `A` against `rImpl … b`. On the first challenge `a`, `rImpl` answers
`⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩`; under CPA, `Dec` answers ⊥. The real experiment is `H_false`
(`realAcc_eq_hybAcc`).

**Ideal = `H_true`** (`exists_simulator`).
- The simulator is T2's machine of `chalHandler (simParams …)`, with `M`'s advice hard-wired.
- It answers the one challenge with one query and replays the record for repeated challenges.
- It has a separate branch for `ctLen(n) = 0`.
- **Budget 1.** `finCall = 1`, the run makes at most one query (`chalHandler_costBoundedBy`), and the
  finalization makes none. The new generic lemma `toCompOn_budget_eq` / `buildComp_budget_eq` (any budget at least
  the cost gives the same run) then brings it to budget 1.

**`NM_b = H_b` when `msgLen(n) > 0`** (`exists_nmAdversary`).
- `B` asks `⟨M(a; ρ), M(a; ρ̃)⟩`.
- For each output `c_i` it emits `c_i ‖ Enc(f^L) ‖ Enc((¬f)^L)`, with `f = [c_i = y]`. It does the same for each bit
  of `a`, `m` and `σ`, giving `3r + 2(pl + L + sl)` ciphertexts.
- `recDist` reads the result back with `NMCCA2.guessBit`. In `guessBit_encPair`, correctness makes a pair's two
  ciphertexts differ, so at most one of them is the challenge. `ctLen_pos` shows that `msgLen(n) > 0` forces
  `ctLen(n) > 0`.

**`msgLen(n) = 0`.** `hybAcc_true_eq_false` follows from `rImpl_eq_of_msgLen_eq_zero`, so the advantage is 0.

### Questions for the audit

Is either reduction lossy? Does an equality fail on some branch? Check:
- budget 0, `r = 0`, `sl = 0`;
- no challenge, and repeated challenges;
- `A` outputting the challenge, or a malformed or invalid ciphertext;
- codec timeouts;
- `ctLen = 0`;
- `m₀ = m₁`.

Does `SimNMSecure`'s quantifier order (`Sim` chosen before `D`) allow D' and D'' to be used against the same `Sim`?
Is the budget lemma sound in general?

## Also check

**Statement freeze.**
- `decls2` against the base: 269 added, 0 changed, 0 removed.
- Every pre-existing declaration is byte-identical: `SimNMSecure`, `NMSecure`, both experiments and
  `simNMSecure_cpa_iff_nmSecure_cpa`.
- Only the two target bodies and their sketches changed.

**Rule 10.** No touched declaration reads another file's definition, including generated matchers and projections.
- The 10 helpers are foreign to each other, to the owned file, to `Indistinguishability/*`, `OracleSecurity`,
  `Games/*`, `AdaptiveCPA/*` and `ChallengeSim`.
- The review's whole-file seals A and B pass for all 11 files at the delivered head, and again at the landing head.
- The explicit-unfold scan finds 0 foreign definitions.

**API** (policy §3).
- Names, formula docstrings, sketches, module docstrings, and the owned file's `## Contents`.
- No `@[simp]`. The one public `abbrev`, `runB`, has `runB_eq`.
- Sizes are all below 1000 lines; the largest is `SimIND`, at 912.

**Duplication.** Ruling (Seyoon, 2026-11-13): the undisclosed duplicates are accepted as ledger debt **DL-37**, with
named payback. That disposition is not a finding. What you can still raise:
- a copy that DL-37 or DL-36 misses;
- a disagreement with the payback plan.

The DL-37 copies:
- `chunkAt` = `coinBlock`;
- the private `padFin_replicate_false`;
- `impl_of_ret`, `rdU`…`rdLog`, `rdState`, `finSt`;
- the generic neighbours.

**Landing edits** (`5da558b4d97aca00efd6dc396a1b0f3bffff268b`). They change no statement and no proof route; text outside comments is identical in
all 11 files.
- LE-W re-wraps the 68 lines that were longer than 100 characters.
- LE-D1 adds formula docstrings to `chalRun_eq`, `simFin_eq` and `nmFin_eq`.
- LE-D2 adds proof sketches to 10 long proofs.
- LE-D3 adds `SimINDGap`'s `## Main definitions`.

**Land order** (ruling 2026-11-13). nm-sim lands before the DL-30–DL-34 consolidation. When the consolidation lands,
it re-points these files to the moved names. That is not a finding here.

## Evidence

- **`review.md`:** the maintainer's independent review (ACCEPT WITH LANDING EDITS), with its findings, its
  promotion-request table and the consolidation re-point list.
- **`verification.zip`:** the review's raw evidence, at the delivered head. `PROVENANCE.txt` and the inner
  `SHA256SUMS` describe it. It covers:
  - integrity (587/587, patch replay to tree `a39affb9`);
  - a fresh build of 262 modules with 0 errors;
  - the admission census (26 → 24);
  - decls2;
  - the axioms of all 574 stored constants;
  - seals A and B for all 11 files, with a base control;
  - paired controls (22 probe pairs per variant, ALL_OK);
  - the explicit-unfold scan (1,850 items);
  - lint.
- **`landing.zip`:** the landing-edit run at the head. It holds:
  - the full diff;
  - the rebuild of the 11 modules and 3 facades;
  - decls2 from the delivered head to the landing head (empty);
  - all 574 constants' axioms, unchanged;
  - seals A and B, 22/22 at the head;
  - lint;
  - the widths;
  - the sketch audit.
- **`landing/`:** logs at the final head on the full-library tree.
  - `root-order.txt` and `root-checks.jsonl`: the 11 modules, the 3 facades and root `TCSlib`, all rc 0, each row's
    `source_sha256` matching `source-head.json`. `audits/pass-shelat/Checks` imports none of them.
  - `axioms-head.log`: the two targets and `simNMSecure_cpa_iff_nmSecure_cpa` each print
    `[propext, Classical.choice, Quot.sound]`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `da56632fb066b657d3054865cc1b4f7535018951`.
- **`pr.diff.txt`:** `git diff` from the base to the head.
- **`source-head.json`:** the head hashes of the 11 changed files.
- **`sources.zip`:** the source closure of the owned module at the head.

## Findings delivery

Return `gate19-nm-sim-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement change, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
