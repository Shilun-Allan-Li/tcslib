# Gate 44 · resolutions, round 1 · HOLD → ruling, landing edit, pack correction

Codex's verdict is **HOLD**: 0 blockers, 1 major, 1 minor, 1 note.
- **Findings:** `findings-r1.md` (verbatim, filed by the maintainer; the evidence ZIP it mentions was not received).
- **Audited:** #340 at `916afc25c21f5e52b4b01958186ad55d2f615fd1` and #346 at `89a18a8225be1b76166af12a15179da291747783`;
  records `8f888790`; exchange `30ef1257`; joint tree T44 `33681cb8`.

Codex found **no mathematical gap**. Its confirmations are listed below.
- **Proofs.** T1 and T4 establish their frozen statements, edge cases included.
- **Integrity.** The frozen statements and the seven readers are intact, and LE-bb1m is proof- and doc-only.
- **Rule 10.** 24/24 joint-owner and 16/16 supplement seals pass, and request-set identity justifies reusing the seals of
  the three skipped owners.
- **Replay and axioms.** 16/16 rc 0, admissions 198 → 196, the standard axioms.
- **Grades.** BM-F01 to BM-F09 are all agreed. Six of #340's seven overlap disclosures are agreed; item 5 is G44-01.

| Finding | Grade | Resolution | Evidence and pointer |
|---|---|---|---|
| G44-01 | **major** | **Accepted and ledgered** (Seyoon, 2026-11-17, ruling G44-01). The two disclosed re-derivations are retained, and the debt is repaid in cleanup Stage 2. **DL-55:** T1's inline verdict identity (`Pairing/Assumptions.lean:199`) re-derives `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`). Stage 2 promotes that lemma to a shared low-level home, then re-points `TrapdoorPredictor` and T1 (proof-only). **DL-56:** #346's `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (`BonehBoyenMachine/Words.lean:261–271`) re-prove `Games.polyTimeComputable_rU`/`_rZ`/`_rW`/`_rS` (`Games/Efficiency.lean:538–550`). Stage 2 re-points the four, with a reader if the recorded obstruction needs one (proof-only). Both reports' "No duplicated proved material; nothing for the duplication ledger." lines keep their text, with a dated correction under each. The bb1-machine review's duplication paragraph carries a matching note. No code change. | `briefs/pass-shelat-ch5-8/duplication-ledger.md` rows DL-55, DL-56 and `cleanup-stages.md` § Stage 2 (records `4f4a7592`). The plan's ruling row of 2026-11-17. Corrections: `fills/pair-bdh/inhouse-r1/REPORT.md` (under line 99), `fills/bb1-machine/inhouse-r1/REPORT.md` (under line 260), and `fills/bb1-machine/final-r1/review.md` (§ Duplication and reuse). |
| G44-02 | minor | **LE-g44** on #346, docstrings only, commit `98cb0e521a94e94c304c78348fb5d3033435a3ed` on `89a18a82`. `Draws.lean`'s module docstring and `draw`'s docstring now attribute the bounded rejection sampler and its bound to the library's existing construction: `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean:578`, `:618`). For `0 < m < 2^n`, the sampler on `n · n` uniform coins with the fallback `0` is within `(1/2)^n` of uniform below `m`. `[PS10, Theorem 52.3]` (§2.8) is kept as context only: its proof remarks that the domain `Z_q` is easy to sample. The `## References` entries of `Draws.lean`, `Words.lean` and `Handler.lean` are corrected consistently. Each file is byte-identical to the parent once comments are stripped. | `pack-r2.md` § 2. `verification-r2.zip`: `checks/le-r2.txt` (comment-strip identity with controls), `checks/sources-r2.txt`, and `le-g44.diff.txt`. Replay T44′ (§ 4). |
| G44-03 | note | **Corrected in the round-2 pack** (no replay or control repair). Round 1's `pack-r1.md:339–341` doubled the paired-control figures on `Assumptions`. The actual figures, per variant (strict, coe), are **2 sealed and 2 unsealed probes**, with **25 expected sealed negatives (12 in A, 13 in B)**. Across strict and coe together that is 4 sealed and 4 unsealed probes and **50** negatives. Every negative fails exactly once, every reader passes, and every unsealed probe has 0 errors: ALL_OK in both variants. The round-1 pack stays as filed. | Recount from round 1's raw control logs: `verification-r2.zip` `checks/g44-03-controls.txt`. |

**Checks for the new head and T44′:**
- LE-g44 changes docstrings and comments only.
  - With comments stripped, each of the three files equals its parent byte for byte.
  - Three code mutations per file are each caught.
  - No other path changes.
- T44′ = records tip `4f4a7592` × #340 `916afc25` × (#346 + LE-g44) = tree
  `bee027f0903d531b3a43511cea16bfa123210291` in every merge order.
  - It differs from T44 in exactly the three LE-g44 files.
- Replay on a `cp -al` copy of round 1's output (`$SP/olean-replay-g44b`): the three files and their downstream.
  - Build: 10/10 rc 0, 0 errors; state check OK over 1427 modules; every rebuilt olean has link count 1.
  - Snapshot #4 verifies 0/0/0.
  - The 7 downstream oleans are byte-identical to T44's.
  - Admissions are 196, unchanged, and the axioms log is identical.
- Seals carried forward by comment-strip identity, confirmed by canonical coe-A on `Draws`, `Words`, `Handler` and
  `BonehBoyenMachine`.
  - Each is rc 0 with 0 errors.
  - Each request set is row-identical to round 1's.
- Lint has no new FAIL or WARN.

Then Gate 44 round 2 (Codex) at #346 `98cb0e52` with #340 `916afc25`.
