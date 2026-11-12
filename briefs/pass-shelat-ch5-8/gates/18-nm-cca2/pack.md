# Gate 18 · Under CCA2, secrecy and non-malleability coincide (`indSecure_cca2_iff_nmSecure_cca2`)

Round 1. Auditor Codex (standing ruling, 2026-11-11: Codex for audits and reviews).

- **PR:** draft [PR #294](https://github.com/Shilun-Allan-Li/tcslib/pull/294) at
  `1636480237286f538bb75b0021b2285edcd0b5b9` (branch `land/pass-shelat-nm-cca2`).
- **Target and base:** it targets `cryptography/pass-shelat-ch2-4` on base
  `4d10bc4e577a90345717c8777b6a9d16ffd7f1f8`. The fill was issued on `b96ab3ccc1915497ea3138df499eec00b6581db0`
  (the merge of #293). Every commit between the two is records only, and so are later base commits.
- **Commits:** the worker's 4 commits (Claude fill `nm-cca2`), then one maintainer commit of landing edits.
- **Scope:** this is a proof audit. The statement passed Gate 06 (#232) and is unchanged.

## The target

It lives in `PublicKey/NonMalleability/Indistinguishability.lean`, namespace
`TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.

```lean
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2
```

The source is [PS10, Theorem 175.9]: R. Pass and a. shelat, *A Course in Cryptography*, third edition, January
2010. IND-CCA2 is Definition 171.5 (`indGame`, `PublicKey/OracleSecurity.lean`); CCA2 non-malleability is
Definition 172.6 (`nmGame`: the adversary runs against the IND oracles through `nmCodec n ℓ`, outputs `ℓ`
ciphertexts, `nmOutput` decrypts them with `nmDecrypt` giving `⊥ = zeroBits` on a copy of the recorded challenge,
and `D` judges).

## The proof (check each step independently)

1. **(⇒) IND-CCA2 ⇒ NM-CCA2** (`nmSecure_cca2_of_indSecure_cca2`; helpers `Forward`, `Decrypt`).
   - `fwdHandler` is a T2 interactive handler with empty state and one outer call per query
     (`fwdHandler_impl`, `simulate_fwdHandler_impl`): it forwards `A`'s `Dec` and challenge queries.
   - The finalization `dFin` counts the entries of its own log (`length_logEmit_cntRead`) and asks CCA2's `Dec`
     (index `[]`) on `padL ctLen (a.drop (j·ctLen))` while `j < ℓ(n)`; then it returns
     `[D.output(layout 1ⁿ answers α ω) = [true]]` (`simulate_decHandler_finish`, by induction on the remaining
     budget; `ℓ = 0` is the base case).
   - `accept_indGame_decRed`: the IND game at each `b` equals `NM_b`. `castImpl_indImpl_dec` matches CCA2 `Dec`'s
     refusal of the recorded challenge (zeros) with `nmDecrypt`'s ⊥; every other ciphertext, malformed or invalid
     ones included, decrypts identically (invalid ones give `decAnswer none = 0`); with no challenge `st = none`;
     repeated challenges leave the same `st` on both sides; the timeout is inside `toCompOn` on both sides.
   - Budget `q·1 + ℓ` (`perCall`/`finCall` readers); the advice is carried by `exists_withAdviceOn`
     (`NUPPT.exists_comp` re-pairing, then `exists_withAdvice`).
2. **(⇐) NM-CCA2 ⇒ IND-CCA2** (`indSecure_cca2_of_nmSecure_cca2`; helper `Encrypt`).
   - `encHandler`: seed `ρ+ρ` bits read as two `Enc` tapes by take/drop; it outputs `ℓ = 2` encryptions of `g^m`
     and `(¬g)^m` under `pk`, `g = headD` of `A`'s guess (a timeout gives `g = false`); `finCall = 0`
     (`encHandler_finish`).
   - `guessBit`/`guessDist`: if the first decryption is valid return its bit, else `¬` the second
     (`guessBit_valid`, `guessBit_refused`, `guessDist_nmOutput`, using `S.correct` and `enc_length`). For
     `m > 0` the plaintexts differ at bit 0, so at most one ciphertext is the challenge.
   - `msgLen(n) = 0`: `indImpl_eq_of_msgLen_eq_zero` (published `_onSpec` readers only) makes the two IND games
     equal, advantage 0.
3. **Assembly** (`indSecure_cca2_iff_nmSecure_cca2`): the two directions, with each direction's polynomial
   budget.

Is either reduction lossy, or does either equality fail on some branch (budget 0, `ℓ = 0`, no challenge,
repeated challenges, `A` outputting the challenge itself or a malformed/invalid ciphertext, the codec timeout)?

## Also check

- **Statement freeze.** The target is byte-identical to the base (only its sketch was edited), and so is every
  other existing declaration, `NonMalleability/Simulation.lean` included.
- **Authorized readers (landing edit LE-1, escalation E-READER).** `PublicKey/OracleSecurity.lean` has exactly
  two additions, right after `indImpl_dec_onSpec`:
  - `indSpec_decRng : (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool)`;
  - `indImpl_dec_onSpec_cast`: `indImpl_dec_onSpec` with the valid answer cast through `indSpec_decRng`.

  Each must be public, not `@[simp]`, with a formula docstring, and there must be no other change. The file is now
  999 lines (limit < 1000); the split of its `PaddedCPA` section is scheduled with the consolidation and is not a
  finding.
- **Rule 10.** No touched declaration reads another file's definition, including generated matchers and
  projections. The three helper modules count as foreign to each other, to the owned file and to `OracleSecurity`.
  The two new readers may read `outLens` (their home file).
- **API.** Names, formula docstrings and sketches (policy §3), no `@[simp]`, file sizes (owned 655, Forward 350,
  Decrypt 350, Encrypt 332), the owned file's `## Contents`.
- **Duplication.** The generic material the review found (DL-36: `logEmit` vs `relabelN`, the round-input readers,
  `ofFn_nthCt`; deferred until the DL-30–DL-34 consolidation lands) is not a finding unless you disagree with
  deferring it or find an undisclosed copy that DL-36 misses.
- **Landing edits** (`1636480237286f538bb75b0021b2285edcd0b5b9`, review findings 1–3 and 7). They change no
  statement and no proof route: the two readers moved into `OracleSecurity.lean`, `Readers.lean` and its import
  deleted, one re-pointed `rw`, the stale "(statement phase)" title, two blank lines, three formula docstrings.

## Evidence

- `review.md`: the maintainer's independent review (ACCEPT WITH LANDING EDITS), with its findings table and
  dispositions.
- `verification.zip`: the review's raw evidence, run before the landing edits (plus the landing-edit probe):
  integrity; fresh build of 253 modules, 0 errors; admission census (27 → 26); statement comparison (64 added,
  0 changed, 0 removed); axiom census of 170 constants; whole-file closure seals A and B of all 5 files, base
  seals, 20 control probes; the explicit-reader scan; lint; the independent E-READER probe. `PROVENANCE.txt` and the
  inner `SHA256SUMS` describe it.
- `landing/`: logs at the final head.
  - `root-checks.jsonl`, `root-order.txt`: the 29 modules downstream of `OracleSecurity` and the fill, through
    `TCSlib`, rc 0, on the full-library tree, each row's `source_sha256` matching `source-head.json`.
    `audits/pass-shelat/Checks` imports none of them.
  - `axioms-head.log`: at the head, the target, both directions and the two new readers each print
    `[propext, Classical.choice, Quot.sound]`; `simNMSecure_cpa_iff_nmSecure_cpa` prints `sorryAx` (the two open
    `Simulation.lean` targets).
- `worker-report.md`: the worker's report, its `REPORT.md` at exchange `906f47381f5fdf677d88397251dd737c125e4bfb`.
- `pr.diff.txt`: `git diff` base..head.
- `source-head.json`: the head hashes of the 5 changed files.
- `sources.zip`: the source closure of the owned module at the head.

## Findings delivery

Return `gate18-nm-cca2-findings.md` as a Markdown file in this chat. For multiple evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement change, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
