## ===== briefs/pass-shelat-ch5-8/gates/18-nm-cca2/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/18-nm-cca2/review.md =====

# nm-cca2 · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (1 high fixed by a landing edit, 1 medium-low, 3 low, 2 nit, 3 info;
no blockers remain after the edits).

Delivery: Claude worker, exchange `906f47381f5fdf677d88397251dd737c125e4bfb` (`inbox/fills/nm-cca2/`;
checkpoints `f3878eb2b`, `bd936f02c`), 4 patches on the issue base
`b96ab3ccc1915497ea3138df499eec00b6581db0`. Independent review on the landing branch (parent = campaign
`71da4e6a`, 0 Lean changes since the base); evidence `review-evidence.zip` (SHA-256
`fc321bfb04a7fc821da569bf2d56412fa64f70acb02565ad2d21dffbe3948c29`; `PROVENANCE.txt`; inner `SHA256SUMS`
635 entries, SHA-256 `002d52707ecf1e6db2a2d59b39b0423b7feed15150389e365685ac8abf22b55f`).

Target: [PS10, Theorem 175.9], `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2`
(`PublicKey/NonMalleability/Indistinguishability.lean`), proved with helpers
`Indistinguishability/{Forward, Decrypt, Encrypt}.lean` (and `Readers.lean`, removed at landing).

## Checks (re-run by the reviewer)
- Integrity: payload sums 625/625; `git am` at the issue base reproduces the worker's proof-branch tree
  `746ec283e9e6…`; the 5 files are byte-identical to `src/`.
- Build: the fill closure plus downstream (253 modules = issued 249 + the 4 helpers), fresh tree, 253/253,
  0 errors.
- Admissions 27 → 26 (exactly the target). Statements: 64 ADDED, 0 CHANGED, 0 REMOVED.
- Axioms: the target and both directions `[propext, Classical.choice, Quot.sound]`; all 170 stored constants
  of the 5 files standard. `simNMSecure_cpa_iff_nmSecure_cpa` still carries `sorryAx` (the two open
  `Simulation.lean` targets), as at the base.
- Rule 10: whole-file closure seals, variant A (`PolyExpr.eval` exempt as notation) and B (sealed): the owned
  file, Forward, Decrypt and Encrypt pass both; `Readers.lean` fails each with exactly one error, at
  `indImpl_dec_onSpec_cast` (the disclosed exception). Controls: 20 probes, ALL_OK in both variants (67/72
  sealed negatives fail exactly once). Explicit scan 526 items, 0 foreign. Lint 0 FAIL (same 6 WARN as base).
- E-READER confirmed independently: with only `outLens` sealed, four routes to the cast form each leave
  `decAnswer X = cast _ (decAnswer X)`; unsealed, the one-line proof passes. No published reader closes it.

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | high | E-READER: no cast-form reader of the `Dec` answer in `PublicKey/OracleSecurity.lean`; the helper `Readers.lean` reads `outLens`. | **Landing edit LE-1:** `FixedLengthPKScheme.indSpec_decRng` and `indImpl_dec_onSpec_cast` added beside `indImpl_dec_onSpec`; `Readers.lean` and its import deleted; `castImpl_indImpl_dec` re-pointed. Both readers pass seals A and B in their home file. |
| 2 | low | Owned module title still "(statement phase)". | **Landing edit LE-2.** (`Simulation.lean` keeps it: still sorried.) |
| 3 | nit | Two doubled blank lines in the owned file. | **Landing edit LE-3.** |
| 4 | medium-low | `logEmit` (`Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`); its log lemmas mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly`. Not disclosed. | Ledger **DL-36**; promotion redirected beside `relabelN`. |
| 5 | low | Public `finU`…`finL`, `fields_finInput` repeat the DL-34 round-input readers (`rU`…`rL`). | Ledger **DL-36**; re-point to consolidation R6. |
| 6 | low | `ofFn_nthCt` is the generic block fact of DL-34 (`ofFn_acTapes`, `ofFn_pkTapes`). | Ledger **DL-36**. |
| 7 | nit | Label-only docstrings: `polyTimeComputable_cntRead`, `_ansRead`, `_finFields`; `finZ`…`finL`. | **Landing edit:** formulas added to the three; the readers go with finding 5. |
| 8 | info | REPORT says two names re-point in `castImpl_indImpl_dec`; only one does. | No action. |
| 9 | info | The owned file uses `ChallengeSim.expect_sample_*` and `AdaptiveCPA.castImpl*`, which the consolidation moves; its opens should keep them resolving. | Consolidation landing rebuilds and re-points (land-order ruling 2026-11-12). |
| 10 | info | Proof review of both directions, the handlers, finalization, budgets and edge cases (budget 0, ℓ = 0, no or repeated challenge, timeout, `msgLen = 0`): no issues. | — |

**Promotion requests** (worker): accept `fwdHandler`/`_impl` and `exists_withAdviceOn` (→ `Games/Efficiency`),
`cntRead`/`ansRead` (→ `BitCodec`); `logEmit` per finding 4; `finU`…`finL` per finding 5;
`indImpl_eq_of_msgLen_eq_zero` (→ `OracleSecurity`) waits for the split below. All in DL-36.

**Size.** `PublicKey/OracleSecurity.lean` goes 982 → 999 lines (limit < 1000). No headroom: the consolidation's
readers R1, R3, R4 for this file need the split first. Recommended split (reviewer): move `section PaddedCPA`
(297 lines, self-contained; consumers `TrapdoorCPA.lean` and the facade docstring; the `ChallengeSim`/
`RecordHandler` imports go with it) to `PublicKey/OracleSecurity/PaddedCPA.lean`. Scheduled as a landing edit
of the consolidation.

## Landing
Branch `land/pass-shelat-nm-cca2`, rebased onto campaign `4d10bc4e5` (records-only since `71da4e6a`): the 4
delivered commits + landing edits `1636480237286f538bb75b0021b2285edcd0b5b9`. After the edits: the 29 modules
downstream of `OracleSecurity` and the fill (through `TCSlib`) rebuilt on the full tree, hash-bound
(`landing/`). `audits/pass-shelat/Checks` imports none of these modules.

## ===== briefs/pass-shelat-ch5-8/gates/18-nm-cca2/worker-report.md =====

# Fill `nm-cca2` — final

**Worker:** Claude (external). **Issue base:** `b96ab3ccc1915497ea3138df499eec00b6581db0` on
`cryptography/pass-shelat-ch2-4` (the merge of #293). **Local proof branch:** `fill/nm-cca2`, head
`9bd89494b`, never pushed; the whole series from the base is in `patches/` (4 patches). **Pack:** read
at exchange `3f6d6783a1e4527e5287c63a9f1a0075fb6d0369`; `SHA256SUMS` 7/7 OK; all 249 entries of
`SOURCE-SHA256SUMS` match the base. **Checkpoints on the exchange:**
- `f3878eb2b`, checkpoint 1: (⇒) and escalation E-READER;
- `bd936f02c`, checkpoint 2: (⇐) and the target.

## 1. Target status

`TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2`
[PS10, Theorem 175.9] is **proved**. Its statement is byte-identical to the base (`… := by`), and
the body is `exact ⟨S.nmSecure_cca2_of_indSecure_cca2, S.indSecure_cca2_of_nmSecure_cca2⟩`.

`#print axioms` (`evidence/logs/axioms.log`, probe `evidence/seal/Axioms.lean`):
- `indSecure_cca2_iff_nmSecure_cca2`: `[propext, Classical.choice, Quot.sound]`;
- `simNMSecure_cpa_iff_nmSecure_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]`. It still depends on the two
  `Simulation.lean` targets.
- **Every stored constant** of the five changed or new files (170 constants, auxiliary
  declarations included) depends on a subset of `[propext, Classical.choice, Quot.sound]`;
  0 fall outside it.

**One open item: escalation E-READER (§2).** A reader of `PublicKey/OracleSecurity.lean` is missing.
The proof states it in one helper module, and its proof is the fill's only definitional reading
of a foreign definition (`outLens`). It must move to its home file at landing.

## 2. Escalation E-READER: the public-key decryption answer has no cast reader

(First reported at checkpoint 1; unchanged.)

**Obligation.** In (⇒) the CCA2 adversary asks its decryption oracle for each of `A`'s ciphertexts
and must show that the answers, read as strings, are `NM_b`'s decryptions. On T2's codec the
oracle's answer to a query `x` in state `st` is (`castImpl_eq`, then `indImpl_dec_onSpec`,
`decOpen_cca2`):

```
padFin ((acDout S 0).eval n) (List.ofFn p.1),   p.1 = FixedLengthScheme.decAnswer X   (valid branch)
```

where `X = decodeFin _ (S.dec ⟨sk, c⟩)`. `FixedLengthPKScheme.indImpl_dec_onSpec` states this
`decAnswer X` (`: Fin (S.msgLen.eval n + 1) → Bool`) at the oracle's answer type
`(S.indSpec n).rng 0 = Fin (S.outLens n 0) → Bool` **without a cast**: the types agree only by
unfolding `outLens`. So `List.ofFn p.1` is `List.ofFn` at width `S.outLens n 0`. Relating it to
`⟦S.nmDecrypt sk st c⟧` (width `msgLen + 1`) leaves, after every published reader, the goal

```
HEq ((decAnswer X, st).1 : Fin (S.outLens n 0) → Bool) (decAnswer X : Fin (S.msgLen.eval n + 1) → Bool)
```

With `outLens` sealed this cannot be closed. `HEq.rfl`, `cast_eq` and rewriting under `Prod.mk`
(`decAnswer_some`/`_none`, `outLens_zero`) all need the two widths to be definitionally equal
(`evidence/probes/EscNoReader.lean`, `logs/escalation-EscNoReader.log`, which shows the state).

**Reader requested** for `PublicKey/OracleSecurity.lean`. This is the public-key analogue of what
not-cca2 r2 added to `PrivateKey/OracleSecurity.lean`:

```lean
/-- The decryption oracle answers a validity flag and a message. -/
theorem FixedLengthPKScheme.indSpec_decRng (n : ℕ) :
    (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- `indImpl_dec_onSpec` with the valid answer read through `indSpec_decRng`. -/
theorem FixedLengthPKScheme.indImpl_dec_onSpec (atk) (b) (n) (pk sk) (c : (S.indSpec n).dom 0) (s) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (S.indSpec_decRng n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s   -- (the current statement)
```

I recommend adding the second **beside** `indImpl_dec_onSpec` under a new name (for example
`indImpl_dec_onSpec_cast`), which leaves every consumer untouched. `indImpl_dec_onSpec` is used at
the base by `AdaptiveSecurity` (`adaptiveIndImpl_one`, which rewrites both sides with it), and by
`AdaptiveCPA/Games` and `BitwiseCPA/Eager` (the refused branch under CPA). Replacing its statement
instead would require rechecking those three files. Its proof unfolds `outLens`, which is legitimate
only in `OracleSecurity.lean`.

**What the fill does.** `Indistinguishability/Readers.lean` states both readers exactly as above,
as `NMCCA2.indSpec_decRng` and `NMCCA2.indImpl_dec_onSpec_cast`.
- The first is proved from published readers (`indSpec_rng`, `outLens_zero`).
- The second has its one-line home-file proof. It is a **disclosed Rule-10 exception, confined to
  that one lemma**. Every consumer uses only the cast form.

Evidence:
- **Seal A and seal B of `Readers.lean`** fail with exactly one error, at
  `indImpl_dec_onSpec_cast` (`logs/seal/seal-{A,B}-Readers.log`).
- **The same seal with `FixedLengthPKScheme.outLens` alone exempt** compiles
  (`seal/SealAReadersOutLensExempt.lean`, `logs/seal/seal-A-ReadersOutLensExempt.log`), so `outLens` is
  the only obstruction.
- **Probe (b)** (`EscWithReader.lean`): with the cast reader, the consumer obligation compiles
  under a seal of `outLens` and the other definitions involved.
- **Probe (c)** (`EscReaderSealed.lean`): the reader's own proof fails once `outLens` is sealed.
- **Every other file of the fill passes both seals (§7).**

**At landing:**
1. Add the two readers to `OracleSecurity.lean`.
2. Delete `Readers.lean` and its import in the owned file.
3. Re-point two names in the owned file's `castImpl_indImpl_dec`: `NMCCA2.indSpec_decRng` → `S.indSpec_decRng`, and
   `indImpl_dec_onSpec_cast` → the published cast form.

**Please confirm this route, or rule otherwise.**

## 3. The proof

### (⇒) IND-CCA2 ⇒ NM-CCA2 (brief step 1; `nmSecure_cca2_of_indSecure_cca2`)

- **Forwarding handler** (`Forward.lean`). `fwdHandler din dout …` is a `Games.InteractiveHandler`
  with empty state and `perCall = 1`, whose round forwards each inner query to the outer oracle of
  the same index and returns its answer. It is generic in the lengths, the seed, the adversary
  input and the finalization. `fwdHandler_impl` gives `impl i x s = query i x (fun y => pure (y, s))`,
  and `simulate_fwdHandler_impl` gives `simulate impl c s = c.bind (fun a => pure (a, s))`.
- **Log readers** (`Forward.lean`). `logEmit G L` concatenates `G` over the suffixes
  `pairSndD^[i] L`, `i ≤ |L|`. It is polynomial-time by `polyTimeComputable_iterateEmit`, and on an
  encoded log it is `h.flatMap g` (`logEmit_encodeLog`). With `cntRead` it counts entries; with
  `ansRead` it collects the answers.
- **The reduction** (`Decrypt.lean`). `decHandler S ℓ D` is `fwdHandler` on `acDin S`/`acDout S`,
  with:
  - seed `D.coins`;
  - the adversary run on `pk = fst z`, where `z = ⟨pk, α⟩`;
  - `finCall = ℓ`, `outLen = 1`.

  Its finalization round counts the decryptions asked so far, `j`, in the log.
  - If `j < ℓ(n)`, it asks `Dec` (index 0) on block `j` of `A`'s output, `padL ctLen (a.drop
    (j·ctLen))`, using unary multiplication, prefix dropping and `padL`.
  - Otherwise it returns `[D.output(layout 1^n answers α ω) = [true]]`
    (`polyTimeComputable_pairEq`).

  `simulate_decHandler_finish` proves its equation against *any* outer oracle whose `Dec` answers
  are deterministic and keep the state. The proof is by induction on the remaining budget along
  the log.
- **Advice** (`exists_withAdviceOn`, general form): `NUPPT.exists_comp` re-pairs
  `⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `NUPPT.exists_withAdvice` hard-wires `β n = D.advice n`. So
  `B'.toCompOn codec n q pk (coinsCongr h n r) = B.toCompOn codec n q ⟨pk, D.advice n⟩ r`.
- **The game identity** (owned file, `accept_indGame_decRed`): `accept (Ind_b(B')) = accept (NM_b(A, D))` at every `n`.
  1. `B'`'s coins are `(ω, r)` through `φ` and `coinsCongr`; `ω` is `D`'s coins through
     `coinsEquivPoly`.
  2. Transport the run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`)
     and apply T2's equation.
  3. The handler forwards, so the run is `A` against the CCA2 oracles, then the finalization in
     the final state `st` (`simulate_bind`).
  4. `castImpl_indImpl_dec`: CCA2's `Dec` on T2's codec answers `⟦nmDecrypt sk st c⟧`, refusing the
     recorded challenge with `0` exactly as `nmDecrypt` does. This uses the requested reader.
  5. `decBlock_eq_nthCt`: the reduction's block `i` is `nthCt` `i`.
  6. `decAnswers_eq_nmOutput`: the answers are `S.nmOutput sk st a`.
  7. Transport `A`'s run back to `nmCodec` (`nmCodec_eq_bitCodec`).
- **The bound.** `B'` has budget `(q · perCall) + finCall = q·1 + ℓ`. CCA2 security gives `ε`, and
  the NM advantage equals `B'`'s IND advantage at every `n`.

### (⇐) NM-CCA2 ⇒ IND-CCA2 (brief step 2; `indSecure_cca2_of_nmSecure_cca2`)

- **The reduction** (`Encrypt.lean`). `encHandler S` is `fwdHandler` on `acDin S`/`acDout S`, with:
  - a seed of two encryption tapes, `ρ + ρ` bits (`encTape` reads them as `Enc` coins);
  - the adversary run on the reduction input `pk`;
  - `finCall = 0`, `outLen = ctLen + ctLen`.

  Its finalization reads `A`'s guess `g` (the first output bit) and outputs
  `padL ctLen (Enc(1^n, ⟨pk, b^{msgLen}⟩; tape))` for `b = g` with the first tape and `b = ¬g` with
  the second (`polyTimeComputable_eFin`). By `encHandler_finish`, the finalization is
  `pure (c₁ ‖ c₂)` and asks nothing.
- **The distinguisher** `guessDist` is uniform, without coins:
  `guessBit w = if w[0] then w[1] else ¬(last w)`.
  - `guessBit_valid`: a valid first decryption of `g^m`, `m > 0`, gives `g`.
  - `guessBit_refused`: `⊥` followed by a valid decryption of `(¬g)^m` gives `g`.
- **The guess is recovered** (`guessDist_nmOutput`), for any recorded challenge `st`.
  1. By `S.correct` (with `S.enc_length` for the padding), `c₁` decrypts to `g^m` and `c₂` to
     `(¬g)^m`.
  2. So `c₁ ≠ c₂` (bit 0 differs, `m > 0`), and at most one is the challenge.
  3. If `st ≠ some c₁`, use `guessBit_valid`; otherwise `st ≠ some c₂` and use `guessBit_refused`.

  The output's two blocks are `c₁` and `c₂` (`ofFn_nthCt`). `flatten_ofFn_two`, derived from
  `OneWay.flatten_ofFn_two`, handles `Fin ((const 2).eval n)` without reading `PolyExpr.eval`.
- **The game identity** (`accept_nmGame_encRed`, for `msgLen(n) > 0`):
  `accept (NM_b(B, 2, guessDist)) = accept (Ind_b(A))`. The structure is that of (⇒):
  1. coins `(ω, r)` through `φ`;
  2. transport and T2's equation;
  3. forwarding, `simulate_bind` and the finalization;
  4. pointwise `guessDist_nmOutput`;
  5. transport back.

  The result does not depend on `ω` or on the distinguisher's coins (`expect_const`).
- **`msgLen(n) = 0`** (`indImpl_eq_of_msgLen_eq_zero`): both halves of a challenge are `[]`, so
  `indImpl .cca2 false = indImpl .cca2 true` query by query (published `_onSpec` readers only), the
  two games are equal, and the advantage is `0 ≤ ε(n)`.
- **The bound.** `B` has budget `q·1 + 0` and `ℓ = 2`. Non-malleability gives `ε`, and the IND
  advantage is at most the NM advantage at every `n`.

### Assembly (brief step 3)

The target is the pair of the two directions. The budgets are the polynomials
`(q.mul perCall).add finCall` of each direction, read through `PolyExpr.eval_add`/`eval_mul` and
the handlers' `_perCall`/`_finCall` readers.

### Edge cases

- **Budget 0:** every lemma is for an arbitrary budget, by induction on computations or on the
  remaining budget.
- **`ℓ = 0`:** (⇒)'s finalization induction starts at `j = ℓ` and returns `D`'s verdict on `[]`.
- **`msgLen(n) = 0`:**
  - (⇐) is handled separately (above);
  - (⇒) needs no case split, since `decAnswer` at width 1 is uniform.
- **No challenge asked (`st = none`):**
  - in (⇒), `Dec` answers everything, and so does `nmDecrypt` (`none ≠ some c`);
  - in (⇐), both ciphertexts decrypt validly.
- **Repeated challenges:** the state records the first. In (⇒) both sides read the same `st`;
  (⇐) is uniform in `st`.
- **`A` outputs the challenge itself, or a malformed or invalid ciphertext (⇒):** both sides answer
  `nmDecrypt sk st c`, whatever `c` is: `⊥ = 0` on a copy, `decAnswer none = 0` on an invalid one,
  and blocks are read by position whatever their content.
- **The codec's timeout output:**
  - in (⇒), `A`'s timeout output is part of `toCompOn` on both sides and is transported with it;
    the reduction's own budget is never short, by T2's equation;
  - in (⇐), `A`'s timeout output `zeroBits 1` is the guess `g = false`, which the reduction
    encrypts and the distinguisher recovers like any other.

## 4. Changed files and the sketch edit

| File | Change |
|---|---|
| `NonMalleability/Indistinguishability.lean` (owned, 660 lines) | 5 imports added (the 4 helpers, `AdaptiveCPA.Games`); a `## Contents` list; the status line in `## Main results`; a `section Proof` with both directions; the target's sketch rewritten to describe the delivered proof; the target's body. Unchanged: the statement, every other declaration, the statement prose and the global simp attributes. |
| `…/Indistinguishability/Readers.lean` (new, 71 lines) | the two requested readers (escalation, §2) |
| `…/Indistinguishability/Forward.lean` (new, 349 lines) | forwarding handler; finalization-input readers; `logEmit` |
| `…/Indistinguishability/Decrypt.lean` (new, 350 lines) | (⇒): `decHandler`, its finalization equation, `exists_withAdviceOn` |
| `…/Indistinguishability/Encrypt.lean` (new, 332 lines) | (⇐): `encHandler`, `encTape`, `encCt`, `guessDist`, `indImpl_eq_of_msgLen_eq_zero` |

No other file is touched; `Simulation.lean` is unchanged. The owned file imports its four children
precisely and lists them under `## Contents`. Every file is below 1000 lines and no line exceeds
100 characters.

**The sketch edit.** The target's sketch keeps the source's two steps and the closing paragraph.
- Step (⇒) now also says that the adversary forwards every query, and that `Dec` decrypts every
  other ciphertext as `NM` does. It names the handler (`NMCCA2.decHandler`) and the advice route
  (`NMCCA2.exists_withAdviceOn` from `exists_withAdvice`/`exists_comp`).
- Step (⇐) names `NMCCA2.encHandler` and `NMCCA2.guessDist` and states that at `msgLen(n) = 0` the
  CCA2 games coincide.
- Both steps cite their theorems.

## 5. New declarations

Every public declaration has a docstring with its formula, and the nontrivial ones have a proof
sketch. No `@[simp]` attribute was added. `simps` readers carry `isSimp := false`.

- **Readers:** `NMCCA2.indSpec_decRng`, `NMCCA2.indImpl_dec_onSpec_cast`.
- **Forward:**
  - `fwdHandler`, with `simps` readers `_stateLen`, `_seedLen`, `_perCall`, `_init`, `_advIn`,
    `_outLen`, `_finCall` and `_finRun`;
  - `fwdHandler_impl`, `simulate_fwdHandler_impl`;
  - `finU`/`finZ`/`finW`/`finA`/`finL` with their `_eq` lemmas, `fields_finInput`,
    `polyTimeComputable_finFields`;
  - `logEmit` with `_eq`, `polyTimeComputable_logEmit`, `logEmit_encodeLog`;
  - private: `rState`, `rIdx`, `rQuery`, `rLog`, `rAns`, `fields_input`, `fwdRun`,
    `polyTimeComputable_fwdRun`, `length_iterate_pairSndD_le`, `iterate_pairSndD_encodeLog`,
    `flatMap_range_drop`, `length_le_length_encodeLog`.
- **Decrypt:**
  - `cntRead` and `ansRead`, each with `_eq` and `polyTimeComputable_`;
  - `length_logEmit_cntRead`, `logEmit_ansRead`;
  - `decHandler` with `_seedLen`, `_perCall`, `_finCall`, `_outLen` and `_advInput`;
  - `simulate_decHandler_impl`, `decBlock` with `_eq`, `simulate_decHandler_finish`,
    `exists_withAdviceOn`;
  - private: `dCnt`, `dCt`, `dIn`, `dFin`, `polyTimeComputable_dFin`, `polyTimeComputable_decAdvIn`.
- **Encrypt:**
  - `encHandler` with `_seedLen`, `_perCall`, `_finCall`, `_outLen` and `_advInput`;
  - `simulate_encHandler_impl`;
  - `encTape` with `_eq`, `ofFn_encTape`; `encCt` with `_eq`; `encHandler_finish`;
  - `guessBit` with `_eq`, `guessDist`, `guessDist_distinguisherL`, `guessBit_valid`,
    `guessBit_refused`;
  - `indImpl_eq_of_msgLen_eq_zero`;
  - private: `eBit`, `eMsg`, `eTape`, `eCt`, `eFin`, `polyTimeComputable_eFin`,
    `polyTimeComputable_encAdvIn`, `guessFun`, `polyTimeComputable_guessFun`.
- **Owned file:**
  - `nmCodec_eq_bitCodec`, `ofFn_nthCt`;
  - `nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2`;
  - private: `castImpl_indImpl_dec`, `decBlock_eq_nthCt`, `decAnswers_eq_nmOutput`,
    `accept_indGame_decRed`, `flatten_ofFn_two`, `guessDist_nmOutput`,
    `accept_nmGame_encRed`.

## 6. Promotion and reader requests, duplication

- **Reader request (blocking for Rule 10):** `FixedLengthPKScheme.indSpec_decRng` and the cast form
  of `indImpl_dec_onSpec`, both for `PublicKey/OracleSecurity.lean` (§2).
- **Promotion requests (generic):**
  - `NMCCA2.fwdHandler` with `fwdHandler_impl` and `simulate_fwdHandler_impl` →
    `Games/Efficiency.lean`. This is the forwarding interactive handler; `AdaptiveCPA`'s
    `acHandler_impl_forward` is one branch of it.
  - `finU`…`finL` and `fields_finInput` → `Games/Efficiency.lean`, beside
    `InteractiveHandler.finInput`.
  - `logEmit`, `polyTimeComputable_logEmit` and `logEmit_encodeLog` → `Games/Efficiency` or
    `Games/Machines.lean`. They are readers of an encoded query log.
  - `cntRead`, `ansRead`, `length_logEmit_cntRead` and `logEmit_ansRead` → `Games/BitCodec.lean`.
  - `exists_withAdviceOn` (hard-wiring a second input component, for every codec and budget) →
    `Games/Efficiency.lean`, beside `exists_toCompOn_of_toComp`, or `Randomized/Closure.lean`.
  - `indImpl_eq_of_msgLen_eq_zero` → `PublicKey/OracleSecurity.lean`.
- **DL-30–34 overlaps:**
  - **The round-input readers.** `Forward.lean` re-derives private readers (`rState`, `rIdx`,
    `rQuery`, `rLog`, `rAns`, `fields_input`) from `InteractiveHandler.input_eq`, in the general
    form; they play the role of `AdaptiveCPA`'s private `rS`, `rI`, `rX`, `rL`, `rFwd`.
  - **`impl_of_ret`.** `fwdHandler_impl` does its own two-round `buildComp` argument (query, then
    return); it is not a copy of `impl_of_ret`.
  - **`ofFn_padFin_eq_padL`.** `Decrypt.lean` rewrites `ofFn_padFin_eq_take` and
    `EnsembleLemmas.padL_eq` inline (no lemma).

  Nothing was copied from `AdaptiveCPA/`, `BitwiseCPA/` or `OracleFromPRF/`.
- **Public lemmas imported, not copied:**
  - `AdaptiveCPA.castImpl`, `castImpl_eq`, `expect_simulate_castImpl_toCompOn`,
    `indCodec_eq_bitCodec`, `acDin`/`acDout` with `_zero`, `acDin_eval`/`acDout_eval`, `ofFn_cast`,
    `headD_ofFn_one`;
  - `ChallengeSim.expect_sample_equiv`/`_prod`/`_comm`;
  - `OneWay.flatten_ofFn_two`, `OneWay.polyTimeComputable_unaryMulPair`;
  - `GGMRed.ofFn_padFin_of_length`, `ofFn_padFin_eq_take`;
  - `EnsembleLemmas.padL_eq`/`length_padL`/`polyTimeComputable_padL`/`polyTimeComputable_zeros`;
  - `Complexity.polyTimeComputable_iterateEmit`, `polyTimeComputable_pairEq`.

  The maintainer re-points any of these that the parallel `dl-consolidation` moves.

## 7. Checks

- **Preflight** (`logs/preflight.log`, before any cache or Lean work):
  - `nproc` 4;
  - cgroup v1 with no effective limit (`memory.limit_in_bytes` 9223372036854771712), so the
    headroom is `MemAvailable` = 16,021,256 kB = 15.27 GiB (floor 4 GiB: PASS). Memory in use
    (`usage − total_cache + total_shmem`) was 178,421,760 B;
  - the clone (`/workspace/fill`, a worktree of the session's clone), the payload and `/tmp` are on
    ext4 `/dev/vda`, with 25,602,281,472 B free (floor 12 GiB: PASS). No tmpfs was used.
- **Toolchain:** Lean 4.25.0 (`cdd38ac5115b…`) installed by `elan` after the preflight. Disk
  re-check before the cache: 23.0 GB free (floor 8 GiB: PASS; `logs/cache-store.log`).
- **Cache:**
  - The archive store `~/.cache/mathlib` was absent before the fetch.
  - The narrowed `lake exe cache get` over the 97 roots (`logs/mathlib-roots.txt`, identical to the
    pack's `roots.txt`) downloaded 2,370 files, decompressed 2,370 and exited 0
    (`logs/cache-get.log`).
  - Package pins: 11 present match, 0 mismatch; `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and
    `MD4Lean` are ABSENT, and the order imports none of them (`logs/packages-check.log`).
  - No zero-size `.olean`; the root probe passed (`logs/cache-probe.log`).
  - The helpers import no Mathlib module directly, so the roots are unchanged.
- **Bootstrap** (addendum item 5; `logs/bootstrap-*.tsv`, `logs/bootstrap/`):
  - first the owned file's 151-module upstream closure, in `order.txt` order (all pass);
  - then the owned file at the base and `AdaptiveCPA/Hybrid`, `/Handler`, `AdaptiveSecurity`,
    `AdaptiveCPA/Games` (all pass);
  - the remaining modules were built by the sweep.

  The pack's order is `evidence/bootstrap-order.txt`.
- **Order:** `evidence/order.txt` is the issued 249-module order with the four helpers inserted
  directly before `NonMalleability/Indistinguishability` (253 modules). Every helper's imports
  precede it. Its new dependency `AdaptiveCPA/Games` and that file's closure already precede the
  target in the issued order (positions 140–161 against 173).
- **Sweep** (final head, fresh olean tree `.lake/sweep-oleans`, one `lean_check_tree.sh` call per
  module): **253 passed, 0 failed**, 888.8 s of Lean time, peak child RSS 2,941 MiB. The sweep started at `62644213d`. The last commit (`9bd89494b`, owned file only) landed before the sweep reached the owned file (module 177), so every module was checked at the final head's content (`logs/sweep.tsv`, `logs/sweep/`).
- **Admissions** (`logs/sorry-census.txt`): **26** `sorry` declarations against 27 in `base-sorries.txt`. Removed: exactly `NonMalleability/Indistinguishability: indSecure_cca2_iff_nmSecure_cca2`. Added: none.
- **Axioms:** §1.
- **Rule 10: whole-file seals over the full TCSlib import closure.**
  - **Census** (`seal/Scan*.lean`, `logs/seal/scan-*.log`). For each file, a module with exactly
    the file's imports lists every seal candidate of its full TCSlib import closure: every TCSlib
    definition that is neither reducible nor already irreducible, not an instance, not a structure
    projection or auxiliary recursor, and not private or internal. Generated matchers are
    included. The helper modules are foreign to each other and to the owned file, since the census
    sees only the file's imports.
  - **Seals** (`seal/Seal{A,B}*.lean`, `logs/seal/seal-*.log`). Each is a verbatim copy of the file
    with `attribute [local irreducible]` on all its candidates, after the first `open` of its first
    namespace, so the whole file is sealed. Seal A exempts `PolyExpr.eval` as notation; seal B
    seals it too.

    | File | Candidates (A / B) | Seal A | Seal B |
    |---|---|---|---|
    | owned file | 1277 / 1278 | pass | pass |
    | `Readers` | 1232 / 1233 | **fails**: 1 error, at `indImpl_dec_onSpec_cast` (the requested reader) | **fails**: 1 error, at `indImpl_dec_onSpec_cast` (the requested reader) |
    | `Forward` | 1140 / 1141 | pass | pass |
    | `Decrypt` | 1249 / 1250 | pass | pass |
    | `Encrypt` | 1249 / 1250 | pass | pass |
    | base owned file (control) | 1232 / 1233 | pass | pass |
  - **Base control:** the base owned file under the same seals compiles (A and B).
  - **Paired controls** (`seal/Controls{Unsealed,SealedA,SealedB}.lean`, `logs/seal/Controls*.log`).
    There are 13 readings through definition bodies: `inLens`, `outLens`, `PolyExpr.eval`, `seedIn`,
    `padFin`, `acDin`, the helpers' `finU`, `fwdHandler`, `cntRead`, `decHandler`, `encHandler` and
    `guessBit`, and the owned file's `nmCodec`.
    - Unsealed: all 13 pass.
    - Seal A: 12/13 fail; only the `PolyExpr.eval` control passes, as designed.
    - Seal B: 13/13 fail.
  - **Findings and fixes.** The first seal run, at `60b4ad5bf`, failed in two files besides the
    expected `Readers`. Commit `62644213d` fixed them:
    - `Forward`'s empty-log bound read `MachineCodec.encodeLog []` (now `Nat.zero_le`);
    - `Decrypt`'s `ansRead [] = []` read `pairFstD []`/`pairSndD []` (now `pairFstD_nil` and
      `pairSndD_of_pairDecode_eq_none`);
    - `Decrypt`'s verdict round matched `decodeBitMove_ret` through `padFin` (now on the left only).

    Checkpoints 1 and 2 carry the unfixed versions.
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids.log`, `logs/rwids-classified.tsv`,
  `logs/rwids-summary.log`). The scan collects every identifier that the added lines pass to `rw`,
  `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`. Each is resolved
  in its file's namespace with the file's `open`s; `S.foo` is read as `FixedLengthPKScheme.foo`.
  317 entries over the five files. **No foreign definition is passed.** The definitions passed are each file's own:
  - `Forward`: `finU`…`finZ` and the private `rState`…`rAns`, `fwdRun`;
  - `Decrypt`: `decHandler` and the private `dCnt`, `dCt`, `dIn`, `dFin`;
  - `Encrypt`: `encHandler` and the private `eBit`, `eMsg`, `eTape`, `eCt`, `eFin`, `guessFun`.
- **Lint** (`logs/lint-final.log`, `logs/lint-base.log`):
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`
  gives **0 FAIL, 6 WARN over 30 files**. The six warnings are identical to the base's (0 FAIL,
  6 WARN over 26 files), all on untouched files. The five fill files have no warning.
  `git diff --check` is clean.
- **Patch replay** (`logs/patch-replay.log`): `git am` of `patches/` on the base in a clean worktree
  reproduces all five files of `src/` byte for byte; the tree hash equals the proof branch's.
- **Process discipline:**
  - One Lean process at a time, every module check through `scripts/lean_check_tree.sh`, wrapped by
    `tools/chk.py` (UTC start and end, wall time, max child RSS).
  - No `lake build`, no unfiltered cache get, no timeouts.
  - A first final sweep was stopped at module 98 to fix line widths before the seals
    (`logs/dev/sweep-aborted.tsv`); the reported sweep ran once at the final head.
  - The proof branch stayed local.
  - AGENTS.md says to use the VS Code LeanInfoView instead of running `lean`. The brief and the
    dispatch require `scripts/lean_check_tree.sh`, which is what I used.

## 8. For the maintainer

1. **E-READER** (§2) needs a ruling and the two readers in `OracleSecurity.lean`. After that,
   `Readers.lean` goes away and every file of the fill passes the seal.
2. **Stale module title.** The owned file's module docstring is still titled
   "Non-malleable encryption (statement phase)". The brief allows changing only the target's
   sketch and status line, and I updated the status line in `## Main results`.
3. **Order.** `evidence/order.txt` (253 modules) is the issued order plus the four helpers.
4. The owned file now imports `AdaptiveCPA.Games` (with `Hybrid`, `Handler` and `AdaptiveSecurity`)
   for the public transport lemmas. `Simulation.lean` sees them transitively.

## Payload

- `REPORT.md` and `patches/` (the whole `format-patch` series from the base);
- `src/`, the five files at their repository paths;
- `evidence/`:
  - `inputs/`: the pack, the exchange README and `policy.md`;
  - `logs/`: preflight, cache store, cache get, packages, probe, bootstrap, sweep, admissions,
    axioms, escalation probes, seal censuses, seals, controls, unfold scan, lint, patch replay
    and `dev/`;
  - `seal/`, `probes/`, `tools/`;
  - `order.txt`, `bootstrap-order.txt`;
- `SHA256SUMS` over the payload.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/fills/nm-cca2/issued-r1/brief.md =====

# Claude fill · under CCA2, secrecy and non-malleability coincide (`indSecure_cca2_iff_nmSecure_cca2`)

**Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4` (the merge of #293).
**Unit** `nm-cca2`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in
that commit's `lake-manifest.json`.

Prove the admitted theorem of [PS10, Theorem 175.9] in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean`: for a fixed-length public-key
scheme, IND-CCA2 security (Definition 171.5) and CCA2 non-malleability (Definition 172.6) are equivalent. The
statement passed its Gate 06 audit (#232).

**This fill runs in parallel with the `dl-consolidation` job**, which moves the generic lemmas of duplication-ledger
rows DL-30 to DL-34. Read the duplication rule below.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/nm-cca2` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/nm-cca2/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed files;
  - `evidence/`.
- Commit as `fill nm-cca2: checkpoint N` and `fill nm-cca2: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2 := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.
- **`NMSecure atk`:** for all `A`, `q`, `ℓ` and `D`, the advantage between `nmGame atk A q ℓ D false` and `true`
  is negligible.
- **`nmGame`:** the adversary runs against the IND oracles `indImpl atk b` through `nmCodec n ℓ` and outputs `ℓ`
  ciphertexts. They are decrypted by `nmOutput`, with `nmDecrypt` giving `⊥ = zeroBits` on a copy of the recorded
  challenge, and `D` judges the result.
- **`INDSecure`:** defined in `PublicKey/OracleSecurity.lean` (`indGame`, `INDSecure_iff`).

## Published interfaces

| Interface | Provider |
|---|---|
| `nmCodec_*`, `nthCt_eq`, `nmDecrypt_eq`, `nmDecrypt_challenge`, `nmOutput_eq`, `nmGame_eq`, `NMSecure_iff` | `PublicKey/NonMalleability/Indistinguishability.lean` (owned; the statement-phase readers) |
| `FixedLengthPKScheme` fields (`correct`, `enc_length`, `gen_uniform`, …), `inLens_*`, `outLens_*`, `indSpec_*` (incl. `_decDom`, `_challengeDom/_Rng`), `indImpl_dec`, `indImpl_dec_onSpec`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indImpl_dec_cca2_challenge`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `FixedLengthScheme.decAnswer` and its readers | `PrivateKey/OracleSecurity.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, T4 `exists_toOracleAdversary_of_bitCodec`, and the `PolyHandler` / `InteractiveHandler` readers | `Games/Efficiency.lean` |
| `bitCodec_*`, `decodeBitMove`, `simulate` equations, `OracleComp` laws, `advantage_eq`, `accept_eq` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `distinguisherL_eq` | `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean` |
| Worked models of T2 handlers with forwarded oracles, eager coins and cast transport | `PublicKey/AdaptiveCPA/`, `PublicKey/BitwiseCPA/`, `PrivateKey/OracleFromPRF/` (models only; see the duplication rule) |

## Proof route and checkpoints

The target's docstring sketch is authoritative.

1. **(⇒) IND-CCA2 ⇒ NM-CCA2.** Given an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`,
   build an IND adversary with a T2 handler:
   - `advIn = pk`; it forwards `A`'s `Dec` and challenge queries;
   - in finalization (`finCall = ℓ`) it asks CCA2's `Dec` on each of `A`'s ciphertexts, then runs `D` on the
     answers, for total budget `q + ℓ`;
   - the advice is carried through `z` with the `NUPPT` closure lemmas.

   Show that the IND game at each `b` equals `NM_b`, so the advantage is equal. The key facts:
   - CCA2's `Dec` refuses the recorded challenge with the same `zeroBits` that `nmDecrypt` gives a copy
     (`indImpl_dec_cca2_challenge`, `nmDecrypt_challenge`);
   - it decrypts every other ciphertext as `nmDecrypt` does;
   - with no challenge asked, both decrypt everything.

   Send checkpoint 1.
2. **(⇐) NM-CCA2 ⇒ IND-CCA2.** Given an IND adversary `A` with guess `g`:
   - The NM adversary runs `A` and outputs `ℓ = 2` fresh encryptions, of `g^{msgLen}` and `(¬g)^{msgLen}`, under
     `pk` with its own seed coins.
   - The two plaintexts differ for `msgLen(n) > 0`, so by `correct` at most one ciphertext is the challenge.
   - The distinguisher reads `g` from the first decryption if it is valid, and from the second (negated)
     otherwise.

   Show that the NM advantage equals the IND advantage. At `msgLen(n) = 0` both IND games coincide, so the
   advantage is 0.

   Send checkpoint 2.
3. **Assemble the equivalence**, with the polynomial budgets of each direction.

   Send the final delivery.

Check the edge cases:
- budget 0;
- `ℓ = 0`;
- `msgLen(n) = 0`;
- no challenge asked;
- repeated challenges;
- `A` outputting the challenge itself, or a malformed or invalid ciphertext;
- the codec's timeout output, in both directions.

## Scope and proof discipline

- **Owned file.** You own `NonMalleability/Indistinguishability.lean`: replace the proof body and add helpers.
- **Helper modules.** Helper modules are permitted under `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/`.
  The owned file imports them precisely. It gets a `## Contents` list if it becomes a facade, and its status line
  for the target is updated.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file, `NonMalleability/Simulation.lean` included. If a lemma belongs in an
  existing file, put it in your helper module and list it in `REPORT.md` as a promotion request. If a reader of
  another file's definition is missing, escalate: record the exact obligation and the reader you need, and push
  a checkpoint.
- **Duplication (binding).**
  - Do not copy public lemmas: import them where they are at the issue base. The maintainer re-points them at
    landing if the consolidation has moved them.
  - Do not copy private lemmas from `AdaptiveCPA/`, `BitwiseCPA/` or `OracleFromPRF/`. These include the
    round-input readers `rU`…`rCnt`, `impl_of_ret` and `ofFn_padFin_eq_padL`. If your handler needs one of
    them, re-derive it from the published `InteractiveHandler` and `padFin` readers in your helper module,
    disclose it in `REPORT.md` as **"DL-30–34 overlap: <item>"**, and keep its statement in the general form. The
    maintainer replaces it with the promoted lemma at landing.
  - Any other generic probability, simulation or list fact goes on your promotion list. Grep first.
- **Statements.** You may edit the target's sketch to describe the delivered proof. Preserve the statement, every
  other declaration, the statement prose and the global simp attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial (policy §3).
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (249 modules) and the narrow `roots.txt` per the addendum. Check one
  module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules before
  their consumers.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare the `sorry` warnings with
  `base-sorries.txt`: the only change must be the removal of `indSecure_cca2_iff_nmSecure_cca2`.
- **Axioms.**
  - Print the axioms of the target. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
  - Print them for `simNMSecure_cpa_iff_nmSecure_cpa` and report exactly what it prints. It still depends on the
    two `Simulation.lean` targets.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls and
    paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
  - Report the seal both with `PolyExpr.eval` excluded as notation and with it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edit;
  - the new declarations;
  - the promotion and reader requests, and every "DL-30–34 overlap" item;
  - the evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | Open (deferred) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | Open (deferred) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | Open (deferred) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | Open (deferred) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | Open (deferred) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | Open (deferred) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-malleable encryption

[PS10, Definition 172.6] and Theorem 175.9, over the public-key experiment of Definition 171.5
(`Encryption/PublicKey/OracleSecurity.lean`).

**The experiment** `NM_b(Π, A, n)`: `(pk, sk) ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁}(1^n, pk)`;
`c ← Enc_pk(m_b)`; `(c'₁, …, c'_ℓ) ← A^{O₂}(c, state)`; output `(m'₁, …, m'_ℓ)` with
`m'_i = ⊥` if `c'_i = c` and `m'_i = Dec_sk(c'_i)` otherwise. The scheme is non-malleable when,
for every adversary `A` and distinguisher `D`, `D` tells `NM_0` from `NM_1` with negligible
advantage.

**Its encoding.** The oracles and the phases are those of Definition 171.5 (`indImpl`). The
adversary's final output is `ℓ(n)` ciphertexts of `ctLen(n)` bits. Each decryption is encoded as
`Dec`'s oracle answers are (`decAnswer`): a validity flag and the message, all-`false` for `⊥`.
`D` receives their concatenation.

**Source notes.**
- The definition writes private-key notation (`k ← Gen(1^n)`, `Dec_k`) for a public-key scheme;
  the public-key reading is taken (inventory Def-172.6).
- The source leaves the oracles `O₁, O₂` open; they are parametrized by the attack, as in
  Definition 171.5. Theorem 175.9's "CCA2 non-malleability" is the CCA2 instance.
- The adversary chooses `m₀, m₁`, so the definition's closing "for all `m₀, m₁ ∈ {0,1}^n`" is
  dropped. At CPA this is [PSV06, Definition 3], by the source's authors (ruling of 2026-11-05):
  the adversary picks `m₀, m₁` after seeing `pk`, `D` sees only the decryptions, and a copy of
  the challenge and an invalid ciphertext both decrypt to `⊥`.
- [PSV07, Definition 3] (IND-NME′) allows many challenges and distinguishes `COPY` from
  an invalid ciphertext's `⊥`; it is not literally the many-message form of this encoding.
  For the one-challenge security comparison, the complementary-pair copy-flag export argument
  is in the maintainer's sketch of `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa`
  (`SimNonMalleable.lean`). It separates `L = msgLen(n) = 0`, when the two experiments
  coincide, from `L > 0`, when the complementary plaintexts differ and their encrypted pair
  exports each copy flag. This is a security comparison of the one-challenge conventions;
  no many-challenge bridge is claimed here.
- Definition 173.7 and Theorem 174.8 follow [PSV07] (same ruling), in
  `Encryption/PublicKey/NonMalleability/Simulation.lean`.

## Contents

* `NonMalleability.Indistinguishability.Forward`: the forwarding handler and the log readers.
* `NonMalleability.Indistinguishability.Decrypt`: the reduction (⇒), whose finalization decrypts
  the adversary's ciphertexts and runs the distinguisher.
* `NonMalleability.Indistinguishability.Encrypt`: the reduction (⇐), whose finalization encrypts
  the guess and its negation, and the distinguisher that reads the guess back.

## Main definitions

* `FixedLengthPKScheme.nmGame`, `FixedLengthPKScheme.NMSecure`: [PS10, Definition 172.6].

## Main results

* `FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2`: the
  two directions of Thm 175.9.
* `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2` (Thm 175.9, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.5 and §7.1.7, Definition 172.6 and Theorem 175.9 (book pp. 172–175).
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 3.
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The codec of the adversary: the oracles of Definition 171.5, and a final output of `ℓ`
ciphertexts. -/
def nmCodec (n ℓ : ℕ) : MachineCodec (S.indSpec n) (Fin (ℓ * S.ctLen.eval n) → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The non-malleability codec uses `decodeBitMove` with the scheme's oracle lengths and an
output of `ℓ * ctLen(n)` bits. -/
theorem nmCodec_decodeMove (n ℓ : ℕ) (w : List Bool) :
    (S.nmCodec n ℓ).decodeMove w =
      decodeBitMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w

/-- The non-malleability codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem nmCodec_encodeEntry (n ℓ : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.nmCodec n ℓ).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) e

/-- When its query budget expires, the non-malleability codec returns `zeroBits (ℓ * ctLen(n))`.
-/
theorem nmCodec_timeout (n ℓ : ℕ) :
    (S.nmCodec n ℓ).timeout = zeroBits (ℓ * S.ctLen.eval n) :=
  bitCodec_timeout (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The `i`-th of the `ℓ` ciphertexts in the adversary's output. -/
def nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (finProdFinEquiv (i, j))

/-- Ciphertext `i` is the block whose bit `j` is output bit `finProdFinEquiv (i, j)`. -/
theorem nthCt_eq {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    S.nthCt w i = fun j => w (finProdFinEquiv (i, j)) := rfl

/-- The decryption `m'` of an output ciphertext `c'` against the recorded challenge `s`: `⊥` if
`c'` is the challenge, and `Dec_sk(c')` otherwise, encoded as `Dec`'s oracle answers are. -/
def nmDecrypt {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) : Fin (S.msgLen.eval n + 1) → Bool :=
  if s = some c' then zeroBits _
  else FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c'))))

/-- An output ciphertext decrypts to all-false bits when it copies the challenge, and to the
encoded decryption answer otherwise [PS10, Definition 172.6]. -/
theorem nmDecrypt_eq {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk s c' =
      if s = some c' then zeroBits (S.msgLen.eval n + 1)
      else FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c')))) := rfl

/-- The output of `NM_b`: the concatenated decryptions of the adversary's `ℓ` ciphertexts. -/
def nmOutput {n ℓ : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (w : Fin (ℓ * S.ctLen.eval n) → Bool) : List Bool :=
  (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten

/-- The non-malleability output flattens the encoded decryptions of all `ℓ` output blocks. -/
theorem nmOutput_eq {n ℓ : ℕ} (sk : List Bool)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) (w : Fin (ℓ * S.ctLen.eval n) → Bool) :
    S.nmOutput sk s w =
      (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten := rfl

/-- **The experiment `NM_b(Π, A, n)`** [PS10, Definition 172.6] for the attack `atk`, with query
budget `q` and `ℓ` output ciphertexts, followed by the distinguisher `D`: sample the keys and the
coins, run `A` on `pk` against the oracles of Definition 171.5, decrypt its output (`⊥` on a copy
of the challenge), and output `D`'s verdict on the decryptions. -/
noncomputable def nmGame (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (D.Coins n)).bind fun ρ =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res =>
      .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)

/-- The non-malleability experiment samples keys and both machines' coins, runs the adversary
against the IND oracles, and applies the distinguisher to its decrypted output
[PS10, Definition 172.6]. -/
theorem nmGame_eq (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    S.nmGame atk A q ℓ D b n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (ProbComp.sample (D.Coins n)).bind fun ρ =>
      (simulate
          (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
          (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res =>
          .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) :=
  rfl

/-- **Non-malleability** [PS10, Definition 172.6] under the attack `atk`: for every non-uniform
PPT adversary `A`, every polynomial query budget `q` and number `ℓ` of output ciphertexts, and
every non-uniform PPT distinguisher `D`, `D`'s advantage between `NM_0` and `NM_1` is
negligible. -/
def NMSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
      (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n

/-- Non-malleability holds exactly when every adversary, polynomial query and output budgets,
and distinguisher have a negligible bound on the two games' advantage
[PS10, Definition 172.6]. -/
theorem NMSecure_iff (atk : Attack) :
    S.NMSecure atk ↔
      ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
          (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n := Iff.rfl

/-- A copy of the challenge decrypts to `⊥`. -/
theorem nmDecrypt_challenge {n : ℕ} (sk : List Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk (some c) c = zeroBits _ := by
  simp [nmDecrypt]

/-! ### Proof of Theorem 175.9 -/

section Proof

open AdaptiveCPA NMCCA2 ProbComp ChallengeSim

/-- The non-malleability codec is the bit codec of the oracles of Definition 171.5 with
`ℓ · ctLen(n)` output bits: `S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ · ctLen(n))`. -/
theorem nmCodec_eq_bitCodec (n ℓ : ℕ) :
    S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) := rfl

/-- Ciphertext `i` of an output string is its `i`-th block of `ctLen(n)` bits:
`⟦S.nthCt w i⟧ = (⟦w⟧.drop (i · ctLen(n))).take ctLen(n)`. -/
theorem ofFn_nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    List.ofFn (S.nthCt w i) =
      ((List.ofFn w).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
  have hle : (i : ℕ) * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [finProdFinEquiv_apply_val]
    show j + S.ctLen.eval n * i = i * S.ctLen.eval n + j
    rw [Nat.mul_comm]
    omega

/-! ### (⇒) The CCA2 adversary built from a non-malleability adversary -/

/-- **The CCA2 decryption oracle on T2's codec answers as the experiment decrypts:** a query `x`
in state `st` is answered `⟦S.nmDecrypt sk st c⟧`, `c` the query read as a ciphertext, and the
state is kept.

**Proof sketch.** `castImpl_eq` and the decryption reader with its answer cast
(`indImpl_dec_onSpec_cast`); under CCA2 `Dec` is open (`decOpen_cca2`), so it refuses exactly
the recorded challenge with `⊥ = 0`, as `nmDecrypt` does (`nmDecrypt_eq`); the casts keep the
strings (`ofFn_cast`, `ofFn_zeroBits`, `outLens_zero`). -/
private theorem castImpl_indImpl_dec (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (S.indImpl .cca2 b n pk sk) 0 x st =
      .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
        (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
  rw [castImpl_eq, S.indImpl_dec_onSpec_cast, FixedLengthScheme.decOpen_cca2, Bool.true_and,
    S.nmDecrypt_eq]
  by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
  · rw [if_neg (by rw [decide_eq_true hs, Bool.not_true]; exact Bool.false_ne_true), if_pos hs,
      OracleComp.pure_bind]
    dsimp only
    rw [ofFn_zeroBits, ofFn_zeroBits, S.outLens_zero]
  · rw [if_pos (by rw [decide_eq_false hs, Bool.not_false]), if_neg hs, OracleComp.pure_bind]
    dsimp only
    rw [ofFn_cast (S.outLens_zero n).symm]

/-- **The reduction's queries are the experiment's ciphertexts:** block `i < ℓ(n)` of the
adversary's output `a`, read as a decryption query, is ciphertext `i` of `a`.

**Proof sketch.** Both are the bits `[i · ctLen(n), (i + 1) · ctLen(n))` of `⟦a⟧`
(`ofFn_nthCt`, `ofFn_padFin_eq_take`, `ofFn_cast`); they are equal as strings
(`List.ofFn_injective`). -/
private theorem decBlock_eq_nthCt (ℓ : PolyExpr) (n : ℕ)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (i : ℕ) (hi : i < ℓ.eval n) :
    cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn (decBlock S n a i))) =
      S.nthCt (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) ⟨i, hi⟩ := by
  have hct : (acDin S 0).eval n = S.ctLen.eval n := by rw [acDin_zero]
  have hin : S.inLens n 0 = S.ctLen.eval n := S.inLens_zero n
  have ha : (List.ofFn a).length = ℓ.eval n * S.ctLen.eval n := by
    rw [List.length_ofFn, PolyExpr.eval_mul]
  have hle : i * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ.eval n * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    exact this
  have hblk : List.ofFn (decBlock S n a i) =
      ((List.ofFn a).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
    rw [decBlock_eq, ofFn_padFin_eq_take, hct,
      List.take_append_of_le_length (by rw [List.length_drop, ha]; omega)]
  apply List.ofFn_injective
  rw [ofFn_cast hin, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hct, hin]), hblk,
    ofFn_nthCt, GGMRed.ofFn_padFin_of_length ha]

/-- **The reduction's collected answers are the experiment's output:** the concatenated answers
of the CCA2 decryption oracle on the `ℓ(n)` blocks of `a`, in state `st`, are
`S.nmOutput sk st a`.

**Proof sketch.** Answer `i` is `⟦nmDecrypt sk st (block i)⟧` (`castImpl_indImpl_dec`, read at
its width by `acDout_zero`), and block `i` is ciphertext `i` (`decBlock_eq_nthCt`); compare the
two lists entrywise (`nmOutput_eq`). -/
private theorem decAnswers_eq_nmOutput (ℓ : PolyExpr) (n : ℕ) (sk : List Bool)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    ((List.range (ℓ.eval n)).map fun i => List.ofFn (padFin ((acDout S 0).eval n) (List.ofFn
        (S.nmDecrypt sk st (cast (S.indSpec_decDom n) (padFin (S.inLens n 0)
          (List.ofFn (decBlock S n a i)))))))).flatten =
      S.nmOutput sk st (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) := by
  have hout : (acDout S 0).eval n = S.msgLen.eval n + 1 := by
    rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const]
  rw [nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn])
    fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hout]),
    decBlock_eq_nthCt S ℓ n a i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]

/-- **The reduction's game is the non-malleability experiment.** Let `B` be T2's machine for the
handler `decHandler S ℓ D` (with its coin bijection `φ` at `n`) and `B'` the machine `B` with
`D`'s advice hard-wired (`hB'`, coins identified by `hc`). Then `B'`'s CCA2 game `Ind_b` and the
experiment `NM_b` for `A` and `D` accept with the same probability.

**Proof sketch.** Fix the keys. `B'`'s coins are the handler's seed (`D`'s coins, `e`) and `A`'s
coins (`φ`, `expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`). For fixed coins,
transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards (`simulate_decHandler_impl`),
so the run is `A`'s run against the CCA2 oracles followed by the finalization in the final
state (`simulate_bind`), which decrypts the `ℓ` ciphertexts with the state kept
(`simulate_decHandler_finish`, `castImpl_indImpl_dec`) and outputs `D`'s verdict on
`S.nmOutput sk st a` (`decAnswers_eq_nmOutput`). That is `NM_b`'s output, after transporting
`A`'s run back to the experiment's codec (`nmCodec_eq_bitCodec`). -/
private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n : ℕ)
    (φ : (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((decHandler S ℓ D).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((ℓ.mul S.ctLen).eval n)) n (q.eval n) ((decHandler S ℓ D).advInput n z ω) r)
          ((decHandler S ℓ D).init n)).bind
          (fun res => (decHandler S ℓ D).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((decHandler S ℓ D).outLen.eval n)) n
          (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n)
          z (φ (ω, r)))
    (hc : B.coins = B'.coins)
    (hB' : ∀ (Q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn (S.indCodec n) n Q x (NUPPT.coinsCongr hc n r) =
        B.toCompOn (S.indCodec n) n Q (pairEncode x (D.advice n)) r)
    (b : Bool) :
    accept (S.indGame .cca2 B'
        (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n) b n) =
      accept (S.nmGame .cca2 A (q.eval n) (ℓ.eval n) D b n) := by
  have hd1 : (decHandler S ℓ D).outLen.eval n = 1 := by
    rw [decHandler_outLen, PolyExpr.eval_const]
  have hdα : (ℓ.mul S.ctLen).eval n = ℓ.eval n * S.ctLen.eval n := PolyExpr.eval_mul _ _ _
  let e : D.Coins n ≃ (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) :=
    NUPPT.coinsEquivPoly (decHandler_seedLen S ℓ D).symm n
  rw [accept_eq, accept_eq, S.indGame_eq, S.nmGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  conv_lhs => rw [prob_bind, ← expect_sample_equiv (φ.trans (NUPPT.coinsCongr hc n)),
    expect_sample_prod, expect_sample_comm]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  conv_lhs => rw [← expect_sample_equiv e]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [Equiv.trans_apply, hB', prob_bind, indCodec_eq_bitCodec, h1]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
  rw [← hφ, decHandler_advInput, pairFstD_pairEncode, simulate_decHandler_impl,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]
  rw [simulate_bind, expect_bind]
  simp only [simulate_decHandler_finish S ℓ D n _ _ _ _ _ _ (castImpl_indImpl_dec S b n _ _),
    expect_pure]
  -- The experiment's side: transport `A`'s run to T2's codec.
  have h2 : (fun res : (Fin (ℓ.eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hdα _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the verdict on the collected answers is `D`'s verdict on `NM_b`'s output.
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hd1]), List.headD_cons,
    pairSndD_pairEncode, decAnswers_eq_nmOutput, NUPPT.coinsEquivPoly_ofFn,
    ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-- **(⇒) of Theorem 175.9: CCA2 security implies CCA2 non-malleability** [PS10, Theorem 175.9].

**Proof sketch.** Given `A` (budget `q`, `ℓ` ciphertexts) and `D`, T2
(`Games.exists_interactiveHandlerMachine`) makes the handler `decHandler S ℓ D` a machine `B`, and
`exists_withAdviceOn` hard-wires `D`'s advice into it (`B'`). `B'`'s budget is
`q · 1 + ℓ`, a polynomial; CCA2 security gives a negligible bound on `B'`'s advantage, which at
every `n` equals the advantage of `D` between `NM_0` and `NM_1` (`accept_indGame_decRed`). -/
theorem nmSecure_cca2_of_indSecure_cca2 (h : S.INDSecure .cca2) : S.NMSecure .cca2 := by
  rw [NMSecure_iff]
  intro A q ℓ D
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (ℓ.mul S.ctLen) (decHandler S ℓ D)
  obtain ⟨B', hc, hB'⟩ := exists_withAdviceOn B D.advice D.adv D.advice_length
  obtain ⟨ε, hε, hbound⟩ := (S.INDSecure_iff .cca2).1 h B'
    ((q.mul (decHandler S ℓ D).perCall).add (decHandler S ℓ D).finCall)
  refine ⟨ε, hε, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have key := fun b => accept_indGame_decRed S A D B B' q ℓ n φ hφ hc
    (fun Q x r => hB' n (S.indCodec n) Q x r) b
  have hn := hbound n
  rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
  rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
  exact hn

/-! ### (⇐) The non-malleability adversary built from a CCA2 adversary -/

/-- A two-block concatenation at a width only propositionally equal to `2`: for `k = 2`,
`(List.ofFn f).flatten = f 0 ++ f 1` (`OneWay.flatten_ofFn_two` after substituting `k`). -/
private theorem flatten_ofFn_two {k : ℕ} (hk : k = 2) (f : Fin k → List Bool) :
    (List.ofFn f).flatten = f ⟨0, by omega⟩ ++ f ⟨1, by omega⟩ := by
  subst hk
  exact OneWay.flatten_ofFn_two f

/-- **The distinguisher recovers the guess.** Let the reduction output the ciphertexts
`c₁ = encCt … g true` (an encryption of `g^m`) and `c₂ = encCt … g false` (of `(¬g)^m`) under a
generated key, with `m = msgLen(n) > 0`. Then for every recorded challenge `st`, the distinguisher's
verdict on the experiment's output `S.nmOutput sk st (c₁ ‖ c₂)` is `g`.

**Proof sketch.** By correctness `c₁` decrypts to `g^m` and `c₂` to `(¬g)^m` (`S.correct`, with
`S.enc_length` for the padding), so `c₁ ≠ c₂` (their messages differ at bit `0`), and `st` copies
at most one of them. If `st ≠ some c₁` the first decryption is valid (`guessBit_valid`); otherwise
the first is `⊥` and the second valid (`guessBit_refused`). -/
private theorem guessDist_nmOutput (n : ℕ) (hm : 0 < S.msgLen.eval n) (rg : S.gen.Coins n)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g : Bool)
    (st : Option (Fin (S.ctLen.eval n) → Bool)) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) st
      (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n)
        (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g true ++
          encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g false))) ρ = g := by
  set pk := pairFstD (S.gen.runAt n [] rg)
  set sk := pairSndD (S.gen.runAt n [] rg)
  set c₁ := encCt S n pk ω g true
  set c₂ := encCt S n pk ω g false
  have h2 : (PolyExpr.const 2).eval n = 2 := PolyExpr.eval_const _ _
  -- The honest ciphertexts and their decryptions.
  have hc : ∀ β, encCt S n pk ω g β = S.enc.runAt n (pairEncode pk (List.ofFn
      fun _ : Fin (S.msgLen.eval n) => if β then g else !g)) (encTape S n ω β) := fun β => by
    rw [encCt_eq, EnsembleLemmas.padL_eq, List.take_append_of_le_length (by rw [S.enc_length]),
      List.take_of_length_le (by rw [S.enc_length])]
  have hlen : ∀ β, (encCt S n pk ω g β).length = S.ctLen.eval n := fun β => by
    rw [encCt_eq, EnsembleLemmas.length_padL]
  have hdec : ∀ β, decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (encCt S n pk ω g β))) =
      some fun _ => if β then g else !g := fun β => by
    rw [hc]
    exact S.correct n _ rg (encTape S n ω β)
  -- The two blocks of the output.
  set W := padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) (c₁ ++ c₂)
  have hW : List.ofFn W = c₁ ++ c₂ := GGMRed.ofFn_padFin_of_length (by
    rw [List.length_append, hlen, hlen, h2]; omega)
  have hblk : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool), (i : ℕ) = (if β then 0 else 1) →
      List.ofFn (S.nthCt W i) = encCt S n pk ω g β := by
    intro i β hi
    rw [ofFn_nthCt, hW, hi]
    cases β
    · rw [if_neg Bool.false_ne_true, Nat.one_mul, List.drop_left' (hlen true),
        List.take_of_length_le (by rw [hlen])]
    · rw [if_pos rfl, Nat.zero_mul, List.drop_zero, List.take_left' (hlen true)]
  have hdecB : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool),
      (i : ℕ) = (if β then 0 else 1) →
      decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn (S.nthCt W i)))) =
        some fun _ => if β then g else !g := fun i β hi => by
    rw [hblk i β hi]
    exact hdec β
  -- The output is the two decryptions.
  have i₀ : (0 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have i₁ : (1 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have hout : S.nmOutput sk st W = List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨0, i₀⟩)) ++
      List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨1, i₁⟩)) := by
    rw [nmOutput_eq]
    exact flatten_ofFn_two h2 _
  -- The two ciphertexts differ.
  have hne : S.nthCt W ⟨0, i₀⟩ ≠ S.nthCt W ⟨1, i₁⟩ := by
    intro h
    have e := (hdecB ⟨0, i₀⟩ true rfl).symm.trans (h ▸ hdecB ⟨1, i₁⟩ false rfl)
    have := congrFun (Option.some.inj e) ⟨0, hm⟩
    simp at this
  rw [guessDist_distinguisherL, hout]
  by_cases hs : st = some (S.nthCt W ⟨0, i₀⟩)
  · have hs' : st ≠ some (S.nthCt W ⟨1, i₁⟩) := fun h => hne (Option.some.inj (hs.symm.trans h))
    rw [S.nmDecrypt_eq, S.nmDecrypt_eq, if_pos hs, if_neg hs', hdecB ⟨1, i₁⟩ false rfl]
    simpa only [if_neg Bool.false_ne_true] using guessBit_refused hm g
  · rw [S.nmDecrypt_eq, if_neg hs, hdecB ⟨0, i₀⟩ true rfl]
    simpa only [if_pos rfl] using guessBit_valid hm g _

/-- **The reduction's experiment is the CCA2 game.** Let `B` be T2's machine for the handler
`encHandler S` (with its coin bijection `φ` at `n`), and `msgLen(n) > 0`. Then `B`'s experiment
`NM_b` with two output ciphertexts and the distinguisher `guessDist` accepts with the probability
of `A`'s CCA2 game `Ind_b`.

**Proof sketch.** Fix the keys. `B`'s coins are the handler's seed `ω` and `A`'s coins `r` (`φ`,
`expect_sample_equiv`, `expect_sample_prod`). For fixed `ω`, `r` and the distinguisher's coins,
transport `B`'s run to T2's codec (`nmCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards
(`simulate_encHandler_impl`), so the run is `A`'s run against the CCA2 oracles, after which the
finalization outputs the two ciphertexts and keeps the recorded challenge (`simulate_bind`,
`encHandler_finish`). Whatever that challenge is, `guessDist` outputs `A`'s guess
(`guessDist_nmOutput`). Transport `A`'s run back to the game's codec (`indCodec_eq_bitCodec`). The
result does not depend on `ω` or on the distinguisher's coins (`expect_const`). -/
private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
    (hm : 0 < S.msgLen.eval n)
    (φ : (Fin ((encHandler S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((encHandler S).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((encHandler S).advInput n z ω) r)
          ((encHandler S).init n)).bind
          (fun res => (encHandler S).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((encHandler S).outLen.eval n)) n
          (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n) z (φ (ω, r)))
    (b : Bool) :
    accept (S.nmGame .cca2 B
        (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n)
        ((PolyExpr.const 2).eval n) guessDist b n) =
      accept (S.indGame .cca2 A (q.eval n) b n) := by
  have hd1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
  have hd2 : (encHandler S).outLen.eval n = (PolyExpr.const 2).eval n * S.ctLen.eval n := by
    rw [encHandler_outLen, PolyExpr.eval_add, PolyExpr.eval_const]
    omega
  rw [accept_eq, accept_eq, S.nmGame_eq, S.indGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod]
  refine (congrArg _ (funext fun ω => ?_)).trans (expect_const _ _)
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine (congrArg _ (funext fun ρ => ?_)).trans (expect_const _ _)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h2 : (fun res : (Fin ((PolyExpr.const 2).eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (guessDist.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
        else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd2 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
      else 0)).symm.trans ?_
  rw [← hφ, encHandler_advInput, simulate_encHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, encHandler_finish]
  rw [simulate_bind, expect_bind]
  simp only [simulate_pure, expect_pure]
  -- The game's side: transport `A`'s run to T2's codec.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [prob_bind, indCodec_eq_bitCodec, h1]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the distinguisher outputs `A`'s guess.
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false)) =
      encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  dsimp only
  rw [hw, guessDist_nmOutput S n hm]

/-- **(⇐) of Theorem 175.9: CCA2 non-malleability implies CCA2 security**
[PS10, Theorem 175.9].

**Proof sketch.** Given `A` with budget `q`, T2 (`Games.exists_interactiveHandlerMachine`) makes
the handler `encHandler S` a machine `B`, with budget `q · 1 + 0`. Non-malleability for `B`, two
output ciphertexts and `guessDist` gives a negligible bound. At `n` with `msgLen(n) > 0`, `A`'s
CCA2 advantage equals that experiment's advantage (`accept_nmGame_encRed`). At `msgLen(n) = 0` the
two CCA2 games coincide (`indImpl_eq_of_msgLen_eq_zero`), so `A`'s advantage is `0`. -/
theorem indSecure_cca2_of_nmSecure_cca2 (h : S.NMSecure .cca2) : S.INDSecure .cca2 := by
  rw [INDSecure_iff]
  intro A q
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (.const 1) (encHandler S)
  obtain ⟨ε, hε, hbound⟩ := (S.NMSecure_iff .cca2).1 h B
    ((q.mul (encHandler S).perCall).add (encHandler S).finCall) (.const 2) guessDist
  refine ⟨ε, hε, fun n => ?_⟩
  have hn := hbound n
  by_cases hm : S.msgLen.eval n = 0
  · have hg : S.indGame .cca2 A (q.eval n) false n = S.indGame .cca2 A (q.eval n) true n := by
      rw [S.indGame_eq, S.indGame_eq]
      simp only [indImpl_eq_of_msgLen_eq_zero S .cca2 n _ _ hm]
    rw [hg, advantage_self]
    exact (advantage_nonneg _ _).trans hn
  · obtain ⟨φ, hφ⟩ := hB n
    have key := fun b => accept_nmGame_encRed S A B q n (Nat.pos_of_ne_zero hm) φ hφ b
    rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
    rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
    exact hn

end Proof

/-- **Theorem 175.9: under CCA2, secrecy and non-malleability coincide** [PS10, Theorem 175.9].

**Proof sketch** (the source's, made explicit; the delivered proof).
1. (⇒) Given an NM adversary `A` with `ℓ` ciphertexts and a distinguisher `D`, the IND
   adversary runs `A` on `pk`, forwarding every query to its own oracles, then asks CCA2's `Dec`
   for each of `A`'s ciphertexts. `Dec` refuses the recorded challenge with the same `⊥ = 0` that
   `NM` assigns to its copies and decrypts every other ciphertext as `NM` does
   (`indImpl_dec_cca2_challenge`, `nmDecrypt_challenge`), so the answers are exactly `NM_b`'s
   output. It runs `D` on them and outputs `D`'s verdict. T2
   (`Games.exists_interactiveHandlerMachine`) makes this a machine, for the forwarding handler
   `NMCCA2.decHandler`: `advIn = pk`, one outer call per query, and `finCall = ℓ` in
   finalization before running `D`, for total budget `q + ℓ`. `D`'s advice is carried through
   `z = ⟨pk, α⟩` and hard-wired afterwards (`NMCCA2.exists_withAdviceOn`, from the public
   `exists_withAdvice`/`exists_comp` closure lemmas). The two games accept with the same
   probability at every `n` (`nmSecure_cca2_of_indSecure_cca2`).
2. (⇐) Given an IND adversary `A` with guess `g`, the NM adversary runs `A`, forwarding its
   queries, and outputs fresh encryptions of `g^{msgLen}` and `(¬g)^{msgLen}` under `pk` with its
   own seed (`NMCCA2.encHandler`). The two plaintexts differ, so by correctness at most one of
   the two ciphertexts is the challenge. The distinguisher (`NMCCA2.guessDist`) reads `g` from
   the first if it decrypts, and from the second otherwise. Same advantage; at `msgLen(n) = 0`
   the two CCA2 games coincide and the advantage is `0`
   (`indSecure_cca2_of_nmSecure_cca2`).

The source's sketch argues the contrapositives: an NM break yields a related ciphertext that
`Dec` decrypts, and an IND break lets the adversary decrypt and re-encrypt a related message. -/
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2 := by
  exact ⟨S.nmSecure_cca2_of_indSecure_cca2, S.indSecure_cca2_of_nmSecure_cca2⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers and log readers

Both reductions of [PS10, Theorem 175.9] run the adversary once against the reduction's own
oracles: every query is **forwarded** unchanged to the outer oracle of the same index, and only
the finalization differs. This file builds that handler once, generically in the oracle lengths
(`fwdHandler`), as a `Games.InteractiveHandler` with one outer call per inner query and an empty
state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its answers are
the outer oracle's (`fwdHandler_impl`), so simulating it is running the adversary against the
outer oracles (`simulate_fwdHandler_impl`).

It also provides the readers of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (`finU`,
`finZ`, `finW`, `finA`, `finL`) and of an encoded outer log: `logEmit G L` concatenates `G` of the
successive suffixes of the nested log `L`, is polynomial-time for polynomial-time `G`
(`polyTimeComputable_logEmit`), and on an encoded log is the concatenation of `G`'s values on the
entries (`logEmit_encodeLog`).

## Main definitions

* `NMCCA2.fwdHandler`: the forwarding handler with a given finalization.
* `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL`: the fields of a finalization input.
* `NMCCA2.logEmit`: concatenated readings of the suffixes of an encoded log.

## Main results

* `NMCCA2.fwdHandler_impl`, `NMCCA2.simulate_fwdHandler_impl`: forwarding.
* `NMCCA2.polyTimeComputable_logEmit`, `NMCCA2.logEmit_encodeLog`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable {k : ℕ}

/-! ### Readers of a round input -/

/-- The state `s` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rState (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i` of a round input. -/
private def rIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x` of a round input. -/
private def rQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of the call so far. -/
private def rLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The outer answer `y` recorded in a one-entry log `⟨⟨1^j, ⟨x, y⟩⟩, []⟩`. -/
private def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rLog w)))

/-- The fields of a round input (DL-30–34 overlap: the round-input readers). -/
private theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rState (InteractiveHandler.input n z ω s i x L) = s ∧
      rIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
      rQuery (InteractiveHandler.input n z ω s i x L) = x ∧
      rLog (InteractiveHandler.input n z ω s i x L) = L := by
  simp only [InteractiveHandler.input_eq, rState, rIdx, rQuery, rLog, pairFstD_pairEncode,
    pairSndD_pairEncode, and_self]

/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
with the outer answer `y` in the log, return `y` and keep the state. -/
private def fwdRun (w : List Bool) : List Bool :=
  if decide (rLog w = []) then pairEncode [false] (pairEncode (rIdx w) (rQuery w))
  else pairEncode [true] (rAns w ++ rState w)

/-- The forwarding round is polynomial-time. -/
private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hS : PolyTimeComputable rState := hF.comp hD
  have hI : PolyTimeComputable rIdx := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rQuery := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rLog := hD.comp (hD.comp hD)
  have hA : PolyTimeComputable rAns := hD.comp (hD.comp (hF.comp hL))
  exact polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
    ((polyTimeComputable_const [false]).pairEncode (hI.pairEncode hX))
    ((polyTimeComputable_const [true]).pairEncode (hA.append hS))

/-! ### The forwarding handler -/

/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
forwards the query to the outer oracle of the same index and returns its answer; the adversary's
input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
outer queries. -/
def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
  stateLen := .const 0
  seedLen := seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := fwdRun
  poly := polyTimeComputable_fwdRun
  advIn := advIn
  advIn_poly := advIn_poly
  outLen := outLen
  finCall := finCall
  finRun := finRun
  finRun_poly := finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
  finRun] fwdHandler

section Forward

variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)

/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.

**Proof sketch.** The call's first round has an empty outer log, so it is the query
`⟨[false], ⟨1^i, x⟩⟩` (`decodeBitMove_query`); its second round reads the answer `y` from the
one-entry log and returns `y ‖ s` (`decodeBitMove_ret`), which `impl` splits back into `y` and
`s` (`Fin.append_left`, `Fin.append_right`). -/
theorem fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
        i x s = .query i x fun y => .pure (y, s) := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, fwdHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := i) (x := x) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨-, hI, hX, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog [])
    rw [fwdRun, hI, hX, hL, MachineCodec.encodeLog_nil, if_pos (decide_eq_true rfl)]
    exact decodeBitMove_query (fun j => (din j).eval n) (fun j => (dout j).eval n) _ i x),
    OracleComp.query_bind]
  congr 1
  funext y
  rw [buildComp_zero_of_ret (a := Fin.append y s) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨hS, -, -, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]))
    have hlog : (bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]) = pairEncode (pairEncode (List.replicate i true)
          (pairEncode (List.ofFn x) (List.ofFn y))) [] := by
      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
        bitCodec_encodeEntry]
    have hA : rAns (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
          ([] ++ [⟨i, x, y⟩]))) = List.ofFn y := by
      rw [rAns, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
    rw [fwdRun, hA, hS, hL, hlog, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)),
      ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _)]
  rw [OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s j
  · funext j
    exact Fin.append_right y s j

/-- **Simulating the forwarding handler is running the computation:** for every computation
`c` against the oracles and every state `s`, `simulate (H.impl n z ω) c s = c.bind (fun a =>
pure (a, s))`.

**Proof sketch.** Induction on `c`, with `fwdHandler_impl` at each query. -/
theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt din dout n) α)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    simulate ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).impl n z ω) c s = c.bind fun a => .pure (a, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, fwdHandler_impl, OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    rw [OracleComp.pure_bind]
    exact ih y

end Forward

/-! ### Readers of a finalization input -/

/-- The parameter `1^n` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
def finU (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- `finU w = pairFstD (pairFstD w)`. -/
theorem finU_eq (w : List Bool) : finU w = pairFstD (pairFstD w) := rfl

/-- The reduction input `z` of a finalization input. -/
def finZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))

/-- `finZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem finZ_eq (w : List Bool) : finZ w = pairFstD (pairSndD (pairFstD w)) := rfl

/-- The seed `ω` of a finalization input. -/
def finW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))

/-- `finW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem finW_eq (w : List Bool) : finW w = pairSndD (pairSndD (pairFstD w)) := rfl

/-- The adversary's output `a` of a finalization input. -/
def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
theorem finA_eq (w : List Bool) : finA w = pairFstD (pairSndD (pairSndD w)) := rfl

/-- The outer log `L` of the finalization so far. -/
def finL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- `finL w = pairSndD (pairSndD (pairSndD w))`. -/
theorem finL_eq (w : List Bool) : finL w = pairSndD (pairSndD (pairSndD w)) := rfl

/-- **The fields of a finalization input:** on `finInput n z ω s a L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a,
L⟩⟩⟩` the readers return `1^n`, `z`, `ω`, `a` and `L`. -/
theorem fields_finInput (n : ℕ) (z ω s a L : List Bool) :
    finU (InteractiveHandler.finInput n z ω s a L) = List.replicate n true ∧
      finZ (InteractiveHandler.finInput n z ω s a L) = z ∧
      finW (InteractiveHandler.finInput n z ω s a L) = ω ∧
      finA (InteractiveHandler.finInput n z ω s a L) = a ∧
      finL (InteractiveHandler.finInput n z ω s a L) = L := by
  simp only [InteractiveHandler.finInput_eq, seedIn_eq, finU, finZ, finW, finA, finL,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The finalization-input readers are polynomial-time: `PolyTimeComputable finU`, and the same
for `finZ`, `finW`, `finA` and `finL`. -/
theorem polyTimeComputable_finFields :
    PolyTimeComputable finU ∧ PolyTimeComputable finZ ∧ PolyTimeComputable finW ∧
      PolyTimeComputable finA ∧ PolyTimeComputable finL := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp (hD.comp hD),
    hD.comp (hD.comp hD)⟩

/-! ### Readers of an encoded log -/

/-- **Concatenated readings of an encoded log:** `G` applied to the successive suffixes
`L, snd L, snd (snd L), …` of the nested log `L = ⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`, for `|L| + 1` steps, and
concatenated: `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
def logEmit (G : List Bool → List Bool) (L : List Bool) : List Bool :=
  (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L)

/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
theorem logEmit_eq (G : List Bool → List Bool) (L : List Bool) :
    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := rfl

/-- The iterated second projection never lengthens a word. -/
private theorem length_iterate_pairSndD_le (L : List Bool) (i : ℕ) :
    (pairSndD^[i] L).length ≤ L.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_pairSndD_le _).trans ih

/-- **The readings of an encoded log are polynomial-time** when `G` is
(`Complexity.polyTimeComputable_iterateEmit` with the step `pairSndD`, which never lengthens a
word, and `|L|` rounds). -/
theorem polyTimeComputable_logEmit {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (logEmit G) :=
  (polyTimeComputable_iterateEmit polyTimeComputable_pairSndD hG .var .var
    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_iterate_pairSndD_le x i)).congr
    fun L => by rw [PolyExpr.eval_var, logEmit_eq]

section LogEmit

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The second projection of an encoded log drops its first entry. -/
private theorem iterate_pairSndD_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec)
    (i : ℕ) : pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
  induction i generalizing h with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases h with
    | nil =>
      rw [MachineCodec.encodeLog_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
        ← MachineCodec.encodeLog_nil codec, ih, List.drop_nil, List.drop_nil]
    | cons e t =>
      rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- Reading the suffixes of a log within at least its number of steps. -/
private theorem flatMap_range_drop (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) :
    ∀ (h : QueryLog spec) (m : ℕ), h.length ≤ m →
      ((List.range m).flatMap fun i => G (codec.encodeLog (h.drop i))) = h.flatMap g := by
  intro h
  induction h with
  | nil =>
    intro m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, MachineCodec.encodeLog_nil, hnil]
  | cons e t ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      MachineCodec.encodeLog_cons, hcons, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih m' (by rw [List.length_cons] at hm; omega)

/-- An encoded log is at least as long as its number of entries. -/
private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) :
    h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons e t ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **The readings of an encoded log are the readings of its entries:** if `G [] = []` and `G`
reads only the first entry of a nonempty log, `G ⟨⟦e⟧, t⟩ = g e`, then
`logEmit G (codec.encodeLog h) = h.flatMap g`.

**Proof sketch.** The `i`-th suffix of the encoded log encodes `h.drop i`; the first `|h|`
readings are `g` of the entries and the rest are `G [] = []`, since `|h| ≤ |L|`. -/
theorem logEmit_encodeLog (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) (h : QueryLog spec) :
    logEmit G (codec.encodeLog h) = h.flatMap g := by
  rw [logEmit_eq]
  simp only [iterate_pairSndD_encodeLog]
  exact flatMap_range_drop codec G g hnil hcons h _
    (Nat.le_succ_of_le (length_le_length_encodeLog codec h))

end LogEmit

end TCSlib.Cryptography.Composability.NMCCA2

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Decrypt.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction from non-malleability to CCA2 security

Direction (⇒) of [PS10, Theorem 175.9]. Given a non-malleability adversary `A` whose output is
`ℓ(n)` ciphertexts and a distinguisher `D`, the CCA2 adversary runs `A` on the public key and
forwards all of `A`'s queries to its own oracles (`NMCCA2.fwdHandler`). In the finalization it
asks its decryption oracle for each of `A`'s `ℓ(n)` ciphertexts in turn and outputs `D`'s
verdict on the concatenated answers. Under CCA2 the decryption oracle refuses the recorded
challenge with `⊥`, exactly as the non-malleability experiment decrypts a copy of the challenge.

This file builds the handler (`decHandler S ℓ D`): its seed is `D`'s coins, and the reduction
input is `⟨pk, α⟩`, where `α` is `D`'s advice. It proves the finalization's equation against
any outer oracle whose decryption answers are deterministic and keep the state
(`simulate_decHandler_finish`). The advice is hard-wired afterwards (`exists_withAdviceOn`,
from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`).

## Main definitions

* `NMCCA2.cntRead`, `NMCCA2.ansRead`: the per-entry readings of a log (one token, the answer).
* `NMCCA2.decHandler`: the handler of the reduction.

## Main results

* `NMCCA2.simulate_decHandler_impl`: the handler forwards.
* `NMCCA2.simulate_decHandler_finish`: the finalization decrypts the `ℓ` blocks and runs `D`.
* `NMCCA2.exists_withAdviceOn`: hard-wiring a second component of the input.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)

/-! ### Readings of a log entry -/

/-- One token for a nonempty log and nothing for the empty one:
`cntRead v = if v = [] then [] else [true]`. With `logEmit` it counts the entries of a log. -/
def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]

/-- `cntRead v = if v = [] then [] else [true]`. -/
theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl

/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (polyTimeComputable_const [true])

/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of a log:
`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))

/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl

/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

section Readings

variable {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}

/-- **Counting the entries:** `|logEmit cntRead ⟦h⟧| = |h|`. -/
theorem length_logEmit_cntRead (h : QueryLog (bitSpec din dout)) :
    (logEmit cntRead ((bitCodec din dout dα).encodeLog h)).length = h.length := by
  rw [logEmit_encodeLog _ cntRead (fun _ => [true]) rfl
    (fun e t => by rw [cntRead_eq, decide_eq_false (pairEncode_ne_nil _ _)]; rfl)]
  simp only [List.length_flatMap, List.length_singleton, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_one]

/-- **Collecting the answers:** `logEmit ansRead ⟦h⟧` is the concatenation of the entries'
answers, `h.flatMap fun e => ⟦e.2.2⟧`. -/
theorem logEmit_ansRead (h : QueryLog (bitSpec din dout)) :
    logEmit ansRead ((bitCodec din dout dα).encodeLog h) = h.flatMap fun e => List.ofFn e.2.2 :=
  logEmit_encodeLog _ ansRead _ (by
    rw [ansRead_eq, pairFstD_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
      pairSndD_of_pairDecode_eq_none pairDecode_nil]) (fun e t => by
    rw [ansRead_eq, pairFstD_pairEncode, bitCodec_encodeEntry, pairSndD_pairEncode,
      pairSndD_pairEncode]) h

end Readings

/-! ### The finalization -/

variable (S : FixedLengthPKScheme) (ℓ : PolyExpr) (D : NUPPT)

/-- The number of decryptions asked so far, in unary. -/
private def dCnt (w : List Bool) : List Bool := logEmit cntRead (finL w)

/-- The next block of the adversary's output: `ctLen(n)` bits from position `j · ctLen(n)`, for
`j` the decryptions asked so far, padded with `false`. -/
private def dCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
    ((finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length))

/-- `D`'s input layout: parameter `1^n`, the collected answers, the advice (the second component
of the reduction input) and the seed as coins. -/
private def dIn (w : List Bool) : List Bool :=
  pairEncode (pairEncode (pairEncode (finU w) (logEmit ansRead (finL w))) (pairSndD (finZ w)))
    (finW w)

/-- **One round of the finalization.** After `ℓ(n)` decryptions, output `D`'s verdict
`[D(answers) = [true]]`; before, ask the decryption oracle (index `0`) the next block. -/
private def dFin (w : List Bool) : List Bool :=
  if decide (ℓ.eval (finU w).length ≤ (dCnt w).length) then
    pairEncode [true] [decide (D.output (dIn w) = [true])]
  else pairEncode [false] (pairEncode [] (dCt S w))

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_dFin : PolyTimeComputable (dFin S ℓ D) := by
  obtain ⟨hU, hZ, hW, hA, hL⟩ := polyTimeComputable_finFields
  have hCnt : PolyTimeComputable dCnt :=
    (polyTimeComputable_logEmit polyTimeComputable_cntRead).comp hL
  have hAns : PolyTimeComputable fun w => logEmit ansRead (finL w) :=
    (polyTimeComputable_logEmit polyTimeComputable_ansRead).comp hL
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((dCnt w).length * S.ctLen.eval (finU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp
      (hCnt.pairEncode ((polyTimeComputable_unaryPoly S.ctLen).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hCt : PolyTimeComputable (dCt S) := EnsembleLemmas.polyTimeComputable_padL S.ctLen hU hDrop
  have hIn : PolyTimeComputable dIn :=
    ((hU.pairEncode hAns).pairEncode (polyTimeComputable_pairSndD.comp hZ)).pairEncode hW
  have hV : PolyTimeComputable fun w => [decide (D.output (dIn w) = [true])] :=
    (polyTimeComputable_pairEq.comp ((D.polyTimeComputable_output.comp hIn).pairEncode
      (polyTimeComputable_const [true]))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hT : PolyTimeComputable fun w => [decide (ℓ.eval (finU w).length ≤ (dCnt w).length)] :=
    (polyTimeComputable_lenLe.comp (hCnt.pairEncode
      ((polyTimeComputable_unaryPoly ℓ).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  exact polyTimeComputable_ite hT ((polyTimeComputable_const [true]).pairEncode hV)
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hCt))

/-- The adversary's input is the first component of the reduction input. -/
private theorem polyTimeComputable_decAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairFstD (pairSndD ctx)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-! ### The handler -/

/-- **The handler of the reduction (⇒)** for the scheme `S`, `ℓ` output ciphertexts and the
distinguisher `D`: the forwarding handler (`fwdHandler`) on the oracles of Definition 171.5, with
the seed of `D`'s coins, the adversary run on the first component `pk` of the reduction input
`⟨pk, α⟩`, and a finalization with at most `ℓ(n)` outer queries and a one-bit output: it asks
the decryption oracle for each of the `ℓ(n)` blocks of the adversary's output, then outputs
`[D(1^n, answers; α, ω) = [true]]`. -/
def decHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) :=
  fwdHandler (acDin S) (acDout S) D.coins (fun ctx => pairFstD (pairFstD (pairSndD ctx)))
    polyTimeComputable_decAdvIn (.const 1) ℓ (dFin S ℓ D) (polyTimeComputable_dFin S ℓ D)

/-- The handler's seed is `D`'s coins: `(decHandler S ℓ D).seedLen = D.coins`. -/
theorem decHandler_seedLen : (decHandler S ℓ D).seedLen = D.coins := by
  rw [decHandler, fwdHandler_seedLen]

/-- One outer call per inner query: `(decHandler S ℓ D).perCall = .const 1`. -/
theorem decHandler_perCall : (decHandler S ℓ D).perCall = .const 1 := by
  rw [decHandler, fwdHandler_perCall]

/-- At most `ℓ(n)` outer queries in the finalization: `(decHandler S ℓ D).finCall = ℓ`. -/
theorem decHandler_finCall : (decHandler S ℓ D).finCall = ℓ := by
  rw [decHandler, fwdHandler_finCall]

/-- A one-bit output: `(decHandler S ℓ D).outLen = .const 1`. -/
theorem decHandler_outLen : (decHandler S ℓ D).outLen = .const 1 := by
  rw [decHandler, fwdHandler_outLen]

/-- The adversary runs on the first component of the reduction input:
`(decHandler S ℓ D).advInput n z ω = pairFstD z`. -/
theorem decHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) :
    (decHandler S ℓ D).advInput n z ω = pairFstD z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [decHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- **The handler forwards** (`simulate_fwdHandler_impl`): `simulate (H.impl n z ω) c s =
c.bind fun a => pure (a, s)`. -/
theorem simulate_decHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (acDin S) (acDout S) n) α)
    (s : Fin ((decHandler S ℓ D).stateLen.eval n) → Bool) :
    simulate ((decHandler S ℓ D).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (acDin S) (acDout S) D.coins _ polyTimeComputable_decAdvIn (.const 1) ℓ
    (dFin S ℓ D) (polyTimeComputable_dFin S ℓ D) n z ω c s

/-- The `i`-th block of `ctLen(n)` bits of a string `a`, padded with `false`, as a decryption
query: `padFin _ (⟦a⟧.drop (i · ctLen(n)))`. -/
def decBlock (n : ℕ) {d : ℕ} (a : Fin d → Bool) (i : ℕ) : Fin ((acDin S 0).eval n) → Bool :=
  padFin _ ((List.ofFn a).drop (i * S.ctLen.eval n))

/-- `decBlock S n a i = padFin _ (⟦a⟧.drop (i · ctLen(n)))`. -/
theorem decBlock_eq (n : ℕ) {d : ℕ} (a : Fin d → Bool) (i : ℕ) :
    decBlock S n a i = padFin _ ((List.ofFn a).drop (i * S.ctLen.eval n)) := rfl

/-- **The finalization decrypts the blocks and runs `D`.** Against an outer oracle `O` whose
decryption answers `ans x st` are deterministic and keep the state `st`, the finalization after
the adversary's output `a` asks the `ℓ(n)` blocks of `a` and returns `D`'s verdict on the
concatenated answers:
`simulate O (H.finish n z ω s a) st = pure (padFin _ [D.output (layout 1^n ans* (snd z) ω) =
[true]], st)` with `ans* = ⟦ans (block 0) st⟧ ++ ⋯ ++ ⟦ans (block (ℓ(n) − 1)) st⟧`.

**Proof sketch.** Induction on the remaining budget along the finalization's log: after `j`
decryptions the log holds the entries `(0, block i, ans (block i) st)` for `i < j`. Its count is
`j` (`length_logEmit_cntRead`), so for `j < ℓ(n)` the round asks block `j` (its offset is
`j · ctLen(n)`, `decodeBitMove_query`), which `O` answers without changing `st`, and the log
grows by that entry. At `j = ℓ(n)` the budget is spent and the round returns the verdict on the
collected answers (`logEmit_ansRead`, `decodeBitMove_ret`). -/
theorem simulate_decHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool)
    (s : Fin ((decHandler S ℓ D).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) {σ : Type}
    (O : QueryImpl (bitSpecAt (acDin S) (acDout S) n) σ unifSpec)
    (ans : (Fin ((acDin S 0).eval n) → Bool) → σ → (Fin ((acDout S 0).eval n) → Bool))
    (hO : ∀ x st, O 0 x st = .pure (ans x st, st)) (st : σ) :
    simulate O ((decHandler S ℓ D).finish n z ω s a) st =
      .pure (padFin _ [decide (D.output (NUPPT.layout (List.replicate n true)
          ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
          (pairSndD z) (List.ofFn ω)) = [true])], st) := by
  -- The log after `j` decryptions.
  obtain ⟨hist, hhist⟩ : ∃ hist : ℕ → QueryLog (bitSpecAt (acDin S) (acDout S) n),
      hist = fun j => (List.range j).map fun i =>
        (⟨0, decBlock S n a i, ans (decBlock S n a i) st⟩ : Σ i, _) := ⟨_, rfl⟩
  have hfin : (decHandler S ℓ D).finRun = dFin S ℓ D := by
    funext w
    rw [decHandler, fwdHandler_finRun]
  have hctl : (acDin S 0).eval n = S.ctLen.eval n := by rw [acDin_zero]
  have hout : (decHandler S ℓ D).outLen.eval n = 1 := by
    rw [decHandler_outLen, PolyExpr.eval_const]
  -- The fields of the round input on the log `hist j`.
  have hfields : ∀ (j : ℕ) (w : List Bool),
      w = InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog
          (hist j)) →
      (dCnt w).length = j ∧ finU w = List.replicate n true ∧
      dIn w = NUPPT.layout (List.replicate n true)
        ((List.range j).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
        (pairSndD z) (List.ofFn ω) ∧
      dCt S w = List.ofFn (decBlock S n a j) := by
    intro j w hw
    obtain ⟨hU, hZ, hW, hA, hL⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        0).encodeLog (hist j))
    rw [← hw] at hU hZ hW hA hL
    have hc : (dCnt w).length = j := by
      rw [dCnt, hL, length_logEmit_cntRead, hhist, List.length_map, List.length_range]
    refine ⟨hc, hU, ?_, ?_⟩
    · rw [dIn, hU, hZ, hW, hL, logEmit_ansRead, NUPPT.layout_eq, hhist, List.flatMap_map,
        List.flatMap_def]
    · rw [dCt, hU, hA, hc, List.length_replicate, decBlock_eq, ofFn_padFin_eq_take,
        EnsembleLemmas.padL_eq, hctl]
  -- Induction on the remaining budget.
  have key : ∀ m j, j + m = ℓ.eval n →
      simulate O (buildComp (fun L => decodeBitMove (fun i => (acDin S i).eval n)
          (fun i => (acDout S i).eval n) ((decHandler S ℓ D).outLen.eval n)
          ((decHandler S ℓ D).finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
            (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
              0).encodeLog L)))) (zeroBits _) m (hist j)) st =
        .pure (padFin _ [decide (D.output (NUPPT.layout (List.replicate n true)
          ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
          (pairSndD z) (List.ofFn ω)) = [true])], st) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      obtain ⟨hc, hU, hIn, -⟩ := hfields (ℓ.eval n) _ rfl
      rw [buildComp_zero_of_ret, simulate_pure]
      rw [hfin, dFin, hc, hU, List.length_replicate, if_pos (decide_eq_true le_rfl), hIn]
      have hw : List.ofFn (padFin ((decHandler S ℓ D).outLen.eval n)
          [decide (D.output (NUPPT.layout (List.replicate n true)
            ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
            (pairSndD z) (List.ofFn ω)) = [true])]) =
          [decide (D.output (NUPPT.layout (List.replicate n true)
            ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
            (pairSndD z) (List.ofFn ω)) = [true])] :=
        GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hout])
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
        (decodeBitMove_ret _ _ _ _)
    | succ m ih =>
      intro j hj
      obtain ⟨hc, hU, -, hCt⟩ := hfields j _ rfl
      rw [buildComp_succ_of_query (i := 0) (x := decBlock S n a j) (by
        rw [hfin, dFin, hc, hU, List.length_replicate,
          if_neg (fun h => by have := of_decide_eq_true h; omega), hCt]
        exact decodeBitMove_query (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) _
          0 (decBlock S n a j))]
      rw [simulate_query, hO, OracleComp.pure_bind]
      have hh : hist j ++ [⟨0, decBlock S n a j, ans (decBlock S n a j) st⟩] = hist (j + 1) := by
        simp only [hhist, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [hh]
      exact ih (j + 1) (by omega)
  have h0 : hist 0 = [] := by simp only [hhist, List.range_zero, List.map_nil]
  rw [InteractiveHandler.finish_eq, decHandler_finCall, ← h0]
  exact key (ℓ.eval n) 0 (Nat.zero_add _)

/-! ### Hard-wiring the advice -/

/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.

**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
theorem exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
        B.toCompOn codec n q (pairEncode x (β n)) r := by
  have hpre : PolyTimeComputable fun w : List Bool =>
      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
  congr 1
  funext hist
  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

end TCSlib.Cryptography.Composability.NMCCA2

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction from CCA2 security to non-malleability

Direction (⇐) of [PS10, Theorem 175.9]. Given a CCA2 adversary `A` with guess `g`, the
non-malleability adversary runs `A` on the public key and forwards all of `A`'s queries to its own
oracles (`NMCCA2.fwdHandler`). It then outputs two fresh encryptions under `pk`, with its own
coins: of `g^{m}` and of `(¬g)^{m}`, where `m = msgLen(n)`. The distinguisher `guessDist` reads `g`
back from the two decryptions: from the first message bit if the first decryption is valid,
and otherwise from the negated last bit of the second.

This file builds the handler (`encHandler S`), whose seed is two encryption tapes. It proves
the finalization's equation (`encHandler_finish`) and defines the distinguisher with its two
verdicts (`guessBit_valid`, `guessBit_refused`). It also shows that at `msgLen(n) = 0` the two
CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).

## Main definitions

* `NMCCA2.encHandler`: the handler of the reduction.
* `NMCCA2.encTape`, `NMCCA2.encCt`: the seed's two tapes and the two ciphertexts.
* `NMCCA2.guessBit`, `NMCCA2.guessDist`: the distinguisher.

## Main results

* `NMCCA2.simulate_encHandler_impl`, `NMCCA2.encHandler_finish`.
* `NMCCA2.guessDist_distinguisherL`, `NMCCA2.guessBit_valid`, `NMCCA2.guessBit_refused`.
* `NMCCA2.indImpl_eq_of_msgLen_eq_zero`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDout_zero)

variable (S : FixedLengthPKScheme)

/-! ### The finalization -/

/-- The plaintext bit of ciphertext `β`: the adversary's guess `g` (its output's first bit) for
`β = true`, and `¬g` for `β = false`. -/
private def eBit (β : Bool) (w : List Bool) : Bool :=
  if β then (finA w).headD false else !(finA w).headD false

/-- The plaintext of ciphertext `β`: its bit repeated `msgLen(n)` times. -/
private def eMsg (β : Bool) (w : List Bool) : List Bool :=
  if eBit β w then List.replicate (S.msgLen.eval (finU w).length) true
  else List.replicate (S.msgLen.eval (finU w).length) false

/-- The coins of ciphertext `β`: the first (`β = true`) or the second `ρ(n)` bits of the seed. -/
private def eTape (β : Bool) (w : List Bool) : List Bool :=
  if β then (finW w).take (S.enc.coins.eval (finU w).length)
  else (finW w).drop (S.enc.coins.eval (finU w).length)

/-- Ciphertext `β`: `Enc` on `⟨1^n, ⟨pk, plaintext⟩⟩` with empty advice and its coins, padded to
`ctLen(n)` bits. -/
private def eCt (β : Bool) (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (finU w)
      (pairEncode (finZ w) (eMsg S β w))) []) (eTape S β w)))

/-- **The finalization's round:** output the two ciphertexts, `⟨[true], c₁ ‖ c₂⟩`. -/
private def eFin (w : List Bool) : List Bool := pairEncode [true] (eCt S true w ++ eCt S false w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_eFin : PolyTimeComputable (eFin S) := by
  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
  have hg : PolyTimeComputable fun w => [(finA w).headD false] := polyTimeComputable_headD.comp hA
  have hBit : ∀ β, PolyTimeComputable fun w => [eBit β w] := by
    intro β
    cases β
    · exact (polyTimeComputable_not hg).congr fun w => rfl
    · exact hg.congr fun w => rfl
  have hMsg : ∀ β, PolyTimeComputable (eMsg S β) := fun β =>
    polyTimeComputable_ite (hBit β) ((polyTimeComputable_unaryPoly S.msgLen).comp hU)
      (EnsembleLemmas.polyTimeComputable_zeros S.msgLen hU)
  have hTape : ∀ β, PolyTimeComputable (eTape S β) := by
    intro β
    cases β
    · exact ((polyTimeComputable_pairDropPoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
    · exact ((polyTimeComputable_pairTakePoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hCt : ∀ β, PolyTimeComputable (eCt S β) := fun β =>
    EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
      (((hU.pairEncode (hZ.pairEncode (hMsg β))).pairEncode
        (polyTimeComputable_const [])).pairEncode (hTape β)))
  exact (polyTimeComputable_const [true]).pairEncode ((hCt true).append (hCt false))

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_encAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-! ### The handler -/

/-- **The handler of the reduction (⇐)** for the scheme `S`: the forwarding handler
(`fwdHandler`) on the oracles of Definition 171.5, with a seed of two encryption tapes
(`2ρ(n)` bits), the adversary run on the reduction input `pk`, and a finalization without outer
queries whose output is `2 · ctLen(n)` bits: `Enc_pk(g^{msgLen(n)})` with the first tape, then
`Enc_pk((¬g)^{msgLen(n)})` with the second, where `g` is the adversary's first output bit. -/
def encHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) :=
  fwdHandler (acDin S) (acDout S) (S.enc.coins.add S.enc.coins)
    (fun ctx => pairFstD (pairSndD ctx)) polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen)
    (.const 0) (eFin S) (polyTimeComputable_eFin S)

/-- Two encryption tapes: `(encHandler S).seedLen = ρ + ρ`. -/
theorem encHandler_seedLen : (encHandler S).seedLen = S.enc.coins.add S.enc.coins := by
  rw [encHandler, fwdHandler_seedLen]

/-- One outer call per inner query: `(encHandler S).perCall = .const 1`. -/
theorem encHandler_perCall : (encHandler S).perCall = .const 1 := by
  rw [encHandler, fwdHandler_perCall]

/-- No outer query in the finalization: `(encHandler S).finCall = .const 0`. -/
theorem encHandler_finCall : (encHandler S).finCall = .const 0 := by
  rw [encHandler, fwdHandler_finCall]

/-- Two ciphertexts as output: `(encHandler S).outLen = ctLen + ctLen`. -/
theorem encHandler_outLen : (encHandler S).outLen = S.ctLen.add S.ctLen := by
  rw [encHandler, fwdHandler_outLen]

/-- The adversary runs on the reduction input: `(encHandler S).advInput n z ω = z`. -/
theorem encHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) :
    (encHandler S).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [encHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- **The handler forwards** (`simulate_fwdHandler_impl`): `simulate (H.impl n z ω) c s =
c.bind fun a => pure (a, s)`. -/
theorem simulate_encHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (acDin S) (acDout S) n) α)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) :
    simulate ((encHandler S).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (acDin S) (acDout S) (S.enc.coins.add S.enc.coins) _
    polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen) (.const 0) (eFin S)
    (polyTimeComputable_eFin S) n z ω c s

/-- **The seed's two encryption tapes:** tape `true` is the first `ρ(n)` bits of the seed, tape
`false` the rest (`ρ(n)` bits), read as coins of `Enc`. -/
def encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    S.enc.Coins n :=
  (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then (List.ofFn ω).take (S.enc.coins.eval n)
    else (List.ofFn ω).drop (S.enc.coins.eval n)))

/-- `encTape S n ω β = (coinsEquivPoly rfl n).symm (padFin _ (if β then ⟦ω⟧.take ρ(n) else
⟦ω⟧.drop ρ(n)))`. -/
theorem encTape_eq (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    encTape S n ω β = (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then
      (List.ofFn ω).take (S.enc.coins.eval n) else (List.ofFn ω).drop (S.enc.coins.eval n))) :=
  rfl

/-- The tapes as strings: `⟦encTape S n ω β⟧ = if β then ⟦ω⟧.take ρ(n) else ⟦ω⟧.drop ρ(n)`. -/
theorem ofFn_encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    List.ofFn (encTape S n ω β) = if β then (List.ofFn ω).take (S.enc.coins.eval n)
      else (List.ofFn ω).drop (S.enc.coins.eval n) := by
  have hω : (List.ofFn ω).length = S.enc.coins.eval n + S.enc.coins.eval n := by
    rw [List.length_ofFn, encHandler_seedLen, PolyExpr.eval_add]
  rw [encTape_eq, NUPPT.coinsEquivPoly_symm_ofFn]
  cases β
  · exact GGMRed.ofFn_padFin_of_length (by
      rw [if_neg Bool.false_ne_true, List.length_drop, hω]; omega)
  · exact GGMRed.ofFn_padFin_of_length (by rw [if_pos rfl, List.length_take, hω]; omega)

/-- **Ciphertext `β` of the reduction's output**, for the public key `z`, the seed `ω` and the
guess `g`: `padL ctLen(n) (Enc_z(b^{msgLen(n)}); encTape β)` with `b = g` for `β = true` and
`b = ¬g` for `β = false`. -/
def encCt (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g β : Bool) :
    List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
    (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
    (encTape S n ω β))

/-- `encCt S n z ω g β = padL ctLen(n) (Enc_z((if β then g else ¬g)^{msgLen(n)}); encTape β)`. -/
theorem encCt_eq (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (g β : Bool) :
    encCt S n z ω g β = EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
      (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
      (encTape S n ω β)) :=
  rfl

/-- **The finalization outputs the two ciphertexts:** after the adversary's output `a` (guess
`g = ⟦a⟧.headD false`), `H.finish n z ω s a = pure (padFin _ (encCt … g true ++ encCt … g false))`,
asking nothing.

**Proof sketch.** With budget `0` the first round returns (`buildComp_zero_of_ret`): its word is
`⟨[true], c₁ ‖ c₂⟩` of the right length (`length_padL`, `decodeBitMove_ret`), and each `cᵢ` is
`encCt` by the input readers, `NUPPT.Uniform.runAt_eq` and `ofFn_encTape`. -/
theorem encHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
    (encHandler S).finish n z ω s a =
      .pure (padFin _ (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) := by
  have hfin : (encHandler S).finRun = eFin S := by
    funext w
    rw [encHandler, fwdHandler_finRun]
  rw [InteractiveHandler.finish_eq, encHandler_finCall, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
  have hCt : ∀ β, eCt S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        0).encodeLog [])) = encCt S n z ω ((List.ofFn a).headD false) β := by
    intro β
    have hm : eMsg S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
        (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
          0).encodeLog [])) =
        List.ofFn fun _ : Fin (S.msgLen.eval n) =>
          if β then (List.ofFn a).headD false else !(List.ofFn a).headD false := by
      rw [List.ofFn_const, eMsg, eBit, hA, hU, List.length_replicate]
      cases β <;> cases (List.ofFn a).headD false <;> rfl
    rw [eCt, hm, hU, hZ, encCt_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
      ofFn_encTape, eTape, hW, hU, List.length_replicate]
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) =
      encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  show decodeBitMove _ _ _ ((encHandler S).finRun _) = _
  rw [hfin, eFin, hCt, hCt]
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### The distinguisher -/

/-- **The distinguisher's verdict** on the concatenated decryptions `w = v₁ ‖ v₂`: the bit after
the first validity flag if that flag is set, and the negated last bit of `w` otherwise. -/
def guessBit (w : List Bool) : Bool :=
  if w.headD false then (w.drop 1).headD false else !w.reverse.headD false

/-- `guessBit w = if w.headD false then (w.drop 1).headD false else ¬ w.reverse.headD false`. -/
theorem guessBit_eq (w : List Bool) :
    guessBit w = if w.headD false then (w.drop 1).headD false else !w.reverse.headD false := rfl

/-- The distinguisher's raw function on the machine input `⟨⟨⟨1^n, w⟩, α⟩, ρ⟩`. -/
private def guessFun (x : List Bool) : List Bool :=
  if (pairSndD (pairFstD (pairFstD x))).headD false then
    [((pairSndD (pairFstD (pairFstD x))).drop 1).headD false]
  else [!(pairSndD (pairFstD (pairFstD x))).reverse.headD false]

/-- The distinguisher's raw function is polynomial-time. -/
private theorem polyTimeComputable_guessFun : PolyTimeComputable guessFun := by
  have hw : PolyTimeComputable fun x => pairSndD (pairFstD (pairFstD x)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hw)
    (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hw))
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp (BinArith.polyTimeComputable_reverse.comp hw)))

/-- **The distinguisher** of the reduction (⇐): the uniform machine without coins computing
`[guessBit w]` on its argument `w`. -/
noncomputable def guessDist : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_guessFun (.const 0)

/-- The distinguisher accepts `w` exactly when `guessBit w`:
`guessDist.distinguisherL n w ρ = guessBit w`. -/
theorem guessDist_distinguisherL (n : ℕ) (w : List Bool) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n w ρ = guessBit w := by
  have hrun : ∀ y r, guessDist.runAtL n y r = guessFun (pairEncode (pairEncode
      (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform polyTimeComputable_guessFun (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, guessFun, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, guessBit_eq]
  split <;> simp

/-- **A valid first decryption gives the guess:** if `v₁` encodes the message `g^m` with `m > 0`,
then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_valid {m : ℕ} (hm : 0 < m) (g : Bool) (v₂ : List Bool) :
    guessBit (List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => g)) ++ v₂) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [FixedLengthScheme.decAnswer_some, guessBit_eq, List.ofFn_succ, List.ofFn_succ]
  simp

/-- **A refused first decryption is answered by the second:** if `v₁` is `⊥ = 0` and `v₂`
encodes `(¬g)^m` with `m > 0`, then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_refused {m : ℕ} (hm : 0 < m) (g : Bool) :
    guessBit (List.ofFn (zeroBits (m + 1)) ++
      List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => !g))) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h2 : List.ofFn (Fin.cons (α := fun _ => Bool) true (fun _ : Fin (m' + 1) => !g)) =
      true :: (List.replicate m' (!g) ++ [!g]) := by
    rw [List.ofFn_succ, Fin.cons_zero, ← List.replicate_succ', ← List.ofFn_const]
    rfl
  rw [FixedLengthScheme.decAnswer_some, h2, guessBit_eq, ofFn_zeroBits, List.replicate_succ]
  simp

/-! ### Empty messages -/

/-- **With empty messages the two CCA2 oracles coincide:** if `msgLen(n) = 0`, then
`S.indImpl atk false n pk sk = S.indImpl atk true n pk sk` (both halves of a challenge are the
empty message).

**Proof sketch.** Compare query by query through the published equations: decryption does not
depend on the bit (`indImpl_dec_onSpec`), a repeated challenge repeats the record
(`indImpl_challenge_repeat_onSpec`), and a first challenge encrypts a half of the query
(`indImpl_challenge_none_onSpec`), whose string is `[]` either way. -/
theorem indImpl_eq_of_msgLen_eq_zero (atk : Attack) (n : ℕ) (pk sk : List Bool)
    (h : S.msgLen.eval n = 0) : S.indImpl atk false n pk sk = S.indImpl atk true n pk sk := by
  have h0 : ∀ f : Fin (S.msgLen.eval n) → Bool, List.ofFn f = [] := fun f =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, h])
  funext i x s
  match i with
  | 0 => rw [S.indImpl_dec_onSpec, S.indImpl_dec_onSpec]
  | 1 =>
    cases s with
    | some c => rw [S.indImpl_challenge_repeat_onSpec, S.indImpl_challenge_repeat_onSpec]
    | none =>
      rw [S.indImpl_challenge_none_onSpec, S.indImpl_challenge_none_onSpec]
      simp only [h0]

end TCSlib.Cryptography.Composability.NMCCA2

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of public-key encryption

[PS10, Definition 171.5], the public-key form of Definition 168.1: `(pk, sk) ← Gen(1^n)`;
`(m₀, m₁, state) ← A^{O₁(sk)}(1^n, pk)`; `c ← Enc_pk(m_b)`; output `A^{O₂(sk)}(c, state)`. The
oracle pairs are `[·, ·]` (CPA), `[Dec, ·]` (CCA1) and `[Dec, Dec*]` (CCA2), where `Dec*` answers
every query except the challenge. There is no encryption oracle: the adversary holds `pk`.
The trapdoor application of Claim 172.a is in `Encryption.PublicKey.TrapdoorCPA`.

**Its encoding.** As in the private-key game (`Encryption/PrivateKey/OracleSecurity.lean`), one
machine plays both phases. It takes `pk` and queries the bit-string oracles `Dec` and `Challenge`.
The oracle state records the challenge and uses it to gate `Dec` by phase (`decOpen`).

**Fixed lengths by canonical padding** (ruling of 2026-11-05). The codec's oracles take and return
fixed-length strings. Public-key schemes of the ch. 2–4 layer have ciphertexts of varying length,
for example Algorithm 104.3's `⟨f_i(r), b ⊕ m⟩`. A generic wrapper (`FixedLengthPKScheme.ofPadded`)
pads every ciphertext `c` to `L(n)` bits as `⟨c, 1^{L(n) − 2|c| − 2}⟩` (`padCt`). Its decryptor
answers `⊥` on every string that is not such a canonical padding (`isPadded`). Without that check
the padded scheme would be malleable: changing a padding bit of the challenge gives a different
string that decrypts to the same message, which breaks CCA2. Padding is a bijection between
ciphertexts and canonical strings (`pairFstD_padCt`, `padCt_of_isPadded`). So `Dec*` refusing the
padded challenge is `Dec*` refusing the challenge. A bound `L` always exists
(`PublicKeyScheme.exists_padBound`, from the machines' time bounds).

**Deviations** (beyond those of Definition 168.1): ciphertexts reach the adversary padded, and
`Dec` takes only `L(n)`-bit queries, so it decrypts only ciphertexts with `2|c| + 2 ≤ L(n)`.
Security is stated for each admissible `L`; a larger `L` admits longer `Dec` queries.

## Main definitions

* `Composability.padCt`, `Composability.isPadded`: canonical padding and its test.
* `Composability.FixedLengthPKScheme`: a public-key scheme with `msgLen(n)`-bit messages and
  `ctLen(n)`-bit ciphertexts; `FixedLengthPKScheme.ofPadded` builds one by padding.
* `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`: the ch. 2–4 schemes, padded.
* `FixedLengthPKScheme.indImpl`, `indGame`, `INDSecure`: [PS10, Definition 171.5].

## Main results

* `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
  canonical strings.
* `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security.
  Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA run and first-challenge
  congruence) and `OracleSecurity.RecordHandler` (the recording handler for T1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it on Construction 104.3 (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Canonical padding -/

/-- **Canonical padding** of a ciphertext `c` to `L` bits: `⟨c, 1^{L − 2|c| − 2}⟩`. -/
def padCt (L : ℕ) (c : List Bool) : List Bool :=
  pairEncode c (List.replicate (L - (2 * c.length + 2)) true)

/-- Padding pairs `c` with `L - (2 * c.length + 2)` true bits. -/
theorem padCt_eq (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl

/-- Whether `w` is a canonical padding: a pair `⟨c, s⟩` whose second part `s` is all `true`. -/
def isPadded (w : List Bool) : Bool :=
  decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)

/-- The canonical-padding test checks that `w` is its decoded pair and that its second
component contains no false bit. -/
theorem isPadded_eq (w : List Bool) :
    isPadded w =
      (decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)) := rfl

/-- A padding to `L ≥ 2|c| + 2` bits has `L` bits. -/
theorem length_padCt {L : ℕ} {c : List Bool} (h : 2 * c.length + 2 ≤ L) :
    (padCt L c).length = L := by
  simp only [padCt, length_pairEncode, List.length_replicate]
  omega

/-- Unpadding recovers the ciphertext. -/
@[simp] theorem pairFstD_padCt (L : ℕ) (c : List Bool) : pairFstD (padCt L c) = c := by
  simp [padCt]

/-- A padding is canonical. -/
theorem isPadded_padCt (L : ℕ) (c : List Bool) : isPadded (padCt L c) = true := by
  simp [isPadded, padCt, BinArith.hasFalse_eq]

/-- A canonical string is the padding of its first part to its own length. -/
theorem padCt_of_isPadded {w : List Bool} (h : isPadded w = true) :
    padCt w.length (pairFstD w) = w := by
  simp only [isPadded, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h
  have hall : pairSndD w = List.replicate (pairSndD w).length true := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
    cases b
    · simp only [BinArith.hasFalse_eq, List.any_eq_false, List.mem_map, id_eq,
        forall_exists_index, and_imp] at h₂
      exact absurd rfl (h₂ _ false hb rfl)
    · rfl
  have hlen : w.length = 2 * (pairFstD w).length + 2 + (pairSndD w).length := by
    conv_lhs => rw [← h₁]
    simp only [length_pairEncode]
  unfold padCt
  rw [hlen, show 2 * (pairFstD w).length + 2 + (pairSndD w).length -
    (2 * (pairFstD w).length + 2) = (pairSndD w).length by omega, ← hall]
  exact h₁

/-- The canonical test is polynomial-time. -/
theorem polyTimeComputable_isPadded : PolyTimeComputable (fun w => [isPadded w]) := by
  have heq : PolyTimeComputable fun w => [decide (pairEncode (pairFstD w) (pairSndD w) = w)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD).pairEncode
        polyTimeComputable_id) using 1
    funext w
    simp [Function.comp_apply]
  exact polyTimeComputable_and heq
    (polyTimeComputable_not (BinArith.polyTimeComputable_hasFalse.comp polyTimeComputable_pairSndD))

/-! ### The padded encryptor and decryptor -/

/-- The padded encryptor's string function: run `Enc` on the same parameter, argument and coins,
and pad its ciphertext to `L(n)` bits. -/
def padEncFun (enc : NUPPT) (L : PolyExpr) (z : List Bool) : List Bool :=
  padCt (L.eval (NUPPT.inParam z).length)
    (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)))

/-- The padded encryptor's string function pads the original output at the same parameter,
argument and coins, with empty advice, to the length prescribed by `L`. -/
theorem padEncFun_eq (enc : NUPPT) (L : PolyExpr) (z : List Bool) :
    padEncFun enc L z = padCt (L.eval (NUPPT.inParam z).length)
      (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z))) := rfl

/-- The padded encryptor is polynomial-time. -/
theorem polyTimeComputable_padEncFun (enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (padEncFun enc L) := by
  have ho : PolyTimeComputable fun z =>
      enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)) :=
    enc.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  have h := ho.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ho.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp NUPPT.polyTimeComputable_inParam)))
  convert h using 1
  funext z
  simp [padEncFun, padCt, Function.comp_apply, length_pairEncode]

/-- The padded decryptor's string function on `⟨sk, w⟩`: `Dec ⟨sk, c⟩` if `w` is the canonical
padding of `c`, and `⊥` otherwise, here `true :: w`, one bit longer than the query. -/
def padDecFun (dec : List Bool → List Bool) (z : List Bool) : List Bool :=
  if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
  else true :: pairSndD z

/-- The padded decryptor decrypts the unpadded query when its canonical test passes and
returns `true :: pairSndD z` otherwise. -/
theorem padDecFun_eq (dec : List Bool → List Bool) (z : List Bool) :
    padDecFun dec z =
      if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      else true :: pairSndD z := rfl

/-- The padded decryptor is polynomial-time when `Dec` is. -/
theorem polyTimeComputable_padDecFun {dec : List Bool → List Bool}
    (hdec : PolyTimeComputable dec) : PolyTimeComputable (padDecFun dec) :=
  polyTimeComputable_ite (polyTimeComputable_isPadded.comp polyTimeComputable_pairSndD)
    (hdec.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    ((polyTimeComputable_const [true]).append polyTimeComputable_pairSndD)

/-- The padded encryptor as a machine, with the coins of `Enc`. -/
noncomputable abbrev padEnc (enc : NUPPT) (L : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor uses the original encryptor's coin polynomial. -/
theorem padEnc_coins (enc : NUPPT) (L : PolyExpr) : (padEnc enc L).coins = enc.coins :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor pads the ciphertext of the uniform `Enc` with the same coin string,
read in `enc` through the public `padEnc_coins` identification. -/
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- The padded decryptor on a padding is `Dec`. -/
theorem padDecFun_padCt (dec : List Bool → List Bool) (sk c : List Bool) (L : ℕ) :
    padDecFun dec (pairEncode sk (padCt L c)) = dec (pairEncode sk c) := by
  simp [padDecFun, isPadded_padCt]

/-- The padded decryptor answers a non-canonical query `w` with a string of `|w| + 1` bits. -/
theorem padDecFun_of_not_isPadded (dec : List Bool → List Bool) (sk w : List Bool)
    (hw : isPadded w = false) : padDecFun dec (pairEncode sk w) = true :: w := by
  simp [padDecFun, hw]

/-! ### Fixed-length public-key schemes -/

/-- A **public-key scheme with fixed-length ciphertexts** [PS10, Definition 102.1]: `msgLen(n)`-bit
messages; `Gen(1^n) = ⟨pk, sk⟩`; `Enc_pk(m)` activated on `⟨pk, m⟩`, whose ciphertexts under
generated keys have `ctLen(n)` bits; a deterministic polynomial-time `Dec` on `⟨sk, c⟩`, with
`⊥` any output that decodes to no message; perfect correctness. -/
structure FixedLengthPKScheme where
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The ciphertext length. -/
  ctLen : PolyExpr
  /-- The key generator. -/
  gen : NUPPT
  /-- The encryptor. -/
  enc : NUPPT
  /-- The decryptor. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
  /-- Ciphertexts under generated keys have `ctLen(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
    (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length =
      ctLen.eval n

namespace FixedLengthPKScheme

/-- **The padded scheme**: a public-key scheme with ciphertexts padded to `L(n)` bits, given that
`L` bounds the honest ciphertexts (`2|c| + 2 ≤ L(n)`) and the message length (so that `⊥` on a
non-canonical `L(n)`-bit query, `|w| + 1` bits, decodes to no message). -/
noncomputable def ofPadded (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (_hmsg : ∀ n, msgLen.eval n ≤ L.eval n) : FixedLengthPKScheme where
  msgLen := msgLen
  ctLen := L
  gen := gen
  enc := padEnc enc L
  dec := padDecFun dec
  gen_uniform := gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_padDecFun dec_poly
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))

section PaddedReaders

variable (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, msgLen.eval n ≤ L.eval n)

/-- The padded constructor preserves the supplied message-length polynomial. -/
theorem ofPadded_msgLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).msgLen =
      msgLen := rfl

/-- The padded constructor's ciphertext-length polynomial is `L`. -/
theorem ofPadded_ctLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).ctLen =
      L := rfl

/-- The padded constructor preserves the supplied key generator. -/
theorem ofPadded_gen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).gen =
      gen := rfl

/-- The padded constructor uses `padEnc enc L` as its encryptor. -/
theorem ofPadded_enc :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).enc =
      padEnc enc L := rfl

/-- The padded constructor uses `padDecFun dec` as its decryptor. -/
theorem ofPadded_dec :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).dec =
      padDecFun dec := rfl

end PaddedReaders

end FixedLengthPKScheme

/-- **A ch. 2–4 public-key scheme, padded** to `L(n)`-bit ciphertexts. -/
noncomputable def _root_.TCSlib.Cryptography.PublicKeyScheme.padded (S : PublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded .var S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n m rg re => S.correct n m rg re) L hL hmsg

section PublicKeyPaddedReaders

variable (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n)

/-- Padding a public-key scheme preserves its message-length polynomial `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.var := rfl

/-- The padded public-key scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded public-key scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded public-key scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end PublicKeyPaddedReaders

/-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
messages, `Enc` activated on `⟨pk, [b]⟩`. -/
noncomputable def _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded (S : BitPublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded (.const 1) S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n (m : Fin 1 → Bool) rg re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm, S.correct n (m 0) rg re, ← hm, decodeFin_ofFn])
    L
    (fun n rg (m : Fin 1 → Bool) re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm]
      exact hL n rg (m 0) re)
    hmsg

section BitPublicKeyPaddedReaders

variable (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n)

/-- Padding a single-bit public-key scheme preserves its constant one-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.const 1 := rfl

/-- The padded single-bit scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a single-bit public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded single-bit scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded single-bit scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end BitPublicKeyPaddedReaders

/-- **A padding bound exists** for every ch. 2–4 public-key scheme, from the time bounds of
`Gen` and `Enc` (`NUPPT.length_runAt_le_runLenPoly`): `|pk| ≤ Q₁(n)`, the input `⟨pk, m⟩` has at
most `2Q₁(n) + 2 + n` bits, and the ciphertext at most `Q₂(n)`; `L = 2Q₂ + 2 + n` works.

**Proof sketch.** Bound the generator's output by its running-time polynomial, which also
bounds its public-key projection. The pair-encoding length formula then bounds the encryptor's
input by `2Q₁(n) + 2 + n`. Applying the encryptor's output-length bound to this input gives
`Q₂(n)`. Choose `L(n) = 2Q₂(n) + 2 + n`: it covers the ciphertext's pair-encoding overhead and
is at least the message length `n`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.exists_padBound (S : PublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
          + 2 ≤ L.eval n) ∧ ∀ n, n ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)).length ≤
        (PolyExpr.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var).eval
          n := by
    intro n rg m
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨.add (.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var))) (.const 2))
      .var, fun n rg m re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg m) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

/-- **A padding bound exists** for every ch. 2–4 single-bit public-key scheme (as for
`PublicKeyScheme.exists_padBound`).

**Proof sketch.** The generator's output-length bound also bounds the public key by `Q₁(n)`.
Pairing that key with one bit gives an encryptor input of at most `2Q₁(n) + 3` bits. Its
running-time bound therefore supplies a ciphertext-length polynomial `Q₂(n)`. The polynomial
`L(n) = 2Q₂(n) + 2` covers the ciphertext encoding and is at least one, as required for the
single-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.exists_padBound (S : BitPublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
          ≤ L.eval n) ∧ ∀ n, 1 ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (b : Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]).length ≤
        (PolyExpr.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)).eval n := by
    intro n rg b
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_singleton, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  refine ⟨.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)))) (.const 2),
      fun n rg b re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg b) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-! ### The experiment of Definition 171.5 -/

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The query lengths of the two oracles `Dec` and `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => S.msgLen.eval n + S.msgLen.eval n

/-- Decryption queries have the scheme's ciphertext length. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl

/-- Challenge queries contain two messages of the scheme's message length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` a ciphertext. -/
def outLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n

/-- Decryption answers contain a validity bit followed by one message. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl

/-- Challenge answers have the scheme's ciphertext length. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl

/-- The two oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 2) := bitSpec (S.inLens n) (S.outLens n)

/-- The public-key IND oracle specification is the bit specification at the scheme's query
and answer lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Oracle `i` accepts bit strings of length `S.inLens n i`. -/
theorem indSpec_dom (n : ℕ) (i : Fin 2) :
    (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
  bitSpec_dom (S.inLens n) (S.outLens n) i

/-- The decryption oracle accepts a ciphertext at the scheme's encoded width. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_zero]

/-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
theorem indSpec_rng (n : ℕ) (i : Fin 2) :
    (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
  bitSpec_rng (S.inLens n) (S.outLens n) i

/-- **The oracles of `Ind_b`** at parameter `n`, for the keys `pk`, `sk`; the state is the
challenge, once asked.
- `Dec` answers `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not the challenge, and
  `⊥` (all `false`) otherwise; an output that decodes to no message is `⊥` as well.
- `Challenge` answers `Enc_pk(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c)

/-- A decryption query checks oracle availability and refuses the recorded challenge;
otherwise it returns the decoded plaintext with its validity flag, preserving the state. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits _, s) := rfl

/-- The first challenge query encrypts the selected message half using fresh coins and
records the padded ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c) := rfl

/-- A repeated challenge query returns the recorded ciphertext and preserves it as state. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl

/-- The decryption equation on the query specification's type. Read the ciphertext through
the width equality before checking challenge refusal and decrypting. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n pk sk c s

/-- The decryption oracle answers a validity bit followed by one message:
`(S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- `indImpl_dec_onSpec` with the answer cast through `indSpec_decRng`: for `c' = cast _ c`,
`S.indImpl atk b n pk sk 0 c s = if decOpen atk s.isSome && s ≠ some c' then
pure (cast _ (decAnswer (decodeFin _ (Dec ⟨sk, c'⟩))), s) else pure (zeroBits _, s)`. -/
theorem indImpl_dec_onSpec_cast (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (S.indSpec_decRng n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s

/-- The challenge oracle returns a ciphertext at the scheme's encoded width. -/
theorem indSpec_challengeRng (n : ℕ) :
    (S.indSpec n).rng 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_rng, S.outLens_one]

/-- A challenge query contains two messages at the scheme's message width. -/
theorem indSpec_challengeDom (n : ℕ) :
    (S.indSpec n).dom 1 = (Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_one]

/-- The fresh challenge equation on the query specification's type. Draw new encryption
coins, encrypt the selected half of the query, and record the resulting ciphertext. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n pk sk mm

/-- Repeating the challenge preserves the previous state for a query of the specification's
type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n pk sk mm c

/-- Under CPA, `Dec` never answers. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n pk sk 0 c s = .pure (zeroBits _, s) := by
  simp [indImpl, FixedLengthScheme.decOpen_cpa]

/-- Under CCA2, `Dec` refuses the challenge. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n pk sk 0 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, FixedLengthScheme.decOpen_cca2]

/-- The codec of the adversary: the two oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The public-key IND codec decodes a move with the bit decoder at the scheme's oracle
lengths and a one-bit final output. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The public-key IND codec encodes an entry by pairing the unary oracle index with its
query and answer strings. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The public-key IND codec returns the false one-bit result on timeout. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res => .pure (res.1 0)

/-- The public-key IND game samples key-generation and adversary coins, simulates the
oracles on the public-key input from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)))
        (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security of a public-key scheme** [PS10, Definition 171.5]: for every
non-uniform PPT `A` and every polynomial query budget, `A`'s advantage between `Ind_0` and
`Ind_1` is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- Public-key IND security is exactly negligible advantage for every non-uniform PPT
adversary and polynomial query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthPKScheme

/-! ### From ensemble security to CPA -/

section PaddedCPA

open ChallengeSim ProbComp

/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
`padCt L(n) c` of the ciphertext it received. -/
private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))

/-- The challenge answer is polynomial-time (as `padEncFun`). -/
private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
  convert h using 1
  funext ctx
  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]

/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
  subst hk
  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
    List.ofFn_succ]

/-- **Eager challenge coins** (checkpoint 1). Under CPA, simulating the oracles of `Ind_b` from
the state `s` has, for every function `G` of the output, the expectation of first sampling the
encryption coins `re` and then running the deterministic oracles whose challenge answer is the
encryption of `m_b` with coins `re` (`chRun`).

**Proof sketch.** Induction on the computation. Decryption queries are answered all-`false`
in both (`indImpl_dec_cpa`); a repeated challenge repeats the recorded ciphertext in both. At the
first challenge the lazy side samples `re` and continues from the recorded ciphertext; by the
induction hypothesis the continuation is again an average over coins `re'`, and from a recorded
state the deterministic run does not depend on `re'` (`chRun_some_congr`), so `re'`
marginalizes out (`expect_const`). -/
private theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2
            else (FixedLengthScheme.splitHalf mm).1))) re) c s).1 := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, S.indImpl_dec_cpa, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, S.indImpl_challenge_repeat, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, S.indImpl_challenge_none, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (S.ctLen.eval n) → Bool) => G p.1)
            (chRun_some_congr _ _ _ _))).trans (expect_const _ _)

/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
      (r : A.Coins n),
      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n)
              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
          B.runAt n z (φ (ω, r)) =
            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
  set S' := S.padded L hL hmsg with hS'
  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  -- The two codecs have equal lengths.
  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
    funext i
    match i with
    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
    funext i
    match i with
    | 0 =>
      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if F rg r ((firstQ (comp rg r)).elim []
                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
    intro b
    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine (expect_simulate_indImpl_cpa S' b n _ _
      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n)]
    refine congrArg _ (funext fun re' => ?_)
    rw [prob_pure]
    congr 2
    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.ctLen.eval n) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => ?_)
    rw [hmm, Option.elim_some]
    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const])]
      rfl)
  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
    intro β rg r re ω
    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
    have hadv :
        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
          (S.pkEncDist n β (rg, re)) ω =
        pairFstD (S.gen.runAt n [] rg) := by
      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
        pairFstD_pairEncode]
    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
        L.eval n := by
      rw [hans]
      exact length_padCt (hL n rg β re)
    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
      (S.pkEncDist n β (rg, re)) ω hw _
    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
    obtain ⟨rfl, rfl⟩ := hsim'
    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
    rw [hadv] at h₁ h₂ hs'
    rw [h₂] at hs'
    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
        [F rg r (W β rg re)] := by
      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [ha]
    cases hq : firstQ (comp rg r) with
    | none =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = none := hq
      rw [hq', Option.elim_none] at hs'
      rw [hs', recOut_init, Option.elim_none]
      decide
    | some l =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = some l := hq
      have hl : l.length = 2 := by
        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
      rw [hq', Option.elim_some] at hs'
      rw [hs', recOut_recorded, Option.elim_some]
      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
        and_true, Bool.decide_eq_true]
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if ((firstQ (comp rg r)).elim false fun l =>
              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
            then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
        Bool) := by
      rw [recHandler_seedLen, PolyExpr.eval_const]
      infer_instance
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re]
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none =>
    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    have hl : l.length = 2 := by
      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
      if_false, if_true]
    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
   that answer (`ChallengeSim.chRun_congr`).
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
  -- Step 4: the advantages are equal.
  obtain ⟨φ, hφ⟩ := hB n
  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ

end PaddedCPA

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of private-key encryption (definitions)

[PS10, Definition 168.1], the first definition of ch. 7 (prong C of the ch. 5–8 campaign), stated
as a game of the `Games` framework over the ch. 2–4 layer's `PrivateKeyScheme`.

**The experiment** `IND_b^{O₁,O₂}(Π, A, n)`: `k ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁(k)}(1^n)`;
`c ← Enc_k(m_b)`; output `A^{O₂(k)}(c, state)`. The oracle pairs are `[Enc; Enc]` (CPA),
`[Enc, Dec; Enc]` (CCA1) and `[Enc, Dec; Enc, Dec]` (CCA2). Under CCA2, `Dec` returns `⊥` on the
challenge `c`.

**Its encoding.** One machine plays both phases against three bit-string oracles:
- `Enc` (`n`-bit messages, `ct(n)`-bit ciphertexts);
- `Dec` (`ct(n)`-bit ciphertexts; an `(n + 1)`-bit answer, a validity flag followed by the message);
- `Challenge`, which takes `⟨m₀, m₁⟩` and returns `c ← Enc_k(m_b)`.

The oracles' state remembers the challenge, once asked. That state decides the phase: `Dec` answers
never (CPA), before the challenge only (CCA1), or always, except on `c` itself (CCA2). A refused
`Dec` query, or a repeated challenge, gets a fixed answer. The machine's final output is one bit.

**Deviations, declared once here.**
- **One machine for both phases.** The source's two-phase adversary passes `state` from phase 1
  to phase 2. Here a single next-move machine plays both phases, and its query log (which includes
  the challenge `c`) is that state. Either form simulates the other, at polynomial cost.
- **Fixed-length ciphertexts.** The scheme's ciphertexts at parameter `n` have exactly `ct(n)`
  bits (`FixedLengthScheme`), as the oracle codec needs.
- **Query budgets.** The adversary's number of oracle queries is an explicit polynomial `q`,
  universally quantified, as in the ch. 2–4 layer's `OracleEnsemble.Indist`.
- **Indistinguishability** of the two one-bit outputs is a negligible distinguishing advantage
  between the games for `b = 0` and `b = 1`.

## Main definitions

* `Composability.Attack`: CPA, CCA1, CCA2.
* `Composability.FixedLengthScheme`: a `PrivateKeyScheme` with fixed-length ciphertexts.
* `FixedLengthScheme.indImpl`, `FixedLengthScheme.indGame`: the oracles and the experiment
  `IND_b`.
* `FixedLengthScheme.INDSecure`: [PS10, Definition 168.1].

## Main results

* `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
  the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
  once).

The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
phase of prong C, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.1, Definition 168.1 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The three attacks of [PS10, Definition 168.1]. -/
inductive Attack : Type where
  /-- Chosen-plaintext: `[Enc; Enc]`. -/
  | cpa
  /-- Non-adaptive chosen-ciphertext: `[Enc, Dec; Enc]`. -/
  | cca1
  /-- Adaptive chosen-ciphertext: `[Enc, Dec; Enc, Dec]`, `Dec` refusing the challenge. -/
  | cca2
  deriving DecidableEq

/-- A **private-key encryption scheme with fixed-length ciphertexts**: every encryption of an
`n`-bit message under a generated key has exactly `ct(n)` bits. -/
structure FixedLengthScheme extends PrivateKeyScheme where
  /-- The ciphertext length `ct(n)`. -/
  ctLen : PolyExpr
  /-- Ciphertexts of `n`-bit messages under generated keys have `ct(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin n → Bool) (r : enc.Coins n),
    (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) r).length = ctLen.eval n

namespace FixedLengthScheme

variable (S : FixedLengthScheme)

/-- The query lengths of the three oracles `Enc`, `Dec`, `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 3 → ℕ
  | 0 => n
  | 1 => S.ctLen.eval n
  | 2 => n + n

/-- The encryption oracle accepts `n`-bit messages. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = n := rfl

/-- The decryption oracle accepts ciphertexts of the fixed ciphertext length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.ctLen.eval n := rfl

/-- The challenge oracle accepts a pair of `n`-bit messages. -/
theorem inLens_two (n : ℕ) : S.inLens n 2 = n + n := rfl

/-- The answer lengths of the three oracles at parameter `n`; `Dec`'s answer is a validity flag
followed by the message. -/
def outLens (n : ℕ) : Fin 3 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => n + 1
  | 2 => S.ctLen.eval n

/-- Encryption returns the fixed ciphertext length. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl

/-- Decryption returns a validity bit followed by an `n`-bit message. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = n + 1 := rfl

/-- The challenge returns the fixed ciphertext length. -/
theorem outLens_two (n : ℕ) : S.outLens n 2 = S.ctLen.eval n := rfl

/-- The three oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens n) (S.outLens n)

/-- The IND oracle specification has the published input and output lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Whether `Dec` answers, given the attack and whether the challenge has been asked. -/
def decOpen : Attack → Bool → Bool
  | .cpa, _ => false
  | .cca1, challenged => !challenged
  | .cca2, _ => true

/-- CPA never opens the decryption oracle. -/
theorem decOpen_cpa (challenged : Bool) : decOpen .cpa challenged = false := rfl

/-- CCA1 opens decryption exactly before the challenge. -/
theorem decOpen_cca1 (challenged : Bool) : decOpen .cca1 challenged = !challenged := rfl

/-- CCA2 always opens decryption, with the challenge refusal checked separately. -/
theorem decOpen_cca2 (challenged : Bool) : decOpen .cca2 challenged = true := rfl

/-- The ciphertext `Enc_k(m)` with coins `r`, read at `ct(n)` bits. -/
def encryptAt (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode k (List.ofFn m)) r)

/-- Encryption is the padded reading of the underlying encryption machine's output. -/
theorem encryptAt_eq (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    S.encryptAt n k m r = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode k (List.ofFn m)) r) := rfl

/-- `Dec`'s answer `⟨1, m⟩` on a valid decryption `m`, and the all-`false` `⊥` otherwise. -/
def decAnswer {n : ℕ} : Option (Fin n → Bool) → (Fin (n + 1) → Bool)
  | some m => Fin.cons (α := fun _ => Bool) true m
  | none => zeroBits _

/-- A successful decryption is prefixed by its `true` validity bit. -/
theorem decAnswer_some {n : ℕ} (m : Fin n → Bool) :
    decAnswer (some m) = Fin.cons (α := fun _ => Bool) true m := rfl

/-- Failed decryption is the all-false answer. -/
theorem decAnswer_none (n : ℕ) : decAnswer (n := n) none = zeroBits (n + 1) := rfl

/-- The first and the second `n` bits of a `2n`-bit query: the challenge messages `m₀, m₁`. -/
def splitHalf {n : ℕ} (x : Fin (n + n) → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
  (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd n j))

/-- The first half of a challenge query consists of its first `n` bits. -/
theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl

/-- The second half of a challenge query consists of its final `n` bits. -/
theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl

/-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
once asked.
- `Enc` answers `Enc_k(m)` with fresh coins.
- `Dec` answers `⟨1, Dec_k(c)⟩` with fresh coins when it is open (`decOpen`) and `c` is not the
  challenge, and `⊥` (all `false`) otherwise; a ciphertext that fails to decrypt is `⊥` as well.
- `Challenge` answers `Enc_k(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, s)
  | 1, c, s =>
    if decOpen atk s.isSome && !decide (s = some c) then
      (ProbComp.sample (S.dec.Coins n)).bind fun r =>
        .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), s)
    else .pure (zeroBits _, s)
  | 2, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c)

/-- An encryption query samples fresh encryption coins and preserves the challenge state. -/
theorem indImpl_enc (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : Fin n → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, st) := rfl

/-- Decryption queries test oracle availability and refuse the recorded challenge before
running the decryption machine. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some c) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), st)
      else .pure (zeroBits _, st) := rfl

/-- A first challenge query encrypts the selected half and records that ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers: every decryption query gets `⊥`. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n k 1 c s = .pure (zeroBits _, s) := by
  simp [indImpl, decOpen]

/-- Under CCA2, `Dec` refuses the challenge: on the recorded challenge `c` it answers `⊥`. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n k 1 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, decOpen]

/-- A repeated challenge query returns the recorded challenge and changes nothing. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (c, some c) := rfl

/-- The encryption oracle accepts an `n`-bit message:
`(S.indSpec n).dom 0 = (Fin n → Bool)`. -/
theorem indSpec_encDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin n → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_zero]

/-- The encryption oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_encRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_zero]

/-- The decryption oracle accepts a ciphertext at the fixed ciphertext width:
`(S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_one]

/-- The decryption oracle answers a validity bit followed by an `n`-bit message:
`(S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_one]

/-- A challenge query contains two `n`-bit messages:
`(S.indSpec n).dom 2 = (Fin (n + n) → Bool)`. -/
theorem indSpec_challengeDom (n : ℕ) : (S.indSpec n).dom 2 = (Fin (n + n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_two]

/-- The challenge oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_challengeRng (n : ℕ) : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_two]

/-- The decryption equation on the query specification's type: with `c' = cast _ c` the
ciphertext read at width `ct(n)`, `S.indImpl atk b n k 1 c st` is
`if decOpen atk st.isSome && !decide (st = some c')` then a fresh `r ← Dec.Coins n` and the answer
`cast _ (decAnswer (decodeFin n (Dec.runAt n ⟨k, c'⟩ r)))` with state `st`, else `⊥` with `st`. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : (S.indSpec n).dom 1) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some (cast (S.indSpec_decDom n) c)) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (cast (S.indSpec_decRng n).symm (decAnswer (decodeFin n
            (S.dec.runAt n (pairEncode k (List.ofFn (cast (S.indSpec_decDom n) c))) r))), st)
      else .pure (zeroBits _, st) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n k c st

/-- The fresh challenge equation on the query specification's type: with
`⟨m₀, m₁⟩ = splitHalf (cast _ mm)`, `S.indImpl atk b n k 2 mm none` draws `r ← Enc.Coins n`,
sets `c = S.encryptAt n k m_b r`, and returns `cast _ c` with the state `some c`. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := S.encryptAt n k (if b then halves.2 else halves.1) r
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n k mm

/-- The encryption equation on the query specification's type: with `m' = cast _ m` the message
read at width `n`, `S.indImpl atk b n k 0 m st` draws `r ← Enc.Coins n` and answers
`cast _ (S.encryptAt n k m' r)`, keeping the state `st`. -/
theorem indImpl_enc_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : (S.indSpec n).dom 0) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        .pure (cast (S.indSpec_encRng n).symm (S.encryptAt n k (cast (S.indSpec_encDom n) m) r),
          st) := by
  simpa only [cast_eq] using S.indImpl_enc atk b n k m st

/-- The repeated challenge equation on the query specification's type:
`S.indImpl atk b n k 2 mm (some c) = pure (cast _ c, some c)`, the recorded ciphertext `c` read at
the challenge oracle's answer type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n k mm c

/-- The codec of the adversary: the three oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The IND codec decodes a move using the bit-string decoder at its oracle lengths. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The IND codec records a log entry as the oracle index paired with its query and answer. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The IND codec returns the false verdict when its budget expires. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (S.gen.runAt n [] rg)) (A.toComp (S.indCodec n) n q r) none).bind
    fun res => .pure (res.1 0)

/-- The IND experiment samples keys and adversary coins, simulates the recorded oracle
interaction from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (S.gen.runAt n [] rg))
        (A.toComp (S.indCodec n) n q r) none).bind fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security** [PS10, Definition 168.1]: for every non-uniform PPT `A` and
every polynomial query budget, `IND_0` and `IND_1` are indistinguishable: `A`'s advantage between
them is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- IND security is exactly negligible advantage for every PPT adversary and polynomial
query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one-oracle `bitCodec` machines to next-query machines (efficiency fill, T4)

The translators behind `Games.exists_toOracleAdversary_of_bitCodec` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T4"). A machine `B` against one
`bitCodec` oracle with a one-bit output reads `⟨[], log⟩` and writes `bitCodec` moves; a
next-query machine of the ch. 2–4 layer reads a history (`encodeHist`) and writes
`decodeOracleMove` moves. Two polynomial-time maps translate:
- `bridgePre` turns the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` into `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`,
  the empty input followed by the `bitCodec` log (the index of the only oracle is `1^0 = []`);
- `bridgePost` turns a canonical query word `⟨[false], ⟨[], x⟩⟩` into `⟨[false], x⟩`, the word
  `⟨[true], [true]⟩` into the verdict `[true, true]`, and every other word into `[true, false]`.

Both decoders check the payload length `ℓ₁(n)` themselves and agree on it, so neither map
needs the parameter.

## Main definitions

* `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.

## Main results

* `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
* `EffFill.bridgePost_spec`: the translated move is the decoded move.
* `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 96.1 (oracle indistinguishability against oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! ### The history translator -/

/-- The piece emitted for the suffix `w` of an encoded history: `⟨⟨[], fst w⟩, []⟩` for a
non-empty suffix, nothing for the empty one. -/
def relabelEmit (w : List Bool) : List Bool :=
  if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) []

/-- `relabelEmit w = if w = [] then [] else ⟨⟨[], fst w⟩, []⟩`. -/
theorem relabelEmit_eq (w : List Bool) :
    relabelEmit w = if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) [] :=
  rfl

/-- The pieces of the first `m` suffixes `w, snd w, snd (snd w), …`, concatenated. -/
def relabelN (m : ℕ) (w : List Bool) : List Bool :=
  (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w)

/-- `relabelN m w = ⋃_{i < m} relabelEmit (snd^i w)`. -/
theorem relabelN_eq (m : ℕ) (w : List Bool) :
    relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
  rfl

/-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x

/-- `relabel x = relabelN (|x| + 1) x`. -/
theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl

/-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)

/-- `bridgePre x = ⟨[], relabel x⟩`. -/
theorem bridgePre_eq (x : List Bool) : bridgePre x = pairEncode [] (relabel x) := rfl

/-- The empty word has no pieces: `relabelN m [] = []`. -/
theorem relabelN_nil (m : ℕ) : relabelN m [] = [] := by
  rw [relabelN_eq, List.flatMap_eq_nil_iff]
  intro i _
  have h : ∀ j, pairSndD^[j] ([] : List Bool) = [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  rw [h, relabelEmit_eq, if_pos rfl]

/-- One more suffix: `relabelN (m + 1) w = relabelEmit w ++ relabelN m (snd w)`. -/
theorem relabelN_succ (m : ℕ) (w : List Bool) :
    relabelN (m + 1) w = relabelEmit w ++ relabelN m (pairSndD w) := by
  rw [relabelN_eq, relabelN_eq, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- The history of a one-oracle `bitCodec` log, as (query, answer) pairs. -/
def logHist {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  L.map fun e => (e.2.1, e.2.2)

/-- `logHist L` maps each entry `⟨0, x, y⟩` to `(x, y)`. -/
theorem logHist_eq {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    logHist L = L.map fun e => (e.2.1, e.2.2) :=
  rfl

/-- **The pieces of an encoded history form the `bitCodec` log:** for every `m ≥ |L|`,
`relabelN m (encodeHist (logHist L)) = encodeLog L`.

**Proof sketch.** Induction on `L`. The empty history is `[]`, which has no pieces
(`relabelN_nil`). A non-empty history `⟨⟨x, y⟩, rest⟩` emits `⟨⟨[], ⟨x, y⟩⟩, []⟩` and continues
with `rest` (`relabelN_succ`, `encodeHist_cons`); the piece is the entry's `bitCodec` encoding
(`bitCodec_encodeEntry`, the index of the only oracle being `1^0 = []`), and the concatenation is
the nested pair (`GGMRed.pairEncode_append_right`, `encodeLog_cons`). -/
theorem relabelN_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ) :
    ∀ (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) (m : ℕ), L.length ≤ m →
      relabelN m (encodeHist (logHist L)) =
        (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L
  | [], m, _ => by
    rw [logHist_eq, List.map_nil, encodeHist_nil, relabelN_nil, MachineCodec.encodeLog_nil]
  | e :: L, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [logHist_eq, List.map_cons, ← logHist_eq, encodeHist_cons, relabelN_succ,
      pairSndD_pairEncode, relabelN_encodeHist dα L m (by rw [List.length_cons] at hm; omega),
      relabelEmit_eq, if_neg (pairEncode_ne_nil _ _), pairFstD_pairEncode,
      MachineCodec.encodeLog_cons, bitCodec_encodeEntry, ← GGMRed.pairEncode_append_right,
      List.nil_append, Fin.fin_one_eq_zero e.1, Fin.val_zero, List.replicate_zero]

/-- An encoded history has at least as many bits as entries. -/
theorem length_le_length_encodeHist {ℓ₁ ℓ₂ : ℕ} :
    ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)), h.length ≤ (encodeHist h).length
  | [] => Nat.zero_le _
  | p :: h => by
    rw [encodeHist_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeHist h
    omega

/-- **The history translator on a history:** `bridgePre (encodeHist (logHist L)) =
⟨[], encodeLog L⟩`. -/
theorem bridgePre_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    bridgePre (encodeHist (logHist L)) =
      pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L) := by
  rw [bridgePre_eq, relabel_eq, relabelN_encodeHist dα L _]
  have h1 := length_le_length_encodeHist (logHist L)
  rw [logHist_eq, List.length_map] at h1
  rw [logHist_eq]
  omega

/-- The emitted piece is polynomial-time. -/
theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
  (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (((polyTimeComputable_const []).pairEncode polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_const []))).congr fun w => by
    rw [relabelEmit_eq]
    by_cases h : w = []
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

/-- **The history translator is polynomial-time** (`Complexity.polyTimeComputable_iterateEmit`
with the step `pairSndD`, `|x| + 1` rounds and the orbit bound `|x|`). -/
theorem bridgePre_poly : PolyTimeComputable bridgePre := by
  have horbit : ∀ (x : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval x.length →
      (pairSndD^[i] x).length ≤ PolyExpr.var.eval x.length := by
    intro x i _
    clear * -
    rw [PolyExpr.eval_var]
    induction i with
    | zero => exact le_rfl
    | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih
  have h := polyTimeComputable_iterateEmit polyTimeComputable_pairSndD relabelEmit_poly .var .var
    horbit
  refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
  rw [bridgePre_eq, relabel_eq, relabelN_eq, PolyExpr.eval_var]

/-! ### The move translator -/

/-- **The move translator:** a canonical query word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`,
the output word `⟨[true], [true]⟩` becomes `[true, true]`, and every other word `[true, false]`. -/
def bridgePost (w : List Bool) : List Bool :=
  if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
    pairEncode [false] (pairSndD (pairSndD w))
  else if w = pairEncode [true] [true] then [true, true] else [true, false]

/-- The defining equation of `bridgePost`. -/
theorem bridgePost_eq (w : List Bool) :
    bridgePost w =
      if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
        pairEncode [false] (pairSndD (pairSndD w))
      else if w = pairEncode [true] [true] then [true, true] else [true, false] :=
  rfl

/-- **The move translator is polynomial-time** (`eq_poly` for the two tests). -/
theorem bridgePost_poly : PolyTimeComputable bridgePost := by
  have hx := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have h1 := eq_poly polyTimeComputable_id ((polyTimeComputable_const [false]).pairEncode
    ((polyTimeComputable_const []).pairEncode hx))
  have h2 := eq_poly polyTimeComputable_id (polyTimeComputable_const (pairEncode [true] [true]))
  refine (polyTimeComputable_ite h1 ((polyTimeComputable_const [false]).pairEncode hx)
    (polyTimeComputable_ite h2 (polyTimeComputable_const [true, true])
      (polyTimeComputable_const [true, false]))).congr fun w => ?_
  rw [bridgePost_eq]
  simp only [id_eq, decide_eq_true_eq]

/-- **The translated move is the decoded move.** For every word `w`, either `decodeBitMove`
reads the query `x` (to the only oracle) and `decodeOracleMove` reads the query `x` off
`bridgePost w`, or `decodeBitMove` reads an output `a` and `decodeOracleMove` the verdict `a 0`.

**Proof sketch.** Three cases on `w`. A word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`: if
`|x| = ℓ₁` both decoders read the query (`decodeBitMove_query`,
`decodeOracleMove_pairEncode_ofFn`); otherwise both read the default, the all-`false` output and
the verdict `false` (`decodeBitMove_of_not_canonical`,
`decodeOracleMove_pairEncode_false_of_length_ne`). The word `⟨[true], [true]⟩` reads the output
`1` on both sides (`decodeBitMove_ret`, `decodeOracleMove_true_two`). Every other word becomes
`[true, false]`, the verdict `false`; `decodeBitMove` reads either the output `0` (the word
`⟨[true], [false]⟩`) or the default (`decodeBitMove_of_not_canonical`); its query words are all
of the first form, since `1^i = []` for `i : Fin 1`. -/
theorem bridgePost_spec (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (∃ x : Fin ℓ₁ → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .query 0 x ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .query x) ∨
    (∃ a : Fin 1 → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .ret a ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .ret (a 0)) := by
  by_cases hq : w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w)))
  · rw [bridgePost_eq, if_pos hq]
    set xw := pairSndD (pairSndD w)
    by_cases hx : xw.length = ℓ₁
    · obtain ⟨x, hxe⟩ := exists_ofFn_eq hx
      refine Or.inl ⟨x, ?_, ?_⟩
      · rw [hq, ← hxe]
        exact decodeBitMove_query (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 0 x
      · rw [← hxe]
        exact decodeOracleMove_pairEncode_ofFn ℓ₁ x
    · refine Or.inr ⟨zeroBits 1, ?_, ?_⟩
      · refine decodeBitMove_of_not_canonical (fun i x h => hx ?_) (fun a h => ?_)
        · rw [hq, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero] at h
          have h' := congrArg (fun v => pairSndD (pairSndD v)) h
          simp only [pairSndD_pairEncode] at h'
          rw [h', List.length_ofFn]
        · rw [hq] at h
          have h' := congrArg pairFstD h
          simp only [pairFstD_pairEncode] at h'
          exact absurd h' (by decide)
      · rw [decodeOracleMove_pairEncode_false_of_length_ne ℓ₁ hx, zeroBits_apply]
  · by_cases hr : w = pairEncode [true] [true]
    · refine Or.inr ⟨fun _ => true, ?_, ?_⟩
      · rw [hr]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => true)
      · rw [bridgePost_eq, if_neg hq, if_pos hr]
        exact decodeOracleMove_true_two ℓ₁ true
    · rw [bridgePost_eq, if_neg hq, if_neg hr, decodeOracleMove_true_two]
      by_cases hf : w = pairEncode [true] [false]
      · refine Or.inr ⟨fun _ => false, ?_, rfl⟩
        rw [hf]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => false)
      · refine Or.inr ⟨zeroBits 1, ?_, by rw [zeroBits_apply]⟩
        refine decodeBitMove_of_not_canonical (fun i x h => hq ?_) (fun a h => ?_)
        · rw [h, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero, pairSndD_pairEncode,
            pairSndD_pairEncode]
        · have ha : List.ofFn a = [a 0] := by rw [List.ofFn_succ, List.ofFn_zero]
          rw [ha] at h
          cases h0 : a 0
          · rw [h0] at h; exact hf h
          · rw [h0] at h; exact hr h

/-! ### Evaluation -/

/-- **The two computations evaluate alike.** For a string function `D` (a machine with fixed coins),
the ch. 2–4 tree of the next-move function `h ↦ decodeOracleMove ℓ₁ (bridgePost (D (bridgePre
(encodeHist h))))` from the history of a log `L`, evaluated against `f`, is bit `0` of the
`bitCodec` computation of `L ↦ decodeBitMove (D ⟨[], encodeLog L⟩)` from `L`, evaluated against
`f` at the only oracle; for every budget.

**Proof sketch.** Induction on the budget, generalizing the log. The history translates to the
log (`bridgePre_encodeHist`), so both next moves come from the same word, and `bridgePost_spec`
gives corresponding moves. An output `a` gives the leaf `a 0` against the leaf `a`
(`buildTree_*_of_ret`, `buildComp_*_of_ret`). A query with the budget spent gives the verdict
`false` against `zeroBits 1`, whose bit `0` is `false`. A query `x` within budget asks `f x` on
both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`), and the continuations agree by
induction, since the history of `L ++ [⟨0, x, f x⟩]` is that of `L` followed by `(x, f x)`. -/
theorem eval_buildTree_bridge (ℓ₁ ℓ₂ : ℕ) (D : List Bool → List Bool)
    (f : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)) :
    ∀ (q : ℕ) (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))),
      (buildTree (fun h => decodeOracleMove ℓ₁ (bridgePost (D (bridgePre (encodeHist h))))) q
          (logHist L)).eval f =
        (buildComp (fun L => decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1
            (D (pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))))
          (zeroBits 1) q L).evalFn (fun _ => f) 0 := by
  intro q
  induction q with
  | zero =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_zero_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_query hb, QueryTree.eval_ret, OracleComp.evalFn_pure, zeroBits_apply]
    · rw [buildTree_zero_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]
  | succ q ih =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_succ_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_query hb, QueryTree.eval_query, OracleComp.evalFn_query]
      have hh : logHist L ++ [(x, f x)] = logHist (L ++ [⟨0, x, f x⟩]) := by
        rw [logHist_eq, logHist_eq, List.map_append, List.map_singleton]
      rw [hh]
      exact ih (L ++ [⟨0, x, f x⟩])
    · rw [buildTree_succ_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]

end TCSlib.Cryptography.Games.EffFill
