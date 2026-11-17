# gsw-6b-statements · checkpoint 1 (Claude, lead + 2 sub-agents)

**Heads (full hashes).**
- Series 1 `owner/o2-decode`: **`dd84941f747bca798c2a5a792616f5ead21cfa0b`** (1 commit, O2).
- Series 2 `stmt/gsw-6b` at this checkpoint: **`57815173072bf8c145a4bb774797989061fe96f4`** (2 commits on
  O2: `6e01df6c7d5a4f36e92000040d8c83322cb7fef7` Branching + DecryptFormula,
  `57815173072bf8c145a4bb774797989061fe96f4` Bootstrap + Circular).
- Base: **`3e51b5f28900db6190f1eb2e6d207d27ee15d541`** (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`).

This checkpoint claims: the base reproduced; **O2 complete** with its checks 1, 3, 4, 5, 6 and 8; and
`GSW/Branching`, `GSW/DecryptFormula`, `GSW/Bootstrap`, `GSW/Circular` **compiled at the checkpoint head**
(rc 0, 0 errors, only the targets' `sorry` warnings). `patches/` run to both heads, `src/` holds every
file changed between the base and the checkpoint head (the four GSW files and `BitEncoding.lean`),
`src-o2/` holds `BitEncoding.lean` at the O2 head. The remaining files (Leveled, LeveledSecurity,
LWE/Ratio, PolyRatio, Asymptotic, the facades) are written and compile locally; they are **not claimed
here** and arrive with the final.

## 1. Base

`tools/mkbase.sh` in a fresh clone (branches fetched by name; both `land/` branches were at their pinned
heads, `cryptography/pass-shelat-ch2-4` at `3c14bfc42691cb2344351bda9ce86172b829089c`):

```
STEP1 04947bcf35e08ed5f3a4902b2637a77482fd32d2 tree 8eca961769fef59d5a22fd1b46dc821a614daf06
BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde
```

(`evidence/logs/mkbase.log`). Pack verified: `SHA256SUMS` 25/25 OK, `inputs/SHA256SUMS` 8/8 OK. Records
inputs at `e913abe549843088a6cddf541b24e94a2d316f23` match the brief's SHA-256 (`decls2.py fa81981a…`,
`MAINTAINER-HANDOFF.md ec3789a1…`, `duplication-ledger.md d500c17e…`, `policy.md 6599b122…`;
`evidence/records/SHA256-at-e913abe5.txt`). The records branch notes Seyoon's **Q-6B-1 ruling: reader-only
(option A)**, which this job applies.

## 2. Environment, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, hierarchical limit 14,338,760,704 B
  (13.35 GiB), memory in use (usage − cache + shmem) 214,929,408 B, **headroom 13.15 GiB**; disk 23.4 GB free
  (ext4) after making the exchange worktree sparse. Toolchain `leanprover/lean4:v4.25.0` installed by elan after
  the preflight.
- **Cache.** Store absent before the first fetch (`evidence/logs/cache-store.log`). Prefix roots (105) fetched:
  2,345 files downloaded, 0 failed (`cache-get-prefix.log`). Packages: every present package matches the
  manifest; ABSENT `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` (`packages-check.log`). No empty oleans.
- **Pool** (`evidence/logs/pool.log`): `min(nproc, headroom/4 GiB) = 3` slots, a counting semaphore of `flock`
  slot files shared by all agents (tools `evidence/tools/lead/poollib.py`, `pool_run.py`, `pbuild.py`, copied
  from the 6a fills with the pool path changed). Lowest MemAvailable seen at an acquisition 12.0 GB; peak RSS
  of one process 5.7 GB (a seal run). The pool size was not changed.
- **Who wrote what.** The lead wrote O2 and every statement file and made every commit. Two sub-agents
  (each with its own worktree and olean tree, seeded by copying the lead's TCSlib oleans after a source-identity
  check, `evidence/subagents/seed-check.txt`): **`seal`** (Rule 10 seals, controls, unfold scan) and **`probe`**
  (probes, reader census, clash/shadow and duplication scans). This differs from the brief's suggested split
  (`lev`/`asy` writing statements): with the files depending on each other's definitions, the lead wrote all
  statements and delegated the verification streams instead.

## 3. O2 (series 1)

`LWE/BitEncoding.lean`, after `decode_eq`: `decodeLo` (`= q/2/2 + 1`, reader `decodeLo_eq`), `decodeHi`
(`= (q + q/2 + 1)/2`, reader `decodeHi_eq`), and **`decode_iff_mem_Ico`, proved** (25 proof lines: Mathlib's
`ZMod.valMinAbs_def_pos`, `ZMod.val_sub`, `ZMod.val_natCast_of_lt`, `ZMod.natCast_self`,
`ZMod.natCast_zmod_val`, the file's `decode_eq`/`distance_eq`/`codepoint_eq`, then `omega`), with a formula
docstring, "Glue for the file's `decode`", and a proof sketch; the module docstring's Main definitions/results
gain one entry each. It does not re-prove `decode_codepoint_add`.

| Check | Result |
|---|---|
| decls2 vs base (`evidence/stmt/decls2-o2.txt`) | **5 ADDED, 0 CHANGED, 0 REMOVED** |
| Frozen check (`evidence/headers/frozen-o2.txt`) | 0 violations: 12 base declarations identical, 5 allowed additions, text changes insertions only. Controls: one altered character in `decode_eq` → exactly 1 header difference; deleting `codepoint_eq` → exactly 1 removal |
| Sweep at O2 head (`evidence/build/sweep-o2/`) | the 18 `DOWN` modules rc 0, 0 errors (both forms), 0 `sorry` |
| Admissions | O2 head = base: 289 in 55 modules (syntactic scan `evidence/admissions/graph/o2/sorries.txt`, identical to `base-sorries.txt`); the 18 swept modules carry none |
| Axioms (`evidence/stmt/axioms-summary.txt`) | 31 constants of `BitEncoding` (source byte-identical at O2 and the final head), only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| Rule 10 (`evidence/rule10/o2/`, `final-bitenc/`) | seals A, B, coe-A, coe-B: 9 requests each, install 9/9 and EOF 9/9, 0 errors, no failing declaration, at the O2 head and the final head (same source, same closure). Controls on `decodeLo`: unsealed 0 errors; strict and coe negative read by `rfl` fails exactly once, inside the example; positive through `decodeLo_eq` 0 errors. Unfold scan: 0 foreign |

## 4. The four checkpoint files (series 2, commits 1–2)

All compile at `57815173` (`evidence/build/sweep-cp1/summary.tsv`: the 18 `DOWN` modules and the 4 new ones,
22/22 rc 0, 0 errors in both forms, source SHA-256 bound to `git show HEAD`). Admitted targets: Branching 3
(`Encrypts.select`, `encrypts_homEvalPBP`, `encrypts_homEvalFormula`), DecryptFormula 6
(`vecMul_secretVector_eq_sum`, `decryptFormula_eval`, `nandFormula_eval`, `depth_nandFormula_le`,
`maxFanin_nandFormula_le`, `decDepth_le`), Bootstrap 5 (`encrypts_bootNAND`, `decrypt_fheEval`,
`decrypt_fheEvalCircuit`, `decrypt_keygen_fheEvalCircuit`, `bootNoise_le`), Circular 1
(`distAdv_fheView_noEvk_le`). **G11 `encrypts_evalKey` is proved** (`rw [evalKey_eq]; exact
encrypts_encrypt …`). G14 is reader-only (`weakCircularSecure_iff`, Q-6B-1 A). decls2 at this head: 68 ADDED,
0 CHANGED, 0 REMOVED (`evidence/stmt/decls2-cp1.txt`).

Constants settled now (r3 *(fix)*): `decDepth_le : decDepth P ≤ 9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`
(F10's closed form with `⌈log₂ q⌉ ≤ ℓ`); `bootNoise_le : bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2β)`
(`c₀ = 33, c₁ = 9, c₂ = 2`: `decDepth + 1 ≤ 9a + 2b + 22` and `4^⌈log₂ y⌉ ≤ 4y²`, so `4^(decDepth+1) ≤
4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4`). The full derivations, the statement list and the row map come with
the final.

Lint at the final head already passes (`campaign_style_lint` FAIL/WARN line sets identical to the base,
92/104; `style_lint` 0 findings) and every file is at most 100 characters wide; details in the final.

## 5. Scope requests, questions

None so far. One process note: early in the session the lead stopped its own stray `git clone` with
`pkill -f` instead of by recorded PID (the handoff's rule 4); no other process was affected.

## 6. Reproduction

`evidence/repro-cp1.log`: in a scratch clone at the base, `git am` of `patches/o2` then `patches/stmt` with
`COMMITS.tsv`'s committer data and signing off reproduces all three hashes; `src/` and `src-o2/` equal the heads'
files byte for byte. All commits are unsigned (signing column `none`).

## 7. Evidence

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` every delivered file. Sub-agent
output delivered here is limited to the O2 Rule 10 runs; the rest arrives with the final.
