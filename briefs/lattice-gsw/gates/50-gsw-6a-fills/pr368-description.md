## Why

Seyoon ruled **Q-C1** on 2026-11-17 (decision log `LatticeCryptographyPlan.md`). It resolves finding **G6B-C1-F03** of `briefs/lattice-gsw/phase6/checkpoint1-6b-review.md`:

- **The G6 fill needs a lemma that is private.** The fill of `decryptFormula_eval` needs the step `c_last − ⟨s, c_init⟩ = ⟨t, decryptColumn P C⟩`, where `t = (−s, 1)`. That step exists only inside the private `decrypt_eq_decode_errorSum`. A 6b file must not copy private material across files (the GF-F02 pattern).
- **The ruling.** The lemma becomes an owner-side public lemma in `GSW/Scheme.lean`. It lands with the `hybridPlant` reader before the 6b fills.
- **The reader census.** The 6b reader census (`briefs/lattice-gsw/phase6/issued-6b-r1/census.txt`) lists `hybridPlant` as `MISSING`. The statement job adds `decrypt_eq_decode_dotProduct` to the census as MISSING too.

## Changes

There is one signed commit, `1953898b18a33ab2cd533820c5754a1aacffeb44`, on the records tip `55f553715f280be36827ad86a94c93db39ec56c3`. That tip is Lean-equal to the T of snapshot #7, `a1fa7b65`. The diff is +33/−12.

1. **`GSW/Scheme.lean`**
   - New public lemma `decrypt_eq_decode_dotProduct (P) (s) (C) : decrypt P s C = LWE.BitEncoding.decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)`.
     - It sits right after `decrypt_eq`.
     - Its docstring states the formula, cites [GSW13, §3.1, `Dec`; BV14, §3.1, `NCCrypt.Dec`] like the file's other docstrings, and has a proof sketch.
     - It is step 1 (`hsplit`) of the private `decrypt_eq_decode_errorSum`, promoted.
   - Only the **proof body** of `decrypt_eq_decode_errorSum` changes: `hsplit` is replaced by `rw [decrypt_eq_decode_dotProduct, decryptColumn_eq]`, and the redundant `rw [decrypt_eq, Regev.decrypt_eq]; dsimp only; rw [hsplit, …]` becomes `rw […]`. Its statement and docstring are unchanged.
2. **`Encryption/PublicKey/EnsembleSecurity.lean`**
   - New definitional reader `hybridPlant_eq … (pc) (r) : hybridPlant E m m' j D pc r = D (pc.1, fun i => if i < j then … else if i = j then pc.2 else …) r.2 := rfl`.
   - It sits beside `hybridPlant` and follows the file's reader style (`pkEncDist_eq`).

The brief gave `PrivateKey/EnsembleSecurity.lean`. `hybridPlant` is actually in `PublicKey/EnsembleSecurity.lean:110`, which is also the path the census gives.

**Search for existing equivalents.** No equivalent of either lemma exists:

- Neither name occurs in `TCSlib/` or `audits/` at the tip, on `land/gsw-6a-fills` (#366, `ccca6f80`), or in the 6b statement delivery (exchange `1e0647b9`, `src/`, `src-o2/` and both patch series). Both files are identical on #366, and the 6b delivery does not touch them.
- The residual step occurs nowhere else in TCSlib. It needs GSW's `secretVector` and `decryptColumn`, so it cannot be in Mathlib.
- The `hybridPlant` reader has no counterpart either. `distAdv_tuple_le_sum` in `Hybrid.lean` inlines the lambda and has no reader.

## Checks (replay on snapshot #7)

| Check | Result |
|---|---|
| Copy | `cp -al` of snapshot #7 → `olean-replay-6b-prereq`; Mathlib overlay with 3346 symlinks; NthRootLemmas `c0a9cff0…` (lean rc 0) |
| Export | `git archive` of the head, checked blob for blob: 1586 files, 0/0/0 |
| Plan | 2 changed files, 67 downstream modules. Build 67, reuse 1367, full order 1434 |
| Build | One module at a time through `runner.py`, with the slot gate before each module (0 waits). `Scheme` was moved first; the queue is a permutation of the plan |
| Result | 67 modules: rc≠0 0, `error:` 0, `error(` 0, sorry 0. The 1 warning is the existing unused simp argument in `MAC/FromPRF.lean:129`, which earlier replays also report |
| State | `stateplan update` took 67 modules; `check` over 1434 modules gives **RESULT OK** |
| Links | All 67 rebuilt oleans have link count 1 and match their records |
| Snapshot #7 | Rehash **0/0/0** before the build, after it and at the end (map `5105c514…`) |
| Output map | 1465 entries, `6247b348…`. Only `Scheme` and `EnsembleSecurity` differ from #7 |
| Admissions | **192 in 44 modules** at both the tip and the head, identical per module. The 67 rebuilt modules have 0 |
| Axioms | `decrypt_eq_decode_dotProduct`: `propext`, `Classical.choice`, `Quot.sound`. `hybridPlant_eq`: none. Private `decrypt_eq_decode_errorSum`: standard (exactly one constant matched). `decrypt_of_encrypts`, `_dyadic`, `decrypt_keygen_encrypt` and `distAdv_multi_le_sum`: standard. No `sorryAx`. Both readers are applied once in the probe |
| decls2 (`fa81981a`) | **2 ADDED, 0 CHANGED, 0 REMOVED** |
| touched | 2 ADDED, 1 CHANGED (the private `decrypt_eq_decode_errorSum`, proof body only), every other declaration UNCHANGED |
| Coe-A seals, base vs head | `Scheme`: 101 requests, 0 errors on both sides. `EnsembleSecurity`: 1268 requests, 6 errors on both sides, in the same 4 declarations (`bitwiseEncFun_poly`, `bitwise_enc_runAtL`, `singleBitSecure_iff`, `Secure.multiMessageSecure`). Those failures are at the base already. **0 new failures**, and install and EOF records are present everywhere |
| Lint | `campaign_style_lint --check8b` on `TCSlib/Cryptography`: 92 FAIL / 103 WARN at both the base and the head, with the same FAIL set. The one changed WARN is check 8 for `EnsembleSecurity`, which drops `hybridPlant` (4 → 3 defs without a reader). `style_lint` finds 0 problems in both files. No new lines are over 100 characters |
| Slots | At most one Lean process of this job at a time, with a check before each one. 0 waits |

## Gating

Gated with the 6b fills or the next small-items gate, as Seyoon decides.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_
