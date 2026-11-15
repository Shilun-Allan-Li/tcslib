# Fill `prf-long` · checkpoint 1 · D1 and D2

**Worker** Claude. **Unit** `prf-long` (ruling B3: the PRF machinery of [PS10, Theorem 99.2] at `ℓ(n)`-bit
outputs). **Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` (`cryptography/pass-shelat-ch2-4`), read
from the exchange at `b97d359517f8cebbf7e03071e30bc21e66c8403e` (pack verified: `evidence/logs/inputs-check.log`).
**Proof branch** `fill/prf-long` (local); at this checkpoint one commit over the base,
`94e7c1eb09f8cfd27389d5282962e3e95bdf4bcf`.

This unit proves no admitted target and removes no `sorry`.

## Checkpoint 1 (brief: D1 and D2)

### D1 · `Pseudorandom/Functions/Asymptotic/Defs.lean` (447 → 480 lines)

```lean
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q)

theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n))
```

Both as drafted. Re-derived: `prfAdv_toOracleAdversary := prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q`
(the explicit `ℓ₂ := .var` is needed: without it the elaborator must solve `PolyExpr.eval ?ℓ₂ n =?= n` and times
out) and `PRF.negligible_prfAdv := hF.pseudorandom.negligible_prfAdv D q`.

### D2 · `Encryption/PrivateKey/FromPRF/Hybrid.lean` (349 → 511 lines)

All names and signatures as drafted, in `section Concrete` with the added variable `{l : ℕ}`:
`prfEncRealOut` (+`prfEncRealOut_apply`), `otpEncOut` (+`otpEncOut_apply`), `multiMsgAdvOut`,
`eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy`, `acceptProb_oracleDist_multiMsgAdvOut`,
`prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut`, `distAdv_prfEncRealOut_le`,
and the three `rfl` bridges `prfEncReal_eq_prfEncRealOut`, `otpEnc_eq_otpEncOut`,
`multiMsgAdv_eq_multiMsgAdvOut`. Binder note: `prfEncRealOut_apply`, `eval_multiMsgAdvOut`,
`multiMsgAdvOut_boundedBy` and the bridges carry `omit [Fintype K]`/`omit [Fintype ρ]` exactly as their `n`-bit
originals do (otherwise the section's instance arguments would be included and the `n`-bit re-derivations, which
omit them, could not supply them).

**Re-derived** as the case `l = n` (through the bridges): `prfEncReal_apply`, `eval_multiMsgAdv`,
`multiMsgAdv_boundedBy`, `acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`,
`distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`, `distAdv_prfEncReal_le`; their `**Proof sketch.**`
paragraphs now say "the case `l = n` of …", and the full sketches moved to the `Out` lemmas. `chainTree`,
`uprob_not_injective_le` and `pushesUniform_comp_injective` are reused as they are (the collision bound concerns
the `n`-bit points only).

The new declarations sit before the `n`-bit ones they serve (the base declarations keep their relative order).

## Frozen-statement check

`evidence/headers/headers-cp1.txt` (tool `evidence/tools/headers.py`): every base declaration of the seven
scope files (`Asymptotic/Defs`, `FromPRF/Hybrid`, `FromPRF/ReductionMachine`, `FromPRF/HybridLemmas`,
`FromPRF.lean`, `Pseudorandom/Functions.lean`, `Encryption/PrivateKey.lean`) is present in the same order, with
its header, its `omit … in` lines and its statement prose (the docstring before `**Proof sketch`) byte-identical,
and every `def`/`abbrev`/`structure`/`instance` byte-identical in full: **0 differences**. Control
(`evidence/headers/control-cp1.txt`): one character changed in the header of `distAdv_prfEncReal_le` is reported
as exactly one difference.

## Checks at this checkpoint

* **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; no cgroup memory limit, headroom = MemAvailable
  ≈ 15.5 GiB; disk 11.0 GiB free at first (below the 12 GiB floor), so I removed only this session's own
  finished worktrees (`/workspace/prfbase`, `/workspace/folds`; their branches keep their commits): 14.15 GiB free.
* **Packages and cache.** `.lake/packages` is a symlink to this host's populated tree at exactly the
  manifest's pins (the addendum's alternative; the manifest at `7b307d62` is byte-identical to that tree's).
  `evidence/logs/packages-check.log`: "packages: 11 match, 0 mismatch, 4 absent". The 111 Mathlib roots
  computed from `order.txt` equal `roots.txt`; the narrowed `lake exe cache get` (111 roots) exited 0, "No
  files to download" (2,400 decompressed from the cache tool's existing store of 2,402 archives, populated by
  earlier sessions on this host: `cache-store.log`); no zero-size olean; probe `import
  Mathlib.Algebra.BigOperators.Field` passed (`cache-probe.log`).
* **Bootstrap** (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`): 434/434 exit 0, 0 error
  diagnostics with `^\S+\.lean:\d+:\d+: error[:(]` (`evidence/base/bootstrap-errors.txt`). Its history
  (`bootstrap-run.log`): the first background loop ran `sweep.py` without `-I` for 8 modules and was restarted
  with `python3 -I`; I paused it after 176 modules to try the edits, then restored the base sources and rebuilt
  every module from position 149 (the first owned module) at the base before finishing (first-pass rows in
  `bootstrap-pass1.tsv`).
* **Base sorry census** (`evidence/base/sorry-census-base.txt`): 40 declarations in 19 modules, equal to
  `base-sorries.txt`.
* **Checkpoint sweep** (`evidence/cp1/`): every module of `order.txt` from position 149 (`Asymptotic/Defs`, the
  first owned module) to the end (`order-cp1.txt`, 286 modules), at this checkpoint's tree (the 148 modules
  before it import nothing that changed and were checked in the bootstrap): **286/286 exit 0, 0 error
  diagnostics** (`sweep-errors.txt`, per-module rows `sweep.tsv`, raw logs `sweep/`). Sorry census over all
  434 modules (checkpoint logs first, bootstrap logs for the first 148): `sorry-census-cp1.txt`, **identical**
  to the base census (40 declarations in 19 modules).
* **Axioms at this checkpoint** (`evidence/axioms/axioms-cp1.log`, tool `axioms.py`): all 152 stored constants
  of `Asymptotic/Defs` and `FromPRF/Hybrid` depend on at most `propext`, `Classical.choice`, `Quot.sound`; the
  135 base constants of these two modules that are still stored have the same axiom lists as at the base
  (`axioms-base.log`); the five endpoints of the brief: `[Classical.choice, Quot.sound, propext]`, as at the
  base. Disclosed: two **auto-generated** equation lemmas, `multiMsgAdv.eq_1` and `otpEnc.eq_1`, were stored
  in `Hybrid`'s olean at the base only because the base proofs unfolded these definitions with
  `rw [multiMsgAdv, …]`/`simp only [otpEnc, …]`; the re-derived proofs go through the `rfl` bridges instead,
  so the lemmas are no longer realized there. They are not source declarations, nothing names them, and any
  later `rw`/`simp`/`unfold` realizes them on demand (the sweep above is clean).
* **Width and size** (`evidence/checks/widths-cp1.txt`): no new line over 100 characters; the over-long lines
  listed there are byte-identical base lines inside frozen headers, which the frozen-statement rule keeps.
  Files ≤ 1000 lines.
* **Sketches** (`evidence/checks/sketches-cp1.txt`): every proof of 15 lines or more has a sketch.
* **Lint** (`evidence/lint/`): base 92 FAIL / 101 WARN (re-run at `7b307d62`: as the brief states), checkpoint
  92 / 101. Line-set diff: no new FAIL; one WARN line **changed**, disclosed: `Hybrid.lean`'s check-8 line goes
  from "2 … chainTree, otpEnc" to "1 … chainTree", because the bridge `otpEnc_eq_otpEncOut` is a lemma named
  after `otpEnc` (the effect the brief anticipates).
* **Seals, controls, unfold scan**: base runs done (`evidence/seals/base/`, `evidence/base/rwids/`); the final
  runs come with the final delivery.

## Overlap and reuse (checkpoint 1)

| New declaration | Nearest relative | Relation |
|---|---|---|
| `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Asymptotic/Defs.lean:430,441` `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` | generalization to `ℓ₂`; the originals are **re-derived** from them. `SecureComputation/SpecialEncryptionSecurity.lean:67` `prfOut_var_iff` (DL-8) relates `PRFOut .var` to `PRF`; the new lemma takes `PRFOut`'s clause (2) as its hypothesis, as the brief requires (no import of `SecureComputation`). |
| `prfEncRealOut`, `otpEncOut`, `multiMsgAdvOut` and their lemmas | `FromPRF/Hybrid.lean:95,108,118,…,321` the `n`-bit originals | generalization to `l`; every listed original is **re-derived** (no ledger row). |
| `distAdv_prfEncRealOut_random_otp_le` | `Hybrid.lean:243`; `HardcoreBit.pushesUniform_restrict` (DL-2) via `pushesUniform_comp_injective` | reuses `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` as they are. |
| `acceptProb_otpEncOut` | `Hybrid.lean:286`; `zipWith_xor_ofFn_add` (DL-2) | same Boolean-group relabelling; the original is re-derived. |

Searches: `evidence/overlap/dupsearch-base.log` (`evidence/tools/dupsearch.sh` on the issue base).

## Scope requests

None.

## Next

Checkpoint 2: D3 (the string layer at answer width `ℓ(n)`, `exists_queryChainOut_nuppt`, `exists_oneQuery_nuppt`,
the re-derivation of `exists_queryChain_nuppt`). Final: D4 (`FromPRF/MultiMsgOut.lean`), the re-derivations in
`FromPRF.lean`, the B1 consumer map, the full sweep and evidence. All of it already compiles locally.

## Patches and reproduction

`patches/0001-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer set from `COMMITS.tsv`, and reproduces the hash and the tree
(`evidence/amcheck/amcheck-cp1.log`).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, sources of probes and seals, tools); the
top-level `SHA256SUMS` covers every delivered file except itself; both checked against the delivered paths.
