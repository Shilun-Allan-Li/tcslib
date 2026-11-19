# Fill gsw-6b-u14-u16 — checkpoint 1 (GSW 6b units U14 and U16: bootstrapping and the leveled scheme, G9–G13, G18, L2, L3)

**Unit** `gsw-6b-u14-u16` · **Worker** Claude (lead, alone; no sub-agent was used, so the brief's `lev` split did not
apply and the lead wrote both files) · **Base** B6 `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree
`845bdc982fd8f79aba755796bb13188922c4655d`) · **Head** `9852429ef14ce063fcf11ff860e7262f92063d55` (local branch
`fill/gsw-6b-u14-u16`, two commits, one owned file each) · **Records pin** `27e53754d28703907571cacbaf905b441e03c393` ·
**Lean** 4.25.0, Mathlib `029db123ddaa`.

**Status: checkpoint 1, carrying the whole fill. All seven targets are proved, and so is the one public helper
`encrypts_bootGate`.** Neither owned file contains `sorry`. The brief asked checkpoint 1 for the helper, G9 and G13
proved and L2 outlined. This checkpoint delivers all seven with the full C1–C13 payload (COMMON §8: a checkpoint carries
the full payload for what it claims).

| Row | Target (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | File | Base line → head line | Status |
|---|---|---|---|---|
| G9 | `encrypts_bootNAND` | `GSW/Bootstrap.lean` | 235 → 237 | proved |
| — | `encrypts_bootGate` (public helper, Q-6BF-3 A) | `GSW/Bootstrap.lean` | new → 270 | proved |
| G10 | `decrypt_fheEval` | `GSW/Bootstrap.lean` | 264 → 329 | proved |
| G18 | `decrypt_fheEvalCircuit` | `GSW/Bootstrap.lean` | 282 → 381 | proved |
| G12 | `decrypt_keygen_fheEvalCircuit` | `GSW/Bootstrap.lean` | 322 → 423 | proved |
| G13 | `bootNoise_le` | `GSW/Bootstrap.lean` | 344 → 490 | proved |
| L2 | `encrypts_leveledEval` | `GSW/Leveled.lean` | 243 → 244 | proved |
| L3 | `decrypt_keygen_leveledEvalCircuit` | `GSW/Leveled.lean` | 277 → 337 | proved |

**Axioms.** At the head on B6, every target and the helper depend on `[propext, Classical.choice, Quot.sound]` and on
`sorryAx`. The `sorryAx` reaches them only through the frozen U12/U13 targets the brief allows:
`encrypts_homEvalFormula`, `nandFormula_eval`, `depth_nandFormula_le`, `maxFanin_nandFormula_le` and `decDepth_le`
(C5). As a separate information check, I merged the head with the records tip, which already contains the landed U12
and U13 proofs. In that merge, all eight constants depend on `[propext, Classical.choice, Quot.sound]` only, and the
census finds 0 `sorryAx` traces among the 65 constants of the two modules (`logs/merge-check.log`).

**Scope.** One public declaration was added, the ruled `encrypts_bootGate`. One private helper was added,
`four_pow_clog_le` in `Bootstrap.lean`. No import was added. No statement, header, statement prose, definition, reader,
G11 or L1 changed. Neither file contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque`.

## 0. Inputs, base, records tip

- **Inputs (COMMON §1).** All 17 SHA-256 values match at the pin (`logs/inputs-check.log`). The table's `wave1/rulings.md`
  is `briefs/efficiency-gaps/wave1/rulings.md`. The folder `issued-6b-fills-r1` verifies with `sha256sum -c
  SHA256SUMS`: 52 files, all OK, and the paths are equal, with nothing missing or extra. **The folder's `rulings.md` is
  present** (`855ea62b…`): every question is ruled A. Q-6BF-3 A allows exactly two public helpers for 6b fills. This unit
  owns one of them, `encrypts_bootGate`; the other, `Parameters.ofFamily_columns_le`, belongs to U18-U19.
  Read: the brief, COMMON.md, dup-sweep.md (§0 and §U14-U16), the README, `rulings.md`, the addendum, and the §1 inputs
  as they bear on this unit.
- **Base check.** `git rev-parse bff0567b… bff0567b…^{tree}` gives `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` and
  `845bdc982fd8f79aba755796bb13188922c4655d`, as in the brief. The 224 sources of `order.txt` match `SOURCE-SHA256SUMS`
  (`logs/source-sha256.log`). `order.txt`, `roots.txt` and `closures.txt` are the pack's own.
- **Records tip seen at delivery** (`cryptography/pass-shelat-ch2-4`): `f46a2ae434fe16ab81187ea547487a65bcfffd28`. The
  base is an ancestor of it. Between the base and the tip, under `TCSlib/`, only `GSW/Branching.lean` (U12) and
  `GSW/DecryptFormula.lean` (U13) differ. `git merge-tree --write-tree 9852429e… f46a2ae4…` is clean, with tree
  `72f7452519dedd12878a72c77d7249597f00dd4e`. This is information only: `logs/merge-check.log` rebuilds Branching,
  DecryptFormula and the 9 `UNIT-DOWN` modules on that merge (all rc 0), and its axioms census is the one quoted above.
  The scratch worktree and commit were not delivered and have been removed.

## 1. Environment (addendum Part 1; COMMON §3)

- **Preflight** (`logs/preflight.log`). The host has 4 CPUs. The cgroup v1 limit is unlimited, so the headroom is
  `MemAvailable` = 15.3 GiB, against a floor of 4 GiB. The clone's filesystem (ext4, `/dev/vda`) had 17.35 GiB free,
  against a floor of 12 GiB. Result: `PREFLIGHT PASS`. To make that space, two things were done:
  - The worktree of this host's delivered U13 fill (`/workspace/u13`) was removed. Its branch is kept, and it landed as
    #392.
  - The exchange worktree was switched to a sparse checkout of this delivery's folder only. The branch and its history
    are untouched.

  No dependency tree was copied, moved or deleted.
- **Clone.** `/workspace/u1416` is a separate git worktree of the local repository at B6, on branch
  `fill/gsw-6b-u14-u16`.
- **Cache.** The store (`logs/cache-store.log`) held 2403 archives (120576651 B) from this host's earlier fills; this
  session downloaded nothing. The narrowed `lake exe cache get` for the 102 roots (`logs/mathlib-roots.txt`) said "No
  files to download", decompressed 2339 files and exited 0 (`logs/cache-get.log`). No olean among the 2348 has zero
  size (`logs/zero-size-oleans.log`). The cache probe elaborates (`logs/cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`logs/packages-check.log`): `RESULT: all present packages match the manifest`. Four packages are ABSENT,
  as for U13.
- **Pool** (`logs/pool.log`). With `nproc` 4 and `MemAvailable` 16.0 GB, `min(nproc, MemAvailable/4 GB)` is 4. I ran
  **3**, the local-host cap. No other agent ran Lean on the machine.
  - `pool_build.py` reached a peak of 3 concurrent processes in the bootstrap and 2 in the head sweep.
  - The seals ran under `xargs -P 3`.
  - Every other Lean run (scratch compiles, probes, controls, the explicit-unfold scan, the merge check) ran alone, one
    process at a time. None overlapped the pool runs.

  The peak max RSS of one Lean process was 2947048 KiB. There was no OOM and no exit 137.
- **Bootstrap** (`logs/bootstrap.log`, 00:26:02Z–00:33:14Z): 224/224 modules rc 0, with 0 errors. The `sorry` census
  equals `base-sorries.txt` exactly: 42 declarations in 16 modules (`logs/census-bootstrap.txt`,
  `logs/census-bootstrap-diff.txt`). No owned file was edited before the bootstrap ended.

## 2. The proofs (who wrote what: all by the lead)

The owned files are:

- `GSW/Bootstrap.lean`: 349 lines at the base, 518 at the head (+189, −20; max width 99).
- `GSW/Leveled.lean`: 291 lines at the base, 384 at the head (+102, −9; max width 99).

That makes 291 added lines in all, including the public helper (64 lines with its docstring) and the private helper
(21 lines). This is below the brief's estimate of 460–740 fill lines plus 40–80 for the helper: the must-reuse list
covered every step, and `runWith_rel` carries both inductions. Both files stay far from 1000 lines.

**Changed outside the proof bodies, as COMMON §4 and the brief permit:**

- In Bootstrap, the inserted `encrypts_bootGate` with its `## Main results` entry (two lines, directly after G9's).
- The two module-docstring admission sentences:
  - `The targets G9, G10, G12, G13 and G18 are admitted; G11 is proved.` → `The targets G9, G10, G12, G13 and G18 are
    proved, as is G11.`
  - `L2 and L3 are admitted; L1 is proved.` → `L2 and L3 are proved, as is L1.`
- Three refreshed sketches (G10, G13, L2), each changed only to describe the delivered proof. The old and new texts
  are in §2.1.

**Per target: route, helpers and readers.**

- **G9 `encrypts_bootNAND`.** `bootNAND_eq`, then G3 (`encrypts_homEvalFormula`) on `nandFormula P C₁ C₂` with the
  inputs `keyBits P s` and `evk` (instance `Parameters.neZero_columns`, fan-in from `maxFanin_nandFormula_le`). The
  message is read by `nandFormula_eval` (G7). The noise goes through `Encrypts.mono` with `bootNoise_eq`,
  `Nat.mul_le_mul_right` and `Nat.pow_le_pow_right` on `depth_nandFormula_le` (G8). The proof follows its sketch.
- **`encrypts_bootGate`** (public helper, as proposed). Statement: for a NAND gate `g` (`g.IsNAND`), with `evk`
  encrypting `keyBits P s` under `t'` with noise `βk`, and argument ciphertexts that decrypt under `s` to the argument
  values, `Encrypts P t' (g.eval vals).toNat (bootNoise P βk) (bootGate P evk g cts)`. Its docstring has the formula,
  "Glue.", and a **Proof sketch.** The proof:
  - `g.args.length ≤ 2` comes from `DAGGate.isNAND_iff`, and `DAGGate.eval_of_isNAND` (N1) rewrites the value.
  - The padded `G` decrypts to `true` by `decrypt_of_encrypts` on `encrypts_gadget`. The noise is `0`, so the
    separation condition `2·(ℓ·0) < ⌊q/2⌋` follows from `q ≥ 2` (`modulus_ge_two`, `omega`).
  - `rcases` on `g.args` gives three cases, each read by its case reader: `bootGate_of_args_eq_nil`,
    `bootGate_of_args_eq_singleton` and `bootGate_of_args_eq_cons_cons`. For the last, the empty tail comes from the
    length bound (`List.eq_nil_of_length_eq_zero`).
  - In each case G9 applies, after rewriting the decryptions by `hG` or `hargs`, and `simpa` matches `!(d₁ && d₂)` with
    `!(g.args.all …)`.
- **G10 `decrypt_fheEval`.** `runWith_rel` (H19) on `DAGGate.eval` from `List.ofFn x` and `bootGate P evk` from
  `List.ofFn cts`. The relation is "`Encrypts P t b.toNat (if v < k then βin else bootNoise P βk) C`", and `hsep`
  discharges its decryption condition for both branches.
  - Inputs: `List.getD_eq_getElem`, `List.getElem_ofFn` and `hin`.
  - Acyclicity: `Cc.args_lt`.
  - Gate step: `encrypts_bootGate` with `t' = t`, for the gate's NAND property (`DAGCircuit.isNANDForm_iff`) and argument
    decryptions by `decrypt_of_encrypts`.
  - Output: `Cc.output_lt`, then `fheEval_eq`, `DAGCircuit.eval_eq`, `values_eq` and `decrypt_of_encrypts`.

  This is the pattern of phase 5's `eval_encrypts` (`GSW/Eval.lean:250`), with a different relation and gate step (§5).
- **G18 `decrypt_fheEvalCircuit`.** `fheEvalCircuit_eq`, then `← DAGCircuit.toNANDForm_eval` (N3), then G10 on
  `Cc.toNANDForm hC` with `DAGCircuit.toNANDForm_isNANDForm` (N4). The proof follows its sketch.
- **G12 `decrypt_keygen_fheEvalCircuit`.** `hs : LWE.sample P.lwe χ rg = (rg.1, noisyValues rg.1 rg.2.1 (χ.sample ∘
  rg.2.2))` comes from `Prod.ext` of `LWE.sample_fst`/`_snd`. The errors are bounded by `LWE.Noise.bounded_iff`.
  - The evaluation key: `Regev.keygen_fst`, `Regev.keygen_snd` and `hs`, then **G11 `encrypts_evalKey`** (must-reuse).
  - The inputs: `encrypts_keygen_encrypt`.
  - `m·B ≤ bootNoise P (m·B)` follows from `bootNoise_eq`, `N ≥ 1` (`NeZero` from `Parameters.neZero_columns`) and three
    `Nat.le_mul_of_pos_left`, so `hsep` gives the input condition.
  - Then G18. The proof follows its sketch.
- **G13 `bootNoise_le`.** `bootNoise_eq`. `N ≥ 1` holds by the instance, so the sketch's "`N = 0`" case is not needed.
  - `decDepth_le` (G8) and `Nat.pow_le_pow_right` give `4^(decDepth P + 1) ≤ 4^(9a + 2b + 22)`.
  - That equals `4^22·(4^a)^9·(4^b)^2` by `← pow_mul`, `← pow_add` and `omega` on the exponent. `ring` cannot match
    `4^(9a)` with `262144^a`, so this step is written out.
  - Then `≤ 4^22·(4N²)^9·(4X²)^2` by the private helper and `Nat.pow_le_pow_left`, which `ring` turns into
    `4^33·N^18·X^4`.
  - Finally `Nat.mul_le_mul_right` and `ring` give `4^33·N^19·X^4·(2β)`. The constants c₀ = 33, c₁ = 9, c₂ = 2 are as
    frozen.

  **Private helper `four_pow_clog_le`.** Docstring: "For `y ≥ 1`, `4 ^ ⌈log₂ y⌉ ≤ 4 * y ^ 2`, because
  `2 ^ ⌈log₂ y⌉ ≤ 2 * y` (`Nat.pow_pred_clog_lt_self` for `y ≥ 2`, `Nat.clog_one_right` for `y = 1`). Glue for G13."
  Its proof uses `Nat.clog_pos` and `pow_succ` with `omega`, then `pow_mul` and `ring`. The brief asked me to search
  Mathlib for this bound first: there is none (§5).
- **L2 `encrypts_leveledEval`.** `runWith_rel` on `DAGGate.eval` and the leveled gate function. The relation is the
  dependent "`∀ hv : Cc.depthAt v < L + 1, Encrypts P (secretVector P (ss ⟨depthAt v, hv⟩)) b.toNat
  (max βin (bootNoise P βk)) C`".
  - Inputs: `depthAt_input` gives level `0` (`Fin.ext`), then `hin` and `Encrypts.mono` with `le_max_left`.
  - Gate `i`: the data length comes from `runWith_rel`'s hypothesis. The level is `δ = depthAt (2k+i) ≥ 1`
    (`Cc.depthAt_gate`, `DAGGate.depth_eq`), so `levelGate_of_lt` applies with `δ − 1 < L`.
  - The level key `⟨δ−1, _⟩` has successor `⟨δ, _⟩` (`Fin.ext`, `Fin.val_succ`), which turns `hk` into the key
    hypothesis under `t_δ`.
  - Gate step: `encrypts_bootGate` with `s = ss (⟨δ−1,_⟩.castSucc)`, then `Encrypts.mono` with `le_max_right`.
  - Arguments: `DAGCircuit.isLayered_iff` puts each at level `δ − 1`, the relation's cast is matched by `Fin.ext` and
    `Fin.coe_castSucc`, and `decrypt_of_encrypts` applies with the `max` condition (`max_cases`).
  - Output: `Cc.output_lt`, the level `⟨Cc.depth, _⟩ = ⟨depthAt output, _⟩` (`Fin.ext` of `Cc.depth_eq`),
    `leveledEval_eq`, `DAGCircuit.eval_eq` and `values_eq`.
- **L3 `decrypt_keygen_leveledEvalCircuit`.** `leveledEvalCircuit_eq`.
  - Literal ciphertexts by `induction j using Fin.addCases`. The left half uses `literalCts_castAdd`,
    `litInput_castAdd` and `encrypts_keygen_encrypt`. The right half uses `literalCts_natAdd`, `litInput_natAdd`,
    `homNot_eq`, `homAnd_singleton`, and `Encrypts.sub` of `encrypts_gadget` and the input, with the message
    `(!b).toNat = 1 − b.toNat` and noise `0 + m·B ≤ m·B` (`Encrypts.mono`).
  - Then L2 on `(Cc.toNANDForm hC).layerNAND`:
    - NAND form: `layerNAND_isNANDForm` with `toNANDForm_isNANDForm`.
    - Layered: `layerNAND_isLayered`.
    - Depth: `layerNAND_depth` with `hdepth`.
    - Level keys: L1 `encrypts_levelKey`, with `βk = βin = m·B`.
  - The value: `layerNAND_eval` and `toNANDForm_eval`. The output level: `Fin.ext` of `layerNAND_depth`.
  - Finally `decrypt_of_encrypts`, with `hin` or `hsep` by `max_cases`. The proof follows its sketch.

**Readers used.** The census is `seals/reader-census.txt`: every own or foreign definition the proofs read, with its
reader and `path:line`. MISSING: none. No definition is unfolded: the case readers `bootGate_of_args_eq_*` and
`levelGate_of_lt` are used, and `runWith`, `DAGCircuit.eval`, `depthAt`, `toNANDForm`, `layerNAND`, `litInput`,
`Encrypts`, `decrypt` and `Regev.keygen` are read only through their lemmas. C6 confirms this with the seals and the scan.

**Imports added:** none.

### 2.1 Refreshed sketches (old and new text)

G9, G18, G12 and L3 keep their sketches unchanged: each already describes the delivered proof. The three below changed:

- **G10:** the gate step is now the public helper.
- **G13:** `N ≥ 1` replaces the case split, `2^⌈log₂ y⌉ ≤ 2y` replaces `<` (the helper proves `≤`), and the lemmas
  used are named.
- **L2:** the gate step is the public helper, and the data length comes from `runWith_rel` itself.

#### `decrypt_fheEval`

Old (base):

```text
**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn x` and `bootGate P evk` from `List.ofFn cts`, with the vertex relation "the
ciphertext encrypts the vertex's value under `t` with noise at most `βin` (an input) or
`bootNoise P βk` (a gate)", as `eval_encrypts` does for phase 5. Inputs: `hin`. A gate `g`
(a NAND gate by `isNANDForm_iff`, `DAGGate.isNAND_iff`): its arguments are earlier vertices
(`Cc.args_lt`), so they decrypt to their values by `decrypt_of_encrypts` with `hβin` or
`hboot`; the padded `G` decrypts to `true` (`encrypts_gadget`, noise `0`, `q ≥ 2`). By the
three case readers `bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons` and G9
(`encrypts_bootNAND`, `t' = t`), the gate's ciphertext encrypts `!(d₁ && d₂)` with noise
`bootNoise P βk`, which is the gate's value by `DAGGate.eval_of_isNAND` (N1): `NAND() = false
= NAND(1, 1)` and `NAND(a) = ¬a = NAND(a, a)`. The output vertex is in range (`Cc.output_lt`);
`decrypt_of_encrypts` with `hβin` or `hboot` and `DAGCircuit.eval_eq`, `values_eq` finish,
through `fheEval_eq`.
```

New (head):

```text
**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn x` and `bootGate P evk` from `List.ofFn cts`, with the vertex relation "the
ciphertext encrypts the vertex's value under `t` with noise at most `βin` (an input) or
`bootNoise P βk` (a gate)", as `eval_encrypts` does for phase 5. Inputs: `hin`. A gate `g`
(a NAND gate by `isNANDForm_iff`, `DAGGate.isNAND_iff`): its arguments are earlier vertices
(`Cc.args_lt`), so they decrypt to their values by `decrypt_of_encrypts` with `hβin` or
`hboot`. The gate step is `encrypts_bootGate` (`t' = t`): the padded `G` decrypts to `true`
(`encrypts_gadget`, noise `0`, `q ≥ 2`), and by the three case readers
`bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons` and G9 (`encrypts_bootNAND`), the gate's
ciphertext encrypts `!(d₁ && d₂)` with noise `bootNoise P βk`, which is the gate's value by
`DAGGate.eval_of_isNAND` (N1): `NAND() = false = NAND(1, 1)` and `NAND(a) = ¬a = NAND(a, a)`.
The output vertex is in range (`Cc.output_lt`); `decrypt_of_encrypts` with `hβin` or `hboot` and
`DAGCircuit.eval_eq`, `values_eq` finish, through `fheEval_eq`.
```

#### `bootNoise_le`

Old (base):

```text
**Proof sketch.** `bootNoise_eq`. If `N = 0` both sides are `0`. Otherwise `decDepth_le` (G8)
gives `decDepth P + 1 ≤ 9a + 2b + 22` with `a = ⌈log₂ N⌉` and `b = ⌈log₂ X⌉`,
`X = ℓ + ⌈log₂ N⌉ + 3 ≥ 1`. For `y ≥ 1`, `2^⌈log₂ y⌉ < 2y` (`Nat.pow_pred_clog_lt_self` for
`y ≥ 2`; `Nat.clog_one_right` for `y = 1`), so `4^⌈log₂ y⌉ ≤ 4y²`. Hence
`4^(decDepth P + 1) ≤ 4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4` (`Nat.pow_le_pow_right`,
`Nat.pow_le_pow_left`, `pow_mul`), and multiplying by `2·(N·β)` gives the bound
(`Nat.mul_le_mul_right`, `ring_nf`).
```

New (head):

```text
**Proof sketch.** `bootNoise_eq`. Here `N ≥ 1` (`Parameters.neZero_columns`), and `decDepth_le`
(G8) gives `decDepth P + 1 ≤ 9a + 2b + 22` with `a = ⌈log₂ N⌉` and `b = ⌈log₂ X⌉`,
`X = ℓ + ⌈log₂ N⌉ + 3 ≥ 1`. For `y ≥ 1`, `2^⌈log₂ y⌉ ≤ 2y` (`Nat.pow_pred_clog_lt_self` for
`y ≥ 2`; `Nat.clog_one_right` for `y = 1`), so `4^⌈log₂ y⌉ ≤ 4y²` (private
`four_pow_clog_le`). Hence `4^(decDepth P + 1) ≤ 4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4`
(`Nat.pow_le_pow_right`, `pow_mul`, `pow_add`, `Nat.pow_le_pow_left`, `ring`), and multiplying
by `2·(N·β)` gives the bound (`Nat.mul_le_mul_right`, `ring`).
```

#### `encrypts_leveledEval`

Old (base):

```text
**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn y` and to the leveled gate function from `List.ofFn cts`, with the vertex relation:
"if `Cc.depthAt v ≤ L`, the ciphertext encrypts the value under `s_{depthAt v}` with noise at most
`max βin (bootNoise P βk)`". Inputs have level `0` (`depthAt_input`): `hin`. A gate at vertex
`v = 2k + i` (`runWith` hands it the data of length `v`, `length_runWith`) has level
`δ = Cc.depthAt v ≥ 1` (`depthAt_gate`, `DAGGate.depth_eq`); if `δ ≤ L`, `levelGate_of_lt`
selects the level key `δ − 1`. The circuit is layered (`isLayered_iff`), so every argument is
at level `δ − 1` and, by the relation and `decrypt_of_encrypts` (with `hβin` or `hboot`),
decrypts under `s_{δ−1}` to its value; the padded `G` decrypts to `true` (`encrypts_gadget`).
The three case readers of `bootGate` and G9 (`encrypts_bootNAND` with `s = s_{δ−1}`,
`t' = t_δ`, `hk`) give an encryption under `s_δ` of the NAND of the argument values with noise
`bootNoise P βk`, which is the gate's value (`isNANDForm_iff`, `DAGGate.eval_of_isNAND`, N1).
Gates above level `L` are unconstrained and are never read by a vertex at level `≤ L`. At the
output (`Cc.output_lt`, level `Cc.depth = depthAt Cc.output` by `depth_eq`, at most `L`), read
`DAGCircuit.eval_eq`, `values_eq` and `leveledEval_eq`.
```

New (head):

```text
**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn y` and to the leveled gate function from `List.ofFn cts`, with the vertex relation:
"if `Cc.depthAt v ≤ L`, the ciphertext encrypts the value under `s_{depthAt v}` with noise at most
`max βin (bootNoise P βk)`". Inputs have level `0` (`depthAt_input`): `hin` (`Encrypts.mono`). A
gate at vertex `v = 2k + i` (`runWith_rel` hands it the data of length `v`) has level
`δ = Cc.depthAt v ≥ 1` (`depthAt_gate`, `DAGGate.depth_eq`); if `δ ≤ L`, `levelGate_of_lt`
selects the level key `δ − 1`. The circuit is layered (`isLayered_iff`), so every argument is
at level `δ − 1` and, by the relation and `decrypt_of_encrypts` (with `hβin` or `hboot`),
decrypts under `s_{δ−1}` to its value. The gate step is `encrypts_bootGate` (`s = s_{δ−1}`,
`t' = t_δ`, `hk` at `δ − 1`, whose successor is `δ`): the padded `G` decrypts to `true`
(`encrypts_gadget`), and the three case readers of `bootGate` and G9 (`encrypts_bootNAND`) give
an encryption under `s_δ` of the NAND of the argument values with noise `bootNoise P βk`, which
is the gate's value (`isNANDForm_iff`, `DAGGate.eval_of_isNAND`, N1).
Gates above level `L` are unconstrained and are never read by a vertex at level `≤ L`. At the
output (`Cc.output_lt`, level `Cc.depth = depthAt Cc.output` by `depth_eq`, at most `L`), read
`DAGCircuit.eval_eq`, `values_eq` and `leveledEval_eq`.
```

## 3. Statement changes

None. `encrypts_bootGate` is stated exactly as the brief proposes; the brief allowed a refinement, but none was
needed. No target statement changed (C3, C4).

## 4. Checks C1–C13 and the unit checks

- **C1 Bootstrap and sweep.**
  - The bootstrap is as described in §1.
  - The head sweep rechecked the 9 `UNIT-DOWN` rows of `closures.txt` for this unit (`logs/unit-down.txt`: Bootstrap,
    Circular, Leveled, LeveledSecurity, PolyRatio, Asymptotic, GSW, Homomorphic, AdvancedEncryption) in dependency
    order with `pool_build.py` (`logs/head-sweep.log`): every rc 0, 0 errors.
  - `build/summary.txt` has one row per module of `order.txt`. It uses the head sweep's log for the 9 and the
    bootstrap's for the other 215, whose sources are unchanged. Each row gives rc, errors in both forms, `sorry`
    warnings, and the SHA-256 of the source the check read, bound to `git show HEAD:<path>`. Result: **224/224 rc 0, 0
    errors, bound**.
  - The root `TCSlib` was not built.
- **C2 Admissions** (`admissions/`).
  - The head census equals `base-sorries.txt` minus the 7 targets: **35 declarations in 14 modules**
    (`census-head.txt` against `expected-head.txt`: IDENTICAL).
  - Neither owned file contains a `sorry`, `admit`, `native_decide`, `axiom` or `opaque` token
    (`admissions-check.txt`).
- **C3 Statements** (`statements/`).
  - I ran the records' `decls2.py` (SHA-256 `fa81981a…`, as in §1) on each owned file:
    - Bootstrap: **ADDED exactly `encrypts_bootGate`, 0 CHANGED, 0 REMOVED** (`decls2-Bootstrap.txt`).
    - Leveled: **0/0/0** (`decls2-Leveled.txt`, empty).
    - Both `.err` files are empty.
    - The summaries show the parser saw 28 → 29 and 18 → 18 public declarations, with every base statement identical.
  - The `StmtDump` probes print every public declaration with its full name and type (`pp.fullNames`):
    - They run at the base, on verbatim base copies `base/BootstrapBase.lean` and `base/LeveledBase.lean`. The Leveled
      copy imports the real `Bootstrap`, whose definitions are unchanged.
    - They run at the head on the modules themselves.
  - In `stmtdump-diff.txt`, the Bootstrap diff is exactly the added `encrypts_bootGate` block, and Leveled is IDENTICAL.
    §2 maps each target to its proof.
- **C4 Frozen check** (`frozen/`). I wrote `tools/lead/frozen_check_u14u16.py` for this unit, adapted from this host's
  U13 checker.
  - **What it checks.** For each target, the statement prose and the header must be byte-identical. Every other base
    declaration must be byte-identical. A declaration that is new at the head may be:
    - `private` (`four_pow_clog_le`); or
    - the ruled `encrypts_bootGate`, placed immediately after G9 and immediately before G10.

    Non-declaration text may differ in only these ways:
    - the admission sentence;
    - in Bootstrap, the `## Main results` insertion directly after the G9 entry;
    - blank separator lines, at most one per added declaration.
  - **Head:** violations **0** in both files (`frozen-head-Bootstrap.txt`, `frozen-head-Leveled.txt`).
  - **Controls.** Each must report the stated count:

    | Control | Bootstrap | Leveled |
    |---|---|---|
    | 0: base vs itself | 0 | 0 |
    | 1: one-character header change | 1 (HEADER) | 1 (HEADER) |
    | 2: sketch edit spilling into the statement prose | 1 (PROSE) | 1 (PROSE) |
    | 3: definition body | 1 (BODY, `bootNoise`) | 1 (BODY, `literalCts`) |
    | 4: reader | 1 (BODY, `bootNAND_eq`) | 1 (BODY, `levelKey_eq`) |
    | 5: unpermitted import | 1 (TEXT) | 1 (TEXT) |
    | 6: deleted target | 1 (REMOVED) | 1 (REMOVED) |
    | 7: unlisted public declaration | 1 (ADDED) | 1 (ADDED) |
    | 8: `encrypts_bootGate` moved after G10 | 1 (ORDER) | — |
    | 9: another `## Main results` entry edited | 1 (TEXT) | — |

    All 18 control files report as stated.
  - `git diff --stat bff0567b..HEAD` lists only the two owned files.
- **C5 Axioms** (`axioms/`).
  - `#print axioms` of the seven targets and the helper: `[propext, sorryAx, Classical.choice, Quot.sound]` each.
  - I took a census of every stored constant of the two modules: 65 constants, namely the 47 public declarations, the
    private helper, the base's auxiliary `bootGate.match_1`, and 16 auxiliary `_proof_` constants of the new proofs.
    - 0 have an axiom outside the standard three and `sorryAx`.
    - 8 have a `sorryAx` trace: the 7 targets and the helper.
    - **0 trace names are DISALLOWED.** The traces are `[depth_nandFormula_le, nandFormula_eval,
      maxFanin_nandFormula_le, encrypts_homEvalFormula]` for G9, the helper, G10, G18, G12, L2 and L3, and
      `[decDepth_le]` for G13.
    - No trace names a Bootstrap or Leveled declaration.
  - **Base control** (`axioms-base-control.log`): the same census over the two base copies finds 5 + 2 constants
    reaching `sorryAx`. Each is traced to itself and flagged DISALLOWED, so the check is live.
  - On the merge with the records tip (§0), the traces are empty (`logs/merge-check.log`).
- **C6 Rule 10** (`seals/`).
  - **Seals.** Each run seals the whole import closure: every TCSlib definition of the closure is made irreducible and
    removed from instance unfolding. Reducible abbreviations are excluded, as notation.
    - Each run compiles with `lean -DmaxErrors=0` on `lean_check_tree.sh`'s `LEAN_PATH`.
    - There are four variants, A/B × strict/coe, with coe-A canonical.
    - The runs cover both owned files at the head and both base copies (recorded under the owned paths).

    Result: **16/16 runs status 0, 0 errors; no failing declaration at the head** (`seals-summary.txt`, `runs/*.jsonl`
    and raw `runs/*.out`, sealed copies in `seals/sources/`).
    - Sealed: 298–330 definitions.
    - `PolyExpr` is not in this closure (`excluded=0`), so A and B coincide.
    - The one projection coercion is `FinDist.instCoeFunForallReal` (`coe-excluded=1`).
  - **Paired controls** (`controls/`; unsealed `controls-plain.log`: all 8 pass). Each negative control is a foreign
    `rfl` read that passes unsealed and **fails exactly once (1 error) in each of the 4 sealed variants**:
    - `CtlUnfoldBoot`: `bootNoise`, owner Bootstrap.
    - `CtlUnfoldBootGate`: `bootGate` at a fan-in-0 gate. This is **the pair of the new public helper
      `encrypts_bootGate`**: the case split it must read through the case reader.
    - `CtlUnfoldLev`: `levelKey`, owner Leveled.
    - `CtlUnfoldHost`: `DAGCircuit.depth`, owner DAGCircuit/H19.
    - `CtlUnfoldLayer`: `litInput`, owner NANDLayering.
    - `CtlUnfoldNoise`: `Encrypts` by `Iff.rfl`, owner Noise.
    - `CtlUnfoldRegev`: `Regev.keygen`.

    That is 28/28 negative runs status 1 with 1 error. `CtlReader` is the positive half: the same seven facts through
    `bootNoise_eq`, `bootGate_of_args_eq_nil`, `levelKey_eq`, `depth_eq`, `litInput_eq`, `encrypts_iff` and
    `Regev.keygen_snd`, plus an application of `encrypts_bootGate`. It **passes in all 4 sealed variants**.
    No new public definition was added, so no further pair is needed. Request sets: this method collects none (it seals
    the whole closure at the base's sources), so none can be stale (G6B-F11).
  - **Explicit-unfold scan** (`scan/`). At the head, 72 identifiers are given to `rw`/`simp`/… in the two files: 53
    theorems, 17 local or dot-notation names (hypotheses, and `Cc.eval_eq`-style reader calls), and 2 own definitions.
    The 2 own definitions are `bootGate` and `levelGate`, in the frozen case readers' `unfold`, and they are present at
    the base too. **0 foreign definitions.** `scan-compare.log` says "NEW foreign explicit unfolds: 0".
  - **Reader census:** §2.
- **C7 Lint** (`lint/`).
  - `style_lint.py` on the two owned files gives 0 findings at the base and at the head.
  - `campaign_style_lint.py TCSlib/Cryptography --check8b` gives **92 FAIL / 103 WARN over 540 files** (rc 1) at both
    base and head, matching the maintainer's run. The FAIL/WARN line sets are identical (`campaign-lint-diff.txt`). The
    base run used a `git archive` of the base's `scripts/` and `TCSlib/Cryptography/`.
- **C8 Sizes** (`hygiene/sizes-hygiene.txt`):
  - Bootstrap: 349 → 518 lines.
  - Leveled: 291 → 384 lines.
  - Max width is 99 in both, and no line exceeds 100.
  - `Bootstrap.lean` stays under the projected 791 lines.
- **C9 Docstrings and sketches** (`hygiene/sizes-hygiene.txt`): **0 findings.**
  - The helper `encrypts_bootGate` has a formula, "Glue." and a sketch.
  - The private `four_pow_clog_le` has a formula and "Glue for G13.".
  - Every proof of 20 lines or more has a sketch: `encrypts_bootGate` 31, G10 35, G12 26, G13 24, L2 60 and L3 34 lines.
  - The long proofs carry step comments at the major `have`s.
- **C10 Clashes** (`clash/clash.txt`).
  - The new full names are `encrypts_bootGate`, the private `four_pow_clog_le`, and 16 auxiliary `_proof_` constants.
  - None of them occurs at the base, on `iO/phase-a-base` `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, on
    `cleanup/stage2-s2a` `9f7f409c2e09749428db75b9ddd324f92695e4af` (fetched at delivery), or in Mathlib, Batteries or
    core.
  - The only new public short name, `encrypts_bootGate`, occurs at the head only in the two owned files, so no
    resolution in a `UNIT-DOWN` module can change.
- **C11 Reuse and overlap:** §5.
- **C12 Probes.** The brief asks for none, and says not to plan numeric probes of G10 or L2 (G6B-F06). None was run
  beyond the C3/C5 probes.
- **C13 Reproduction** (`logs/repro.log`).
  - `git am` of `patches/` at the base in a scratch clone (`/tmp/u1416-repro`, deleted afterwards), with the committer
    data of `COMMITS.tsv`: **every hash reproduced** (both commits).
  - `src/` equals the head's files byte for byte.
  - Both commits are unsigned (the `signing` column).
- **Unit checks.**
  - C2 count: 35 declarations in 14 modules ✓.
  - C3: Bootstrap ADDED exactly `encrypts_bootGate`, 0/0; Leveled 0/0/0 ✓.
  - C4 allows exactly that insertion and its Main-results line ✓.
  - C5 traces only through the allowed U12/U13 names ✓.
  - The final has no `sorry` ✓.

## 5. Overlap and reuse (C11)

**Searches** (`logs/dup-searches.log`, with commands and hit counts over the base, `iO/phase-a-base`,
`cleanup/stage2-s2a` and Mathlib/Batteries/core):

- **The 7 target names and the 2 helper names.**
  - Targets: 2–4 lines each at the base, all in their own files and docstrings. 0 on both other heads.
  - `encrypts_bootGate` and `four_pow_clog_le`: 0 everywhere.
- **Gate-step shapes.**
  - `theorem …Gate…encrypt|encrypts_…Gate|homGate_encrypts`: 4 lines, all `homGate_encrypts`, `GSW/Eval.lean:181`.
  - `IsNAND.*Encrypts`: 0.
  - `decrypt P s (cts.getD`: 0.
- **`runWith_rel`: 7 lines.** Its definition, `eval_encrypts`'s use, and the two frozen sketches.
- **`eval_encrypts` (5 lines) and `decrypt_keygen_eval` (2 lines).**
- **`clog` bounds.**
  - `^ Nat.clog 2 …`: 15 lines.
  - `pow_pred_clog_lt_self`: 3 lines.
  - `theorem …clog…` in Mathlib: 45 lines.
  - `b ^ clog b x < b * …`-shaped lemmas in Mathlib: 0.
- **Literal and layering lemmas** (7 + 15 lines) and `homNot_eq|homAnd_singleton` (5 lines).
- **`LWE.sample_fst P.lwe χ`: 1 line**, in `encrypts_keygen_encrypt`'s proof.

**Must-reuse items of dup-sweep.md §U14-U16**, with where they are used:

| Item | Used in |
|---|---|
| G3 `encrypts_homEvalFormula` (U12) | G9 |
| G7 `nandFormula_eval` (U13) | G9 |
| G8 `depth_nandFormula_le`, `maxFanin_nandFormula_le` (U13) | G9 |
| G8 `decDepth_le` (U13) | G13 |
| within the unit: G9 → helper → G10 → G18 → G12; G9/helper → L2 → L3 | helper uses G9; G10 and L2 use the helper; G18 uses G10; G12 uses G18; L3 uses L2 |
| `runWith_rel` (`DAGCircuit.lean:637`) | G10, L2 |
| `length_runWith` (`:176`) | not called directly: `runWith_rel`'s gate hypothesis already supplies the data lengths (it uses `length_runWith` internally); the L2 sketch was refreshed to say so |
| `values_eq`, `DAGCircuit.eval_eq` | G10, L2 |
| `depth_eq` | L2 (output level) |
| `depthAt_input` | L2 (inputs) |
| `depthAt_gate`, `DAGGate.depth_eq` | L2 (`δ ≥ 1`) |
| `DAGGate.getD_lt_depth` (`:592`) | not needed: in a layered circuit `isLayered_iff` gives each argument's level exactly (`δ − 1`), which is stronger than "shallower" |
| fields `args_lt`, `output_lt` | G10, L2 |
| `DAGGate.isNAND_iff` | helper |
| `DAGCircuit.isNANDForm_iff` | G10, L2 |
| `DAGGate.eval_of_isNAND` | helper |
| `toNANDForm_eval` | G18, L3 |
| `toNANDForm_isNANDForm` | G18, L3 |
| `DAGCircuit.isLayered_iff` | L2 |
| `litInput_castAdd`, `litInput_natAdd` | L3 |
| `layerNAND_eval`, `layerNAND_isLayered`, `layerNAND_isNANDForm`, `layerNAND_depth` | L3 |
| `decrypt_of_encrypts` | helper, G10, L2, L3 |
| `encrypts_keygen_encrypt` | G12, L3 |
| `encrypts_encrypt` | through G11 in G12 (G11's proof cites it) |
| `encrypts_gadget` | helper, L3 |
| `Encrypts.sub` | L3 |
| `Encrypts.mono` | G9, L2, L3 |
| `homNot_eq`, `homAnd_singleton` | L3 |
| `Regev.keygen_fst`/`_snd`, `LWE.sample_fst`/`_snd`, `LWE.Noise.bounded_iff` | G12 |
| own reader `bootNAND_eq` | G9 |
| own readers `bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons` | helper |
| own reader `bootNoise_eq` | G9, G12, G13 |
| own readers `fheEval_eq`, `fheEvalCircuit_eq` | G10, G18 |
| `evalKey_eq` | through G11 |
| `encrypts_evalKey` (G11) | G12 |
| `levelKey_eq` | through L1 |
| `literalCts_castAdd`/`_natAdd` | L3 |
| `levelGate_of_lt` | L2 |
| `levelGate_of_le` | not needed: gates above `L` are excluded by the relation's hypothesis, never computed |
| `leveledEval_eq`, `leveledEvalCircuit_eq` | L2, L3 |
| `encrypts_levelKey` (L1) | L3 |
| instance `Parameters.neZero_columns` | G9 (instance), G12, G13 |
| G13: `Nat.pow_pred_clog_lt_self`, `Nat.clog_one_right`, `Nat.pow_le_pow_right`, `Nat.pow_le_pow_left`, `pow_mul` | G13 and `four_pow_clog_le` |

**Near relatives and specializations (disclosed):**

- **Phase 5's `eval_encrypts`** (`GSW/Eval.lean:250`) is the same `runWith_rel` pattern, as the brief says. G10 and L2
  share its call shape and its input-vertex rewriting. That rewriting is the four rewrites `List.getD_eq_getElem` ×2 and
  `List.getElem_ofFn` ×2 under `List.length_ofFn`, which are identical in shape; these few lines are the only text in
  common.
  - G10 differs in its relation (input or gate noise by `if v < k`, no depth) and its gate step (`encrypts_bootGate`
    plus decryption of the arguments).
  - L2 differs in its dependent level relation, its level arithmetic and its keys.
  - No proof text is copied beyond that call shape.
- **`homGate_encrypts`** (`GSW/Eval.lean:181`) is the phase-5 analogue of `encrypts_bootGate`: a per-gate step over
  `vals`/`cts` for `homGate`. It cannot be reused. Its hypothesis is an encryption of each argument with noise `β`, and
  its noise grows (`(N+1)·β`). The helper instead takes decryptions and returns the fixed `bootNoise P βk` under a
  possibly different key `t'`.
- **`decrypt_keygen_eval`** (`GSW/Eval.lean:300`) is G12's leveled phase-5 analogue: `encrypts_keygen_encrypt` for
  the inputs, then evaluation, then `decrypt_of_encrypts`. G12 adds the evaluation key (G11) and the `m·B ≤ bootNoise`
  step.
- **G12's local `hs`** (`LWE.sample … = (rg.1, noisyValues …)` by `Prod.ext` of `LWE.sample_fst`/`_snd`) is the same
  two-line step as inside `encrypts_keygen_encrypt`'s proof (`GSW/Scheme.lean:214–216`). No published lemma states it.
  It is needed because the must-reuse G11 is stated for `(A, noisyValues A s e)`. It is a local `have` of two cited
  readers, not a declaration, so there is no private copy. See question U14-U16-W1.
- **`four_pow_clog_le`.** Mathlib has no `b ^ clog b x ≤ b * x` lemma (0 hits). TCSlib has `two_pow_clog_le`
  (`2^⌈log₂ 2n⌉ ≤ 4n + 1`) and `two_pow_lovaszBits_lt` in `ClassP/BinaryArith/PrimeFind.lean:119/:74`. Both are about
  `clog 2 (2n)`, a different shape, and neither is in this unit's import closure (224 modules). The private helper
  states `4^⌈log₂ y⌉ ≤ 4y²`, which the brief named. Its proof follows the same `pow_pred_clog_lt_self` route, written
  independently.
- There is no exact restatement, no inline re-derivation of a published lemma, and no private or cross-file copy.

## 6. Promotion requests

None. The only public helper is the ruled one. `four_pow_clog_le` is a one-use `clog` bound. If a later unit needs it,
it would belong next to Mathlib's `Nat.clog` lemmas; it is not requested now.

## 7. Scope requests

None. No frozen file was touched, and no reader was missing.

## 8. Checkpoints

- **Checkpoint 1** (this delivery): head `9852429e…`. All seven targets and the helper are proved, and C1–C13 have run
  (a full payload). The brief asked for the helper, G9 and G13, and an outline of L2. L2's outline is its proof (§2).
- **Final:** to follow. If the head does not change, the final will carry the same head and evidence, with the records
  tip re-read.

## 9. Probes and attribution

No citation was added or changed. The only docstring changes are the three refreshed sketch paragraphs, the helpers'
docstrings, the Main-results entry and the admission sentences. Probes, controls and base copies live outside the
library: they are `lean_proof/u1416/…` in the worktree, which git ignores. Their sources are under `evidence/probes/`,
`evidence/controls/` and `evidence/base/`.

## 10. Questions for Seyoon

- **U14-U16-W1 · G12's honest-key rewriting.** G12 must reuse G11 (`encrypts_evalKey`), which is stated for the key
  `(A, noisyValues A s e)`. Rewriting `Regev.keygen` into that form needs `LWE.sample P.lwe χ rg = (rg.1, noisyValues
  …)`, which no lemma states. I wrote it as a local two-line `have` (`Prod.ext` of `LWE.sample_fst` and
  `LWE.sample_snd`), the same two lines as inside phase 5's `encrypts_keygen_encrypt` proof.
  - **A** (recommended): accept it as is. It is the brief's prescribed route, and the two-line `have` cites only
    published readers.
  - **B**: in a later cleanup, publish `LWE.sample_eq` in `LWE/Basic.lean` and use it in both places. That file is
    outside this unit's scope, so this would be a promotion for the cleanup, not for this fill.

## 11. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- **`logs/`:**
  - Inputs and environment: `inputs-check.log`, `preflight.log`, `source-sha256.log`, `order.txt`,
    `mathlib-roots.txt`, `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`,
    `cache-probe.log`, `pool.log`.
  - Builds: `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-diff.txt`, `unit-down.txt`, `head-sweep.log`,
    `base-copy.log`.
  - Other: `dup-searches.log`, `repro.log`, `merge-check.log` (information).
- **Check outputs:**
  - `build/summary.txt`.
  - `admissions/`: `census-head.txt`, `expected-head.txt`, `admissions-check.txt`.
  - `statements/`: `decls2-*.txt`/`.err`, `decls2-summary-*.txt`, `stmtdump-{base,head}-{bootstrap,leveled}.log`,
    `stmtdump-diff.txt`.
  - `frozen/`: `frozen-head-*.txt` and the 18 control outputs.
  - `axioms/`: `axioms-head.log`, `axioms-base-control.log`.
  - `seals/`: `seals-summary.txt`, `runs/` (48 `.jsonl` + `.out`), `sources/` (the sealed copies), `controls-plain.log`,
    `reader-census.txt`.
  - `scan/`: ids, raw logs, tsv, compare, kinds, and the scan modules in `sources/`.
  - `lint/`, `hygiene/`, `clash/`.
- **Sources:**
  - `controls/`: the 8 control files.
  - `base/`: the verbatim base copies.
  - `probes/`: `CacheProbe`, the four `StmtDump*` files and the three `Axioms*` files.
- **`tools/`:** every script used, with relative paths kept.
  - New for this unit: `seal_jobs.sh` (rewritten for the two files and eight controls), `scratch.sh`,
    `dup_searches.sh`, `reader_census.sh`, `lead/frozen_check_u14u16.py`.
  - Adapted from U13's copies to two files: `lead/sizes_hygiene.py`, `manifest.sh` (keeps paths).
  - Unchanged in substance, with paths rewritten to this unit: `check.sh`, `pool_build.py`, `census.py`, `pkgcheck.py`,
    `seal_gen.py`, `seal_run.py`, `rwids.py`, `rwids_run.sh`, `cmp_scans.py`, `width_check.py`, `payload.sh`,
    `repro_check.sh`, `lead/decls2_summary.py`, `lead/summary.py`.
  - `records/decls2.py`: the records' copy, unchanged.
- **`patches/`:** two patches and `COMMITS.tsv`, with the signing column.
- **`src/`:** the two owned files at the head.

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/gsw-6b-u14-u16/` except itself, with no
leading `./`. Its paths equal the delivered files; this was checked before the push.
