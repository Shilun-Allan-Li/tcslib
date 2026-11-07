# E-PAD fill — `Complexity.mem_SPACE_padLang` (`SpaceComplexity/Padding.lean`)

**Status: COMPLETE.** All four checkpoints reached; `Complexity.mem_SPACE_padLang` is proved and
prints `[propext, Classical.choice, Quot.sound]`. The module has no `sorry` and no `admit`, and
no new axiom; no new public declaration (3 public, as at the base). No escalation.

## 1. Base, branch, commits

| item | value |
|---|---|
| campaign branch | `complexity/arora-barak-ch3-4` |
| ancestor check | `git merge-base --is-ancestor 72fcfbef3c1deb331aedc95d4a158a9ed4c56524 HEAD` → 0 |
| base (branched at exactly) | `72fcfbef3c1deb331aedc95d4a158a9ed4c56524` |
| `git rev-parse HEAD:TCSlib/Complexity/SpaceComplexity/Padding.lean` at base | `39a59037fb3b7582ef154cd8819640ac05c1b6ea` (as required) |
| fill branch | `fill/epad` (never rebased, merged or cherry-picked) |
| checkpoint 1 commit | `07b50af5` — route vocabulary and imports |
| checkpoint 2 commit | `53c3d0c2` — the validator (`epad_V_mem`) |
| checkpoint 3 commit | `80072733` — the bank (`epad_Q_mem`) and the run phase (`epad_run`) |
| checkpoint 4 commit (final) | `7d16731e` — `mem_SPACE_padLang` proved |

Delivery: by push of each zip to `exchange/pass-shelat-ch5-8` under
`arora-barak-ch3-4/inbox/fill-epad/` (the user's override of the brief's "zip in the reply";
one commit per zip, `git pull --rebase` before each push, never forced; nothing else touched).

## 2. Environment (addendum v2.6, Parts 1 and 2; Part 3's one-Lean rule)

This session earlier completed a different fill (Pass–shelat unit `rabin`) on the same host and
clone; E-PAD is a separate item with its own branch, bootstrap, checks and zip.

* **Preflight** (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, `memory.limit_in_bytes`
  unlimited, so headroom = `MemAvailable` = 15.41 GiB (floor 4 GiB): PASS; clone filesystem free
  23.73 GiB (floor 12 GiB): PASS.
* **Toolchain**: Lean 4.25.0 (`lean-toolchain` pin), installed under elan from the official
  GitHub release archive (`release.lean-lang.org` is unreachable from this host; disclosed, no
  shim needed: Lean starts normally, so Part 2's shim was **not** used).
* **Cache** for the roots only (`evidence/logs/mathlib-roots.txt`: 64 Mathlib roots of the
  227-module order list `evidence/logs/order.txt` = the TCSlib closure of `Padding`,
  `PreimageHost`, `InputDevice`, `VirtualInput`, `InputCall`, `PolyTimePairing` and the
  `SpaceComplexity` facade). Store logged before the fetch (`cache-store.log`: it existed, 2346
  files, from the earlier fill); `lake exe cache get <roots>`: "Attempting to download 20",
  "Decompressing 1061", exit 0 (`cache-get.log`). Package check PASS (`packages-check.log`);
  no zero-byte oleans (`zero-oleans.log`); cache probe exit 0 (`cache-probe.log`).
* **Bootstrap** of all 227 modules through `scripts/lean_check_tree.sh` into the scratch olean
  tree `/workspace/epad-oleans` (`bootstrap.log`): 01:58:56–02:26:22 UTC, every module exit 0,
  sum of module walls 1641 s, largest module 306 s, peak RSS 4565 MiB.
* **Import probe** (the brief's, at the base): exit 0, every host prints its type, the target's
  only admission is its own `sorry` (`evidence/logs/importprobe-base.out`, identical to the
  pre-ship output apart from the exit line).
* Every Lean run went through `scripts/lean_check_tree.sh` (wrapper `tools/chkE.py`, which logs
  start, end, wall time and peak RSS), one at a time.

## 3. Route and design note (checkpoint 1)

**Chosen route: (A), the preimage route, closed by the catalog's conditional.** Three machines
and one combinator, every host proved at the base:

1. **The validator** `D` decides the padded words
   `epadV C d = {y | ∃ a, y = pairEncode a 1^{C (|a|+1)^d}}`, malformed inputs included, in
   `O(log m) ⊆ O(m + 1)` cells (leaf `epad_V_mem : epadV C d ∈ LOGSPACE`, checkpoint 2).
2. **The run phase** `O`: the oracle-input simulator
   `LogProg.compileFinTM (LogProg.OIS.prog M) (LogProg.OIS.start M) (LogProg.bankTM Ms) (LogProg.bankStart Ms)`
   runs `L`'s decider `M` on the **virtual input** `v = epadVirt C d y`: the first component
   `pairFstD y` of a padded word, and `[]` on every other input. The virtual input is never
   written; its length and bit queries `⟨y, bits i⟩` are answered by a bank of two deciders for
   `epadQ C d false` / `epadQ C d true` (leaf `epad_Q_mem : epadQ C d mode ∈ LOGSPACE`,
   checkpoint 3), whose laws on genuine queries are `epad_query_mem_iff` (proved, this commit).
   Host: `Complexity.LogProg.OIS.compile_decides`.
3. **The constant** `[false]` machine: `Turing.FinTM.computesFunInTime_const_spaceUsed`.
4. **The combinator**: `Turing.FinTM.computesFunInTime_cond_spaceUsed` (`Build/Catalog`, proved):
   on `y`, run `D`; if it accepts, run `O`, else the constant. Its output is
   `if y ∈ epadV then [y.fst ∈ L] else [false] = [y ∈ padLang L pad]`. Its hypotheses
   (`ComputesFunInTime` and space at **every** time) come from
   `Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` (`ConfigCount`).

**Why the conditional, and why `epadVirt y = []` off the padded words.** `compile_decides`
returns `M`'s answer on the virtual input, so invalid inputs must be rejected elsewhere; with the
conditional no word `w₀ ∉ L` is needed and `L = univ` needs no separate case. The conditional's
space hypotheses are uniform over inputs (`∀ x t, … ≤ s |x|`), so the run phase must be
space-safe on **invalid** inputs too: there its virtual input is `[]`, on which `M` uses the
constant `c · S 0` (never `S` of a long first component, which `hST` does not control).

**Why not route (B).** The machine-level hosts that would give a space-bounded validator are
not available: the catalog's length check `computesFunInTime_pairLenCheck_spaceUsed` writes the
unary bank `C (|a| + 1)^e` before comparing, so its space is polynomial in `m` on malformed
inputs (`c ((m+1)^e + m + 1)`); `polyUnaryTM_spaceUsed`, `branchTM_spaceUsed` and
`timedCondTM_spaceUsed` are `sorry` at the base (never cited). The register-machine layer
(`Machines/ARM*`, `Logspace/InputAccess`) has proved run lemmas for every loop the validator
needs and a proved space wrapper (`Complexity.LogProg.arm_decides_poly`), so (A) needs no new
machine semantics: only register programs and their runs.

**The validator and the bank (checkpoints 2–3), as abstract register machines.** Registers hold
naturals in binary; the input is read through the published deciders `inputBitLang`,
`inputLenLang` (`inputBitLang_mem`, `inputLenLang_mem`) by `whole`-mode calls on `⟨y, bits p⟩`.
* *Validator on `y`*: `inputLength_loop` (`|y|`); `alignedPair_loop` (stride 1) parses
  `y = ⟨a, b⟩` or rejects; `|a| + 1` = the pointer halved; a ones-scan of `b` counting `|b|`
  (rejects at a `0`); `P := C`, then `d` times `P := P · (|a| + 1)` by addition loops; accept
  iff `|b| = P`. Register values stay below `C (m + 1)^d + O(m)`, so `arm_decides_poly` gives
  `epadV C d ∈ LOGSPACE`. The pad is never written; malformed inputs are rejected by the parse
  or the scan within the same bound.
* *Bank on `z = ⟨y, w⟩`*: length of `z`; `alignedPair_loop` on `z` (reject unless a pair);
  `canonicalTail_loop` with cap `|y|` (reject a non-canonical or too-wide index: genuine queries
  have `i ≤ |v| ≤ |y|`); `boundedDecode_loop` (`i := bitsVal w`); the validator's block on `y`
  at stride 2 (`y`'s letters are `z`'s doubled first field); then mode `false`: `i < |a|`;
  mode `true`: if `i < |a|`, read `z` at `4i` (`= a_i`), else `0`.

**The space ledger** (proved in the route probe). Let `m = |y|`, `v = epadVirt C d y`
(`|v| ≤ m`), `M` decide `L` in `c · S`, the bank's deciders run in `c₀ · logSpace`,
`c₁ · logSpace`, `k_D = bankK Ms + bankK Ms`.
* `compile_decides`: the run phase uses at most
  `M.k (2 s_M + 1) + (|bits (|v| + 1)| + 2) + k_D (2B + 1)` cells, where `s_M ≤ c · S |v|` is
  `M`'s space on `v` and `B = (c₀ + c₁)(3m + 4) + 1` bounds the bank's radius on every query
  `⟨y, bits i⟩`, `i ≤ |v|` (its length is `2m + 2 + |bits i| ≤ 3m + 3`; `logSpace q ≤ q + 1`).
* Padded `y = ⟨a, 1^{C(|a|+1)^d}⟩`: `m = 2|a| + 2 + C (|a| + 1)^d` (`length_pairEncode`), so
  `S |v| = S |a| ≤ T m` by `hST`. Otherwise `v = []` and `S 0 ≤ S 0 · T m` (`T m ≥ 1`). Both:
  `S |v| ≤ (S 0 + 1) T m`.
* `|bits (|v| + 1)| + 2 ≤ |v| + 4 ≤ 4 T m`; `2B + 1 ≤ (8 (c₀ + c₁) + 3) T m` (as
  `3m + 4 ≤ 4 (m + 1) ≤ 4 T m`, from `hT`).
* Run phase: `≤ K T m`, `K = M.k (2c (S 0 + 1) + 1) + 4 + k_D (8 (c₀ + c₁) + 3)`.
* Validator: `c_V logSpace m ≤ c_V (m + 1) ≤ c_V T m`. Constant machine: `c_f ≤ c_f T m`.
* Conditional: `c_V logSpace m + max (K T m) c_f + c_c ≤ (c_V + K + c_f + c_c) T m`, so
  `padLang L pad ∈ SPACE T` with constant `c_V + K + c_f + c_c`.

**Initialization and the simulated input** (gate 110, note 4): `SPACE` counts visited work cells
(`SpaceComplexity/Basic`). `compile_decides` charges every work tape of the compiled machine:
`M`'s tapes as registers (`M.k (2 s_M + 1)`, origins included), the index register of the
virtual input (`|bits (|v|+1)| + 2`: the simulated input costs only its head position), and the
bank's `k_D` tapes (`2B + 1` each). The conditional's own overhead (capture tape, dispatch) is
its constant `c_c`. The input tape is read-only and uncounted.

**Route probe** (`evidence/probes/EPadRoute.lean`, output `evidence/logs/route-probe-cp1.out`):
a copy of `Padding.lean` in which `mem_SPACE_padLang` is proved from the two leaves; exit 0; the
only `sorry`s are `epad_V_mem` and `epad_Q_mem` (two "declaration uses 'sorry'" warnings, at
those two lines); the target prints `[propext, sorryAx, Classical.choice, Quot.sound]`.

## 4. New declarations and their roles

All private, prefix `epad`/`epad_`/`EPad`. Base: 77 lines, 3 public, 0 private.
Final: **1762 lines, 3 public, 50 private** (no new public declaration; the module's
non-private constants are exactly the base's three, checked by a constant walk). One `local`
tactic macro, `epad_upd` (register-file case split), scoped to its section.

*Vocabulary (checkpoint 1).*

| declaration | kind | role |
|---|---|---|
| `epadValid C d y` | def (Prop) | `y` is a padded word `⟨a, 1^{C(\|a\|+1)^d}⟩` |
| `epadV C d` | def (language) | the validator's language |
| `epad_mem_V` | lemma | membership in `epadV` (`Iff.rfl` on this file's definition) |
| `epadVirt C d y` | def | the virtual input: `pairFstD y` on padded words, `[]` otherwise |
| `epadQ C d mode` | def (language) | the bank's two query languages (exactly what the bank decides) |
| `epadVirt_of_valid`, `epadVirt_of_not_valid` | lemmas | `epadVirt` on and off the padded words |
| `epadVirt_length_le` | lemma | `\|epadVirt y\| ≤ \|y\|` |
| `epad_mem_Q_iff`, `epad_not_mem_Q` | lemmas | membership in `epadQ` for a decoded pair, and off the pairs (moved here at checkpoint 3) |
| `epad_query_mem_iff` | lemma | the bank's laws on genuine queries `⟨y, bits i⟩`, `i ≤ \|y\|` (from `epad_mem_Q_iff` since checkpoint 3) |

*Register machines (checkpoint 2).* Registers `Fin 18`; deciders `epadIn = ![inputBitLang, inputLenLang]`.

| declaration | kind | role |
|---|---|---|
| `epadOk` | def | the instructions whose syntactic preconditions hold everywhere (distinct registers in `jeq`, distinct call arguments, no input comparison) |
| `epad_preS` | lemma | `PreS` at a label holding an `epadOk` instruction, from the published `preS_of_ins` (never unfolding `PreS`) |
| `epad_ones_loop` | theorem | a strided scan of a segment: exits with its length counted if all letters are `1`, fails at the first `0` (frame and bounds) |
| `epad_mul_loop` | theorem | `q += kr · p`, by `kr` rounds of the published `registerCopy_loop` (`t := p`) and `registerScale_loop` at factor 1 (`q += t`) |
| `epad_pow_loop` | theorem | `p := p · n^dc` by `dc` multiplication rounds (`registerCopy_loop` for `kr := n` and `p := q`) |
| `EPadVL C d` | inductive | the validity block's labels (no `deriving`: derived instances would be public) |
| `epadVLAll`, `epadVLFintype` | defs | the labels listed; their `Fintype` structure, used as a local instance only |
| `epadS` | def | the block's stride: 1 on the input, 2 inside a query word |
| `epadAdvEnd`, `epadAdv`, `epadOsAdv`, `epadDI`, `epadCI` | defs | label chains in the shapes `alignedPair_loop`, `epad_ones_loop` and `arm_chain` read |
| `epadValCode` | def | **the validity block's code**: pair scan; `\|a\|+1` from the pointer; ones scan of the pad counting `\|b\|`; `P := C`, `D := d`; `P := P·(\|a\|+1)^D`; compare `\|b\| = P` |
| `epad_valid_iff_of_decode`, `epad_not_valid_of_decode` | lemmas | padded words through `pairDecode` |
| `epad_eq_replicate_iff` | lemma | a word is `1^n` iff all its letters are `1` and its length is `n` |
| `epad_val_run` | theorem | **the block's run** at either stride: reaches `yes` iff padded, registers ≥ 9 untouched, every register `≤ B`, `\|a\|+1` left in register 2 |
| `EPadVX`, `epadVXFintype` | inductive, def | the validator's extra labels (length count, answers) and their `Fintype` structure |
| `epadVA C d` | def | **the validator** as an abstract register machine |
| `epadIn`, `epadIn_mem`, `epadIn_answer` | def, lemmas | the two input deciders, in `L`, and their answers on genuine queries |
| `epad_bound` | lemma | `C (n+1)^d + d + 4n + 4 ≤ (C + d + 8)(n+1)^{d+1}` (the register bound) |
| `epad_V_mem` | theorem | **checkpoint 2**: `epadV C d ∈ LOGSPACE` (via `arm_decides_poly`) |

*The bank and the run phase (checkpoint 3).*

| declaration | kind | role |
|---|---|---|
| `EPadBX`, `epadBXAll`, `epadBXFintype` | inductive, defs | the bank's labels around the block, listed, and their `Fintype` structure (local instance only) |
| `epadZEnd` | def | the outer pair scan's advance targets |
| `epadBA C d mode` | def | **the bank** as an abstract register machine (length; outer pair scan; tail base, block limit and cap; canonical tail check; decoder; the block at stride 2; seek) |
| `epadOr` | def | the machines' oracle: the input deciders' answers |
| `epad_bank_post` | theorem | the bank's last phase: `registerCopy_loop`, one decrement, `registerScale_loop` (factor 4), `indexedSeek_loop` (stride 4), answer |
| `epad_two_pow_bits` | lemma | `2^{\|bits n\|} ≤ 2n + 1` (bounds the decoder's values) |
| `epad_bank_pre` | theorem | the bank's first phase, up to the block entry or a rejection |
| `epad_getD_four` | lemma | letter `4i` of `⟨⟨a, b⟩, w⟩` is letter `i` of `a` |
| `epad_Q_mem` | theorem | **checkpoint 3**: `epadQ C d mode ∈ LOGSPACE` (via `arm_decides_poly`) |
| `epad_run` | theorem | **checkpoint 3, the run phase**: `compile_decides` gives a machine computing `[epadVirt y ∈ L]` in space `K · T` on every input, with the ledger of §3 |

*Assembly (checkpoint 4).* No new declaration: the target's proof combines `epad_V_mem`,
`epad_run`, `computesFunInTime_const_spaceUsed` and `computesFunInTime_cond_spaceUsed`, and its
docstring gains an **Implementation** paragraph (its proof sketch is refined to the route).

## 5. Added imports and why

| import | why |
|---|---|
| `TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost` | `LogProg.OIS.compile_decides` (the run phase); transitively `Logspace/InputAccess` (input deciders `inputBitLang_mem`, `inputLenLang_mem`; ARM loops `alignedPair_loop`, `inputLength_loop`, `registerCopy_loop`, `registerScale_loop`, `arm_chain`, `register_update_le`; `vword_whole₁`, `pairEncode_getD_snd`, `drop_canon`), `Machines/ARMKit` (`arm_decides_poly`, `indicator_eq_decide`), `Machines/ARMProof` (`AReach`/`AHalt` combinators, `preS_of_ins`), `Machines/ARM` (`astep_*`), `SpaceComplexity/ConfigCount` (`computesFunInTime_and_forall_spaceUsed_le`) |
| `TCSlib.Complexity.TuringMachine.Build.Catalog` | `FinTM.computesFunInTime_cond_spaceUsed`, `FinTM.computesFunInTime_const_spaceUsed` |
| `TCSlib.Complexity.ClassNP.PolyTimePairing` | `pairFstD`, `pairFstD_pairEncode`, `length_pairFstD_le` |
| `TCSlib.Complexity.SpaceComplexity.Codec.Word` | `Codec.bitsVal_lt_two_pow` (`bitsVal w < 2^{\|w\|}`: the bank decoder's value bound), cited rather than re-proved (ground rule 5) |

None of them imports `SpaceComplexity/Padding` or `SpaceComplexity/Hierarchy` (checked on the
import closure); only the `SpaceComplexity` facade imports `Padding`, so no cycle.

## 6. Cited declarations outside the file

The citation walk `evidence/probes/EPadCites.lean` lists every constant of another TCSlib module
occurring in the module's declarations (`evidence/logs/cites-final.txt`, 121 constants with
constructors and auxiliaries); the extended import probe `#check`s each at the base
(`evidence/probes/EPadImportProbeExt.lean`, `evidence/logs/importprobe-ext-final.out`: exit 0).
By module (theorems cited, and definitions/types that occur in the statements used):

* `ClassNP.PolyTimePairing`: theorems `Complexity.length_pairFstD_le`, `Complexity.pairFstD_pairEncode`; definitions/types `Complexity.pairFstD`
* `SpaceComplexity.Basic`: theorems `Complexity.LOGSPACE_eq`, `Complexity.logSpace_le_succ`, `Complexity.mem_SPACE_iff`, `Turing.FinTM.computesInSpace_iff`, `Turing.FinTM.decidesInSpace_iff`; definitions/types `Complexity.LOGSPACE`, `Complexity.SPACE`, `Complexity.logSpace`, `Turing.FinTM.ComputesInSpace`, `Turing.FinTM.DecidesInSpace`
* `SpaceComplexity.Codec.Word`: theorems `Complexity.Codec.bitsVal_lt_two_pow`
* `SpaceComplexity.ConfigCount`: theorems `Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le`; definitions/types `Turing.FinTM.configBound`
* `SpaceComplexity.Logspace.InputAccess`: theorems `Complexity.LogProg.alignedPair_loop`, `Complexity.LogProg.arm_chain`, `Complexity.LogProg.boundedDecode_loop`, `Complexity.LogProg.canonicalTail_loop`, `Complexity.LogProg.drop_canon`, `Complexity.LogProg.indexedSeek_loop`, `Complexity.LogProg.inputLength_loop`, `Complexity.LogProg.registerCopy_loop`, `Complexity.LogProg.registerScale_loop`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.vword_whole₁`, `Complexity.indicator_inputBitLang`, `Complexity.indicator_inputLenLang`, `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`, `Complexity.pairEncode_getD`, `Complexity.pairEncode_getD_snd`; definitions/types `Complexity.inputBitLang`, `Complexity.inputLenLang`
* `SpaceComplexity.Logspace.PreimageHost`: theorems `Complexity.LogProg.OIS.compile_decides`; definitions/types `Complexity.LogProg.OIS.Ph`, `Complexity.LogProg.OIS.instDecidableEqPh`, `Complexity.LogProg.OIS.instFintypePh`, `Complexity.LogProg.OIS.prog`, `Complexity.LogProg.OIS.start`
* `SpaceComplexity.Machines.ARM`: theorems `Complexity.LogProg.astep_call`, `Complexity.LogProg.astep_clr`, `Complexity.LogProg.astep_dec`, `Complexity.LogProg.astep_half`, `Complexity.LogProg.astep_inc`, `Complexity.LogProg.astep_jeq`, `Complexity.LogProg.astep_jz`; definitions/types `Complexity.LogProg.AConf`, `Complexity.LogProg.ARM`, `Complexity.LogProg.Ins`, `Complexity.LogProg.astep`
* `SpaceComplexity.Machines.ARMKit`: theorems `Complexity.LogProg.arm_decides_poly`, `Complexity.LogProg.indicator_eq_decide`
* `SpaceComplexity.Machines.ARMProof`: theorems `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.preS_of_ins`; definitions/types `Complexity.LogProg.AHalt`, `Complexity.LogProg.AReach`, `Complexity.LogProg.PreS`
* `SpaceComplexity.Machines.Bank`: definitions/types `Complexity.LogProg.BankS`, `Complexity.LogProg.bankK`, `Complexity.LogProg.bankStart`, `Complexity.LogProg.bankTM`
* `SpaceComplexity.Machines.Bin`: theorems `Complexity.LogProg.bitsVal_bits`, `Complexity.LogProg.length_bits_le_log`, `Complexity.LogProg.length_bits_mono`; definitions/types `Complexity.LogProg.bitsVal`
* `SpaceComplexity.Machines.CleanSweep`: definitions/types `Complexity.LogProg.CleanSt`, `Complexity.LogProg.instDecidableEqCleanSt`, `Complexity.LogProg.instFintypeCleanSt`
* `SpaceComplexity.Machines.Compile`: definitions/types `Complexity.LogProg.compileFinTM`
* `SpaceComplexity.Machines.FragDec`: theorems `Complexity.LogProg.canon_bits`; definitions/types `Complexity.LogProg.Canon`
* `SpaceComplexity.Machines.Layout`: definitions/types `Complexity.LogProg.vword`
* `SpaceComplexity.Machines.ParsePlain`: definitions/types `Complexity.LogProg.ValidPair`, `Complexity.LogProg.ValidPlain`
* `SpaceComplexity.Machines.Program`: definitions/types `Complexity.LogProg.Mode`, `Complexity.LogProg.callSegs`
* `TuringMachine.Build.Catalog`: theorems `Turing.FinTM.computesFunInTime_cond_spaceUsed`, `Turing.FinTM.computesFunInTime_const_spaceUsed`
* `TuringMachine.Deterministic`: definitions/types `Turing.MultiTapeTM.indicator`, `Turing.MultiTapeTM.initCfg`, `Turing.MultiTapeTM.spaceUsed`
* `TuringMachine.Encoding`: theorems `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Turing.pairDecode_pairEncode`; definitions/types `Turing.pairDecode`, `Turing.pairEncode`
* `TuringMachine.Finite`: theorems `Turing.FinTM.computesFunInTime_iff`; definitions/types `Turing.FinTM`, `Turing.FinTM.ComputesFunInTime`, `Turing.FinTM.ComputesInTime`, `Turing.FinTM.State`, `Turing.FinTM.decEqState`, `Turing.FinTM.fintypeState`, `Turing.FinTM.k`, `Turing.FinTM.tm`

## 7. Seal (rule 7) and inspection table

Per checkpoint `<tag>` (`cp1`, `cp2`, …), under `evidence/`:
* **Foreign definitions** read by the module's declarations (types and values, auxiliaries
  included): `seal/foreign-defs-by-decl-<tag>.txt` (generated by `probes/EPadForeignDefs.lean`).
* **Sealed** (`attribute [local irreducible]`, `seal/seal-list-<tag>.txt`): every one of them
  except the exemptions below. At cp2: 18 definitions; at cp3: 34 (adding the simulator and bank
  constants `OIS.prog`, `OIS.start`, `compileFinTM`, `bankTM`, `bankStart`, `bankK`, their
  instances `OIS.instDecidableEqPh`, `OIS.instFintypePh`, `instDecidableEqCleanSt`,
  `instFintypeCleanSt`, and `ComputesInSpace`, `ComputesInTime`, `DecidesInSpace`, `logSpace`,
  `MultiTapeTM.initCfg`, `MultiTapeTM.spaceUsed`); **final: 36** (adding `ComputesFunInTime`
  and `configBound`, from the conditional and `computesFunInTime_and_forall_spaceUsed_le`).
* **`attribute [-simp]`**: every TCSlib definition the default simp set can unfold, found by
  `probes/EPadSimpDefs.lean`: `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, and from cp3 (the
  `Codec.Word` import) `NDTM.initCfg`. Added whether or not reached.
* **Not sealed, with reasons** (`seal/not-sealed-<tag>.txt`):
  * `LogProg.ARM`, `LogProg.AConf`: `abbrev` type synonyms of the published register-machine API
    (`ARM m d Λ := Λ → Ins m d Λ`, configurations as triples); every published run lemma applies
    `A l` and takes triples, so sealing them makes the published statements ill-typed at a
    concrete machine. No proof unfolds them beyond this typing.
  * `LogProg.BankS`: an `abbrev` type synonym (the bank's state type in `compile_decides`'s
    statement), `[reducible]` by declaration (Lean refuses `[local irreducible]`); never unfolded.
  * `FinTM.k`, `FinTM.State`, `FinTM.tm`, `FinTM.fintypeState`, `FinTM.decEqState`: structure
    projections of `FinTM`.
  * `LogProg.Ins.casesOn`: the auto-generated eliminator of the inductive `Ins` (reached through
    this file's own `match` in `epadOk`), `[reducible]` by construction (Lean refuses
    `[local irreducible]` on it). The same rule covers `noConfusion`, `recOn`, `brecOn`, `below`.
  * `LogProg.alignedPair_loop.match_1`: the `match` auxiliary of that published statement;
    Lean reduces matchers whatever their reducibility (its control closes even sealed:
    `logs/seal-control-matcher-demo.log`), so it cannot be sealed.
* **Sealed copy** `seal/EPadSealed-<tag>.lean` (the module with the seal block after
  `open Turing`): exit 0, no error (`logs/seal-main-<tag>.log`).
* **Controls**, one per sealed definition (`seal/EPadSealControl{Unsealed,Sealed}-<tag>.lean`):
  `#epad_seal_rfl f` states Lean's first defining equation of `f` (`f.eq_1`) and closes it by
  `intros; rfl`. Unsealed: all close (18/18 at cp2, 34/34 at cp3, **36/36 final**); sealed: all
  fail (18/18, 34/34, **36/36**)
  (`logs/seal-control-<tag>.log`).
* **Inspection table** `logs/inspection-<tag>.md`: every `rw`/`rwa`/`simp`/`simpa`/`simp_all`/
  `dsimp`/`unfold`/`show`/`change` argument on an added line, kinds resolved by a Lean probe
  (`probes/EPadKinds.lean`). At cp2: 484 arguments, at cp3: 834, **final: 861**; **no
  other-file definition is an argument** (simprocs `Fin.reduceEq`, `reduceIte` are Lean core).
  Final counts by kind: theorem 266, local hypothesis 450, own file 37, `show` restatement 24,
  bare `simp` (default set) 31, simproc 45, inline term 8.
  Own-file definitions unfolded: `epadVirt` (its two equation lemmas). The `show` steps restate
  goals through core/Mathlib reductions only (`cond`, `![…]` vectors, set-builder membership) or
  this file's definitions (`epadIn`, `epadS`, `epadVA`).

## 8. Axiom print

`evidence/logs/axioms-final.log` (`probes/EPadAxioms.lean`):

```
'Complexity.mem_SPACE_padLang' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.padLang' does not depend on any axioms
'Complexity.mem_padLang_iff' does not depend on any axioms
```

The walk over every declaration of the module (private ones and auxiliaries included) shows no
`sorryAx` anywhere and nothing beyond `[propext, Classical.choice, Quot.sound]`. (At cp1–cp3 the
target printed `sorryAx`: the base's own `sorry`, which checkpoint 4 removes.)

## 9. Duplication search per private

* **By name**: `git grep -n "epad\|EPad"` over `TCSlib/` at the base: no hit (prefix unused).
* **`exact?` probe on every private lemma's statement**, placed just before it in a scratch copy
  of the module (`probes/EPadDupProbe.lean`, generated by `tools/epad_dup.py`; log
  `logs/dup-exact-<tag>.log`, table `logs/dup-exact-<tag>.md`). At cp2, of 17 private lemmas
  and theorems, 16, at cp3 and final, of 25, 24: "`exact?` could not close the goal";
  `epad_mem_V` is closed by `Eq.to_iff rfl` (it is definitional on this file's own definition).
* **By statement** (`git grep` over `TCSlib/SpaceComplexity/` for the published loop and run
  lemmas, `*_loop`/`*_run`):
  * `epad_preS`/`epadOk`: the published facts are `preS_of_ins` (used) and `GuardLe.of_preS`;
    the library's loops prove `PreS` inline by unfolding it, which this file may not; no
    published per-instruction lemma. (A first draft had eight per-instruction copies; the
    screen flagged them as mutual copies and they were merged into this one lemma before the
    commit.)
  * `epad_ones_loop`: the published scans are `alignedPair_loop` (pair parse),
    `canonicalTail_loop` (last letter and width), `Codec.scan_loop` (a two-pointer lockstep fold,
    stated with the `GuardLe` guard); none checks that a strided segment is all ones while
    counting it.
  * `epad_mul_loop`, `epad_pow_loop`: published arithmetic loops are `registerCopy_loop`,
    `registerScale_loop` (fixed factor; both used inside), `arm_chain`, and in `ARMLoops`
    `move_run`/`copy_run`/`shl_run` (by `2^c`)/`halve_run`/`sub_run`; none multiplies by a
    register or raises to a power. `Logspace/QueryReshape` has **private** factor/power runs
    (`comp_factor_run`, `comp_power_run`) over its own machine `compARM`: not published, not
    citable, not re-walked; the screens show no copy. An earlier draft of this file had its own
    addition loop; it was replaced by the published `registerCopy_loop` + `registerScale_loop`
    before the checkpoint 2 commit.
  * `epad_valid_iff_of_decode`, `epad_not_valid_of_decode`, `epad_eq_replicate_iff`, `epad_bound`,
    `epadIn_*`, `epad_val_run`, `epad_V_mem`: statements about this file's definitions or plain
    arithmetic/list facts with no published counterpart (`List.eq_replicate_iff` is used inside
    `epad_eq_replicate_iff`).
  * The bank (`epad_bank_pre`, `epad_bank_post`, `epad_Q_mem`): built from the published
    `inputLength_loop`, `alignedPair_loop`, `registerCopy_loop`, `canonicalTail_loop`,
    `boundedDecode_loop`, `registerScale_loop` and `indexedSeek_loop`; the published query
    validators of `Logspace/InputAccess` (`access_mem`) and `Logspace/QueryReshape` (`drop_mem`,
    `comp_mem`) are private and decide other languages (`inputBitLang`/`inputLenLang`, the
    reshaped queries); none decides a query about a padded word's first component.
    `epad_two_pow_bits` has no published counterpart (`length_bits_le_log`,
    `Nat.pow_log_le_self` are used inside); `epad_getD_four` composes `pairEncode_getD` twice.
    A draft `epad_query_mem_iff` re-proved part of `epad_mem_Q_iff`; the screen flagged the pair
    and it now cites it.
  * The time-side paddings (`ClassNP/Nondeterminism.lean`'s `C·2^{(|x|+1)^c}` padding,
    `Diagonalization/EXPCOM.lean`, `ClassNP/NP.lean`'s private `paddedVerifier`) define padded
    languages for time classes; none is a space-bounded validator.

**Per private** (final; "no hit" = `git grep -n <name>` over `TCSlib/` at the base):

| private | kind | by name | by statement (`git grep` of the published loops/runs and paddings) | `exact?` before it |
|---|---|---|---|---|
| `epadValid` | def | no hit | time-side paddings (`Nondeterminism`, `EXPCOM`, `NP.paddedVerifier`) pad for time classes with other pads; no polynomial-pad validity predicate | — (definition) |
| `epadV` | def | no hit | as `epadValid` | — (definition) |
| `epad_mem_V` | lemma | no hit | about `epadV` | closed by `Eq.to_iff rfl` (definitional, own definition) |
| `epadVirt` | def | no hit | no published "first component or empty" map; it is `pairFstD` (cited) guarded by `epadValid` | — (definition) |
| `epadQ` | def | no hit | no published query language about a padded word's first component (`indexLang` is not used: membership off genuine pairs has no published reading) | — (definition) |
| `epadVirt_of_valid` | lemma | no hit | about `epadVirt` | could not close |
| `epadVirt_of_not_valid` | lemma | no hit | about `epadVirt` | could not close |
| `epadVirt_length_le` | lemma | no hit | from `length_pairFstD_le` | could not close |
| `epad_mem_Q_iff` | lemma | no hit | about `epadQ` | could not close |
| `epad_not_mem_Q` | lemma | no hit | about `epadQ` | could not close |
| `epad_query_mem_iff` | lemma | no hit | from `epad_mem_Q_iff`, `bitsVal_bits`, `canon_bits`, `drop_canon`, `length_bits_mono` | could not close |
| `epadOk` | def | no hit | mirrors the cases of `PreS` as a predicate on one instruction; no published counterpart (only `preS_of_ins`, used) | — (definition) |
| `epad_preS` | lemma | no hit | `preS_of_ins` (cited) is the general form; `GuardLe.of_preS` needs `PreS` already | could not close |
| `epad_ones_loop` | theorem | no hit | published scans: `alignedPair_loop`, `canonicalTail_loop`, `Codec.scan_loop` (two-pointer fold, `GuardLe` guard); none checks a strided all-ones segment while counting it | could not close |
| `epad_mul_loop` | theorem | no hit | published: `registerCopy_loop`, `registerScale_loop` (fixed factor; both used inside), `ARMLoops.shl_run` (by `2^c`); `QueryReshape.comp_factor_run` is private; none multiplies by a register | could not close |
| `epad_pow_loop` | theorem | no hit | `QueryReshape.comp_power_run` is private (own machine `compARM`); no published power loop | could not close |
| `EPadVL` | inductive | no hit | labels of this file's block | — (definition) |
| `epadVLAll` | def | no hit | — | — (definition) |
| `epadVLFintype` | def | no hit | replaces a `deriving Fintype` (whose instances would be public) | — (definition) |
| `epadS` | def | no hit | — | — (definition) |
| `epadAdvEnd` | def | no hit | — | — (definition) |
| `epadAdv` | def | no hit | — | — (definition) |
| `epadOsAdv` | def | no hit | — | — (definition) |
| `epadDI` | def | no hit | — | — (definition) |
| `epadCI` | def | no hit | — | — (definition) |
| `epadValCode` | def | no hit | the block's code; no published register program validates padded pairs | — (definition) |
| `epad_valid_iff_of_decode` | lemma | no hit | about `epadValid`; uses `pairDecode_pairEncode`, `eq_pairEncode_of_pairDecode` | could not close |
| `epad_not_valid_of_decode` | lemma | no hit | as above | could not close |
| `epad_eq_replicate_iff` | lemma | no hit | `List.eq_replicate_iff` (cited inside) in the `getD` form the scan produces | could not close |
| `epad_val_run` | theorem | no hit | the block's run; no published counterpart | could not close |
| `EPadVX` | inductive | no hit | — | — (definition) |
| `epadVXFintype` | def | no hit | as `epadVLFintype` | — (definition) |
| `epadVA` | def | no hit | the validator program | — (definition) |
| `epadIn` | def | no hit | the pair `![inputBitLang, inputLenLang]` of published deciders | — (definition) |
| `epadIn_mem` | lemma | no hit | from `inputBitLang_mem`, `inputLenLang_mem` | could not close |
| `epadOr` | def | no hit | the machines' oracle | — (definition) |
| `epadIn_answer` | lemma | no hit | from `indicator_inputBitLang`, `indicator_inputLenLang` | could not close |
| `epad_bound` | lemma | no hit | arithmetic; no published bound of this shape | could not close |
| `epad_V_mem` | theorem | no hit | no published validator of padded words | could not close |
| `EPadBX` | inductive | no hit | — | — (definition) |
| `epadBXAll` | def | no hit | — | — (definition) |
| `epadBXFintype` | def | no hit | as `epadVLFintype` | — (definition) |
| `epadZEnd` | def | no hit | — | — (definition) |
| `epadBA` | def | no hit | the bank program; the published query validators (`InputAccess.access_mem`, `QueryReshape.drop_mem`/`comp_mem`) are private and decide other languages | — (definition) |
| `epad_bank_post` | theorem | no hit | built from `registerCopy_loop`, `registerScale_loop`, `indexedSeek_loop` | could not close |
| `epad_two_pow_bits` | lemma | no hit | no published lemma (`length_bits_le_log`, `Nat.pow_log_le_self` used inside) | could not close |
| `epad_bank_pre` | theorem | no hit | built from `inputLength_loop`, `alignedPair_loop`, `registerCopy_loop`, `canonicalTail_loop`, `boundedDecode_loop` | could not close |
| `epad_getD_four` | lemma | no hit | two applications of `pairEncode_getD` (cited) | could not close |
| `epad_Q_mem` | theorem | no hit | no published logspace bank for a padded word's first component | could not close |
| `epad_run` | theorem | no hit | its host is `OIS.compile_decides`; the consumer `mem_LOGSPACE_preimage` is logspace-only (needs `ImplicitlyLogspaceComputable`, which this file can neither build without unfolding nor needs) | could not close |

## 10. Screens

`scripts/copy-text-screen-v3.py` under `nice -n 10`, on frozen `git worktree`s of the base and of
the checkpoint commit, one at a time; population = `Padding.lean` + every TCSlib file in the
citation walk (`evidence/screens/population-<tag>.txt`); outputs `screens/screen-base-<tag>.txt`,
`screens/screen-after-<tag>.txt`, their difference `screens/screen-diff-<tag>.txt`.

| checkpoint | files | before: declarations / pairs | after: declarations / pairs | new pairs |
|---|---:|---|---|---:|
| cp1 | 7 | 154 / 21 | 157 / 21 | 0 |
| cp2 | 14 | 249 / 33 | 273 / 33 | 0 |
| cp3 | 20 | 336 / 39 | 372 / 39 | 0 |
| final | 22 | 783 / 333 | 820 / 333 | 0 |

## 11. Per-module time and memory

`evidence/logs/module-checks-<tag>.log` (`scripts/lean_check_tree.sh` through `tools/chkE.py`):

| checkpoint | `SpaceComplexity/Padding` | `SpaceComplexity` facade |
|---|---|---|
| cp1 | 1.2 s, 1833 MiB | 1.2 s, 2198 MiB |
| cp2 | 25.3 s, 2001 MiB | 1.2 s, 2130 MiB |
| cp3 | 42.9 s, 2228 MiB | 1.2 s, 2134 MiB |
| **final** | **44.8 s, 2252 MiB** | **1.1 s, 2133 MiB** |

## 12. Checkpoints

| checkpoint | status |
|---|---|
| 1 design note and route probe | **reached** (commit `07b50af5`, `fill-epad-cp1.zip`, exchange `839b39b7`) |
| 2 validator | **reached** (`epad_V_mem`, commit `53c3d0c2`, `fill-epad-cp2.zip`, exchange `515030bd`) |
| 3 run phase | **reached** (`epad_Q_mem`, `epad_run`, commit `80072733`, `fill-epad-cp3.zip`, exchange `98a3c1a4`) |
| 4 assembly and ledger | **reached** (`mem_SPACE_padLang`, commit `7d16731e`, `fill-epad.zip`) |

## 13. Escalations

None. No public lemma of another file is missing for this route.

## 14. Disclosures

* The module docstring is unchanged (its headings are frozen); its "Main results" line still
  reads "(Statement; its proof is a fill.)" and its "Implementation notes" mention a copy of the
  first component, which this proof does not make (it reads the component in place). The
  maintainer may want to update both; the target's own docstring now carries the
  Implementation paragraph.
* Seal exemptions (§7) are type synonyms (`ARM`, `AConf`, `BankS`), structure projections of
  `FinTM`, auto-generated eliminators (`Ins.casesOn`) and a `match` auxiliary; each with its
  reason in `seal/not-sealed-final.txt`.

* The checkpoint 3 commit was recommitted once before any delivery (local, never pushed), so
  that `epad_query_mem_iff` cites `epad_mem_Q_iff` instead of repeating its argument.
* The checkpoint 2 commit was recommitted twice before any delivery (`git reset --soft HEAD~1`
  on the local, never-pushed versions: first to replace a private addition loop by the published
  `registerCopy_loop`/`registerScale_loop`, then to merge eight per-instruction `PreS` lemmas
  and two decider-answer lemmas that the screen flagged as mutual copies), keeping one commit
  per checkpoint. No delivered history was changed.
* The first run of the final packaging script (`tools/epad_pack.sh final`) was started in the
  foreground and stopped by the tool's 5-minute limit during the seal step (03:57–04:02); no
  other Lean process was running. It was rerun from the start in the background
  (`logs/pack-final.out`), one Lean process at a time; all final evidence is from that rerun.
* `release.lean-lang.org` is unreachable from this host; the pinned toolchain was installed from
  the official GitHub release archive (§2).
