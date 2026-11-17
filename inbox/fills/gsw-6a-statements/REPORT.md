# gsw-6a-statements · final delivery (GSW phase 6a statements and owner PR O1)

Claude was the worker: a lead with two sub-agents, `bp` and `fa`. This delivery replaces checkpoint 1 (exchange commit `c0e11b31`).
Every branch is local. Nothing was pushed to a campaign branch.

## 1. Base, heads, inputs

- **Issue base:** `f6f295a6502b72bbf498bb8c64b63f847e910866`, the tip of `cryptography/pass-shelat-ch2-4` at issue.
  - It was fetched by name into the separate clone `/home/user/gsw6a`.
  - Every piece of work started from it.
- **Records pin:** `c5eb7cf4b9f13eb2d4340493b7537b9de092d457`.
  - `briefs/lattice-gsw/phase6/plan-section.md` (`06824b3d…`) and `rulings.md` (`312fef45…`) equal the pack's `inputs/`.
  - The seven files of `issued-6a-r1/` that are also in the pack are byte-equal to it.
- **Exchange pack:** read at `7031cef6ea880180f265fd5878d26a37a25b868f`. `shasum -a 256 -c` passes on `SHA256SUMS` (6 files) and on `inputs/SHA256SUMS` (4 files).
  - The Bar89 ingest also equals the base's `blueprint/src/references/` copy (`0e14d97e…`).
- **O1 head:** `owner/o1-balanced` = `413e9aa42f6b96b4d65673c37c83819b2fb77579`, one commit.
- **Statement head:** `stmt/gsw-6a` = `ec36703b56513d575036fa75ddb0b2b9d3f893b6`, five commits on O1, as the brief suggests:

| Commit | Contents |
|---|---|
| `ad8e170f` | BranchingPrograms/Defs and Eval |
| `0c39a064` | Barrington, BarringtonConverse, NC1 and the facade |
| `4981a2a9` | NANDForm and NANDLayering |
| `5159f5c9` | the rest of FormulaArith |
| `ec36703b` | registrations, CircuitComplexity/ComputationalModels/TCSlib imports, and the `machine-library-design.md` rows |

  - Each commit adds only files whose imports already exist at that commit. The facades and registrations come last, so every commit compiles.
- **Signing:** both series were committed with `commit.gpgsign=false` (column `signing` = `none` in each `COMMITS.tsv`).
- **Reproduction:**
  - `patches/o1/` and `patches/stmt/` were applied with `git am` in a scratch clone of the base, setting the committer fields from `COMMITS.tsv`.
  - This reproduces `413e9aa4` and then all five statement hashes (`evidence/git/reproduce.txt`).
- **Open PRs at issue:** the work stayed on the issue base. The single shared path with #331 is `TCSlib.lean`.
  - The new import is `import TCSlib.Complexity.BranchingPrograms` at line 28, directly after line 27 (`import TCSlib.Complexity.CircuitComplexity`) in the Complexity block.
  - That is far from #331's hunk at line 75.

## 2. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`, `preflight-assessment.txt`):
  - `nproc` 4.
  - No cgroup memory limit, so the headroom is `MemAvailable`: 14.65 GiB, above the 4 GiB floor.
  - `/dev/vda` (ext4) had 15.11 GiB free, above the 12 GiB floor.
  - Pass. No E-RES condition occurred at any point.
- **Toolchain:** `elan` installed `leanprover/lean4:v4.25.0` (`toolchain.log`).
- **Cache:**
  - The archive store `~/.cache/mathlib` did not exist before the first fetch (`cache-store.log`).
  - One narrowed `TAR_OPTIONS=--no-same-owner lake exe cache get` ran on the 377 roots (`mathlib-roots.txt`, which equals the pack's `roots.txt`). It attempted 3,607 files, downloaded 3,607, decompressed 3,607, and exited 0 (`cache-get.log`).
  - No zero-size olean. No other cache command ran.
  - The new files' Mathlib imports are all inside the fetched closure, so no second fetch was needed.
- **Packages:** `package-check.log` ends `RESULT: PASS: 11 present, 0 mismatched, absent: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean`. No module imports an absent package.
- **One Lean process at a time** on the host, for all three agents, through one `flock` (`tools/check.py`, `sweep.py`, `runner_lock.py`). Lean was never run with `lake build`.
- **PFR (disclosed adaptation).** Five library modules (`CommunicationComplexity/NewmanTheorem/…`) import the package `PFR`, which the Mathlib cache does not cover.
  - The 31 PFR modules they need (all importing only Mathlib, all of whose imports are in the cache) were compiled with plain `lean <file> -o <the lead's TCSlib olean tree>/PFR/…`.
  - They ran one at a time, under the lock, in import order (`evidence/build/pfr/`).
  - Nothing was written inside `.lake/packages`. No package tree was copied or modified. `lake` was not used.
  - Without this, the root build could not have reached `TCSlib`.
- **Sub-agents.**
  - Each had its own sparse worktree (`/home/user/wt-bp`, `/home/user/wt-fa`) and its own TCSlib olean tree, seeded by copying the lead's bootstrapped TCSlib oleans.
  - `.lake/packages` was a symlink to the lead's.
  - Only the lead ran `lake`. Only the lead committed.

## 3. Who wrote what

| Agent | Wrote |
|---|---|
| **Lead** | O1 (`FormulaArith/Combinators.lean` O1 part, `FormulaArith.lean` facade, `TreeNCAC.lean`, `CircuitComplexity.lean`); `NANDForm.lean`; `NANDLayering.lean`; the registrations (`CircuitComplexity.lean`, `ComputationalModels.lean`, `TCSlib.lean`); the `machine-library-design.md` rows H18–H20 and the gadget subsection; probes P8, P9; all evidence tools and checks; every commit and the delivery |
| **Sub-agent `bp`** | `BranchingPrograms.lean` and `BranchingPrograms/{Defs,Eval,Barrington,BarringtonConverse,NC1}.lean`; probes P0–P7 |
| **Sub-agent `fa`** | the F1–F3 part of `Combinators.lean` (appended after O1's text, which stays byte-identical); `FormulaArith/{CarrySave,Compare,ModSum}.lean`; the facade's new import and contents lines; probes P10a–c and T0 |

The lead's edits to sub-agent files:
- one Bar89 quotation made verbatim (`BarringtonConverse.lean`, "yielded by a each instruction", sic);
- the reader `BranchingProgramFamily.language_eq` (`Defs.lean`, for lint check 8);
- the three `set_option` lines and the extended Combinators contents line in the `FormulaArith.lean` facade.

The sub-agents' reports are `evidence/subagents/{bp,fa}/REPORT.md`, with their logs.

## 4. Statement list (check 3) and the r3 row map

- **decls2:** `decls2.py . f6f295a6 <17 new and changed Lean files>` gives **271 ADDED, 0 CHANGED, 0 REMOVED** (`evidence/stmt/decls2.tsv`). The moved O1 privates are not public, so they are not listed.
- **StmtDump** (`evidence/stmt/StmtDump.lean`, `.log`) prints every constant of the 14 new and changed modules, with its full name, kind, module and type, and the library constants the type mentions.
- **Row map** (`evidence/stmt/rowmap.txt`, from the row markers that open each target's docstring). Every row of C1–C25, N1–N13, F1–F3, F5–F10 has its declarations, and every admitted declaration belongs to a row:

| Row | Declarations (all `sorry` unless marked) |
|---|---|
| C1 | `BranchingProgram.yield_append`, `yield_nil` |
| C2 | `yield_conj`, `length_conj`, `length_append` |
| C3 | `yield_complementLast`, `length_complementLast` |
| C4 | `isPermutation_iff` (**proved**, it is `IsPermutation`'s `_iff` reader), `IsPermutation.append`, `.conj`, `.complementLast`, `.bijective_yield` |
| C5 | `evalWith_nil`, `evalWith_append` |
| C6 | `Instr.stepWith_of_isPermutation` |
| C7 | `evalWith_rel` |
| C8 | `evalWith_single` |
| C9 | `isFiveCycle_sigma1`, `isFiveCycle_sigma2`, `isFiveCycle_commutator` |
| C10 | `conjugator_conj` |
| C11 | `FiveCycleRecognizes.conj` |
| C12 | `FiveCycleRecognizes.complementLast` |
| C13 | `barrington_recognizes` |
| C14 | `barrington_length_le`, `barrington_length_pos` |
| C15 | `isPermutation_barrington` |
| C16 | `barrington_yield_zero` |
| C17 | `Instr.wire_eval`, `Instr.depth_wire_le`, `Instr.maxFanin_wire_le` |
| C18 | `wireComp_eval`, `depth_wireComp_le` |
| C19 | `compTree_eval`, `depth_compTree_le`, `maxFanin_compTree_le` |
| C20 | `toFormula_eval` |
| C21 | `depth_toFormula_le`, `maxFanin_toFormula_le` |
| C22 | `BranchingProgram.exists_fiveCycleRecognizes_of_dagCircuit` |
| C23 | `Language.InNC.inPBP_five` |
| C24 | `Language.InBWBP.inNC_one` |
| C25 | `Language.inNC_one_iff_inBWBP`, `Language.inNC_one_iff_inPBP_five` |
| N1 | `BoolCircuit.DAGGate.eval_of_isNAND` |
| N2 | `BoolCircuit.nandGadget_correct` |
| N3–N6 | `DAGCircuit.toNANDForm_eval`, `_isNANDForm`, `_depth_le`, `_size_le` |
| N7–N11 | `DAGCircuit.layerNAND_eval`, `_isLayered`, `_isNANDForm`, `_depth`, `_size_le` |
| N12–N13 | `DAGCircuit.layerGates_acyclic`, `DAGCircuit.layerOutput_lt` |
| F1 | `TreeCircuit.neg_eval`, `depth_neg`, `maxFanin_neg` |
| F2 | `subst_eval`, `depth_subst_le`, `maxFanin_subst_le`, `rename_eval`, `depth_rename` |
| F3 | `const_eval`, `depth_const`, `maxFanin_const`, and for each of `and2`, `or2`, `xor2`, `xor3`, `maj3`: `_eval`, `depth_*_le`, `maxFanin_*_le` |
| F5 | `FormulaArith.csaStep_val`, `depth_csaStep_le`, `maxFaninL_csaStep_le` |
| F6 | `csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`, `csaLevels_le` |
| F7 | `carryOut_eval`, `carryOut_eval_le`, `depth_carryOut_le`, `maxFanin_carryOut_le` |
| F8 | `geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le` |
| F9 | `modSumInterval_eval` |
| F10 | `depth_modSumInterval_le`, `modSumDepth_le`, `maxFanin_modSumInterval_le` |

**100 admitted targets in all.** Per module:

| Module | Targets |
|---|---|
| Defs | 11 |
| Eval | 5 |
| Barrington | 11 |
| BarringtonConverse | 11 |
| NC1 | 5 |
| NANDForm | 6 |
| NANDLayering | 7 |
| Combinators | 26 |
| CarrySave | 7 |
| Compare | 7 |
| ModSum | 4 |

`evidence/stmt/targets-per-module.tsv` has these counts.

Each target's docstring has four parts:
- It opens with the statement in words and its formula.
- It gives the r3 tag with the anchor of §H1 (e.g. `[Bar89, Thm 1, p003-b002]`, `[BV11, Lemma 4.5, p029-b001]`), or says "Glue" (NAND, layering, host readers, combinators).
- It states every deviation r3 lists:
  - BV14's instruction order against Bar89's;
  - program order and the Mathlib product;
  - the `σ 0` reading;
  - the OR case through Lemma 2;
  - Thm 2 as a formula;
  - NAND form not `IsWellFormed`;
  - literal inputs for the layering;
  - the carry-save tree.
- It ends with a `**Proof sketch.**` naming the readers and host lemmas the fill will use.

**Citations.** Every quotation in the new files was checked against the ingests (`evidence/stmt/quotes-check.txt`).
- Every quotation is the ingest's text in Unicode rendering.
- The one inexact quotation was fixed verbatim.
- Every anchor exists in the ingest of its tag.
- No `[Gen09]` appears anywhere.

## 5. Definitions and their readers

`evidence/stmt/definitions-readers.txt` lists, per file, every definition with its proved readers. In summary:

- **Every new public `def`/`structure` has its readers, proved**, all by `rfl`, `Iff.rfl`, or a short proof from its own file's definitions:
  - `_eq` (by `rfl`), or case lemmas covering every input: `nandGadget_*` (7 cases), `barrington_*` (7 cases), `layerChain_zero`/`_succ`, `compTree_nil`/`_singleton`/`_cons_cons`, `complementLast_nil`/`_concat`, `csaLayer_*`, `csaLevels_*`;
  - `_iff` for predicates: `isNAND_iff`, `isNANDForm_iff`, `isLayered_iff`, `isFiveCycle_iff`, `fiveCycleRecognizes_iff`, `isPermutation_iff`, `isPolyLength_iff`, `inBWBP_iff`, `inPBP_iff`;
  - non-simp `simps` for structures: `Instr.ofPerm`, and `DAGCircuit.layerNAND` (`layerNAND_gates`, `layerNAND_output`).
- No `@[simp]`, no global attribute, no `native_decide`, no `axiom`.
- **Computable, as r3 requires:** `barrington`, `conjugator` (built from `θ (σ^k 0) = τ^k 0` with the inverse `Fintype.bijInv`, not `Equiv.ofBijective`), `nandGadget`, `layerGates`/`layerOutput`, and the whole formula arithmetic.
- `toFormula` is `noncomputable` (it enumerates a `Finset`), which r3 allows.
- **Termination proofs are real:** `barrington` (well-founded on `sizeOf`), `compTree` (on the list length), `neg`/`subst` (structural, mutual through the child list), `csaLevels` (fuel).
- **Definitions that carry a target proof:**
  - `DAGCircuit.toNANDForm` passes N2 (`nandGadget_correct`) to `rewrite`.
  - `DAGCircuit.layerNAND`'s two proof fields are N12 and N13.
  - No other definition cites a target (§8).
- **Decidability instances** (needed for the probes' `decide`): `DAGGate.decidableIsNAND`, `DAGCircuit.decidableIsNANDForm`, `DAGCircuit.decidableIsLayered`, `instDecidablePredIsFiveCycle`.

## 6. Statement changes against r3

No change of meaning. No probe showed an r3 statement false.

**NANDForm and NANDLayering (lead)**
1. **N12 is stated in the `args_lt` field's form**: `∀ (i : ℕ) (h : i < C.layerGates.length), ∀ a ∈ (C.layerGates[i]).args, a < n + n + i`. r3's form is `GatesAcyclic (n + n) C.layerGates`.
   - `GatesAcyclic` (`DAGCircuit.lean:395`) has no published reader.
   - Filling `layerNAND`'s field from a `GatesAcyclic` proof would unfold it inside a definition body, a Rule 10 breach that the seal fails.
   - The two propositions are the same (the field is `GatesAcyclic`'s body).
   - Seyoon may prefer r3's form with an owner-side `gatesAcyclic_iff` (question Q2, §16).
2. `DAGGate.eval_of_isNAND` takes `{g : DAGGate}` implicitly, since `autoImplicit` is off. `nandGadget` is total: an `∧`/`∨` gate of fan-in ≥ 3 lies outside N2's domain and is copied. The docstring says so; r3 does not specify this case.
3. **The column builder is public, with readers:** `layerChain` (`_zero`, `_succ`), `DAGCircuit.layerAt` (`_eq`), `layerColumn` (`_eq`), `layerFold` (`_eq`). r3 says "with its column builder" without names.
4. **The decidability instances of §5 were added.**

**BranchingPrograms (sub-agent bp)**
5. **`sigma1`, `sigma2` are `List.formPerm [0,1,2,3,4]` and `List.formPerm [0,2,4,3,1]`.**
   - Mathlib's `c[…]` notation lives in `Mathlib.GroupTheory.Perm.Cycle.Concrete`, which is outside the Mathlib closure fetched for this job.
   - `c[l] = Cycle.formPerm ↑l = List.formPerm l`; the docstrings say so.
   - An extra narrowed fetch could add it if preferred (Q4).
6. **C7 and C6 read through the readers.**
   - C7's index is `B.instrs[t]'(ht.trans_eq B.length_eq)`, because `length` is foreign to Eval.
   - C6 projects with `(ι.isPermutation_iff.1 hι).1`.
   - Both keep r3's binders and meaning.
7. **Explicit binders where `autoImplicit` is off:**
   - `{σ τ}` in C10–C13 and C16;
   - `{c}` in C14 `barrington_length_le` and C16;
   - `wireComp_eval`/`depth_wireComp_le` take `(i k) (x)` after the hypotheses, with `f`, `g` implicit.
8. **`compTree`'s readers use the pattern `ι₁ :: ι₂ :: l`**, split at `length / 2`.
9. **`conjugator` reads its map from a stored list (`conjugatorTable`).** Otherwise Barrington's nested conjugates are recomputed at every application (exponential in depth; measured 2.3 s against 3 ms on a depth-2 formula). The meaning and C10 are unchanged.
10. **Extra glue helpers:**
    - `Instr.isPermutation_ofPerm`, proved;
    - `conjugatorIndex`, `conjugatorFun`, `conjugatorTable`, `commutatorProgram`, each with readers;
    - `FiveCycleRecognizes` is defined as `IsFiveCycle σ ∧ ∀ x, (A x → yield = σ) ∧ (¬A x → yield = id)`, which needs no decidability.

**FormulaArith (sub-agent fa)**
11. **`⨆` is written `Finset.univ.sup`** in `depth_subst_le` and `maxFanin_subst_le`, with the same value.
    - `SupSet ℕ` is not in `Combinators.lean`'s import closure, whose header is O1's and must stay byte-identical.
    - r3 gives no formula for `maxFanin_subst_le`. Chosen: `≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin)`.
12. **`carryOut U W b` takes the position `b` explicitly.** r3's sketch leaves `b` free.
13. **Formulas where r3 names only the lemma:**
    - `csaStep_val`: `val x A + val x B + val x C = val x S + val x K`.
    - `depth_csaStep_le`: `maxDepth (S ++ K) ≤ max 1 (maxDepth (A ++ B ++ C)) + 4`.
    - `csaReduce_val`: `val x U + val x W = (Us.map (val x)).sum`.
    - `depth_csaReduce_le`: `≤ max 1 (maxDepth Us.flatten) + 4·csaLevels |Us|`. The `max 1` is there because a padding constant `node b []` has depth 1.
    - `depth_geConst_le`: `≤ max 1 (maxDepth (U ++ W)) + 2⌈log₂(max |U| |W| + 1)⌉ + 7`.
14. **Fan-in lemmas were added** for every gadget and for `csaStep`, `csaReduce`, `carryOut`, `geConst`, and `const_eval`/`depth_const`/`maxFanin_const` too. The files are foreign to each other, so these lemmas are the only route to F10's fan-in ≤ 2.
15. **`modSumInterval_eval`** keeps r3's hypotheses and right-hand side; only `{a q lo hi}` are implicit.
    - P10 found `hlh : lo ≤ hi` unnecessary on everything tested. It is kept as in r3, and the docstring notes this (Q5).
    - `ha` and `hhq` are necessary. Counterexamples are recorded in P10.
16. **Public helpers:** `csaLayer`, `constBits`, `maskedConst`, each with an `_eq` reader. `csaLevelsAux` has its `_fuel` lemma.

## 7. Constants settled (*(fix)*)

Each constant was derived by hand from the definitions and checked numerically. Kernel `decide` was used where the kernel reduces, otherwise `#eval` with recorded output.

| Item | Constant | Derivation and checks |
|---|---|---|
| **C19** `depth_compTree_le` | `(⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1` (r3's) | Leaves have depth ≤ 1. A split adds `⌈log₂ w⌉ + 1` (`depth_balanced_le`) plus 1 (the binary `∧`). The halves satisfy `⌈log₂⌈l/2⌉⌉ = ⌈log₂ l⌉ − 1`. P7 sweep for `l ≤ 17`, `w ≤ 4`; tight at `l ≤ 1`. |
| **C21** `topDepth w` | `w·⌈log₂ w⌉ + ⌈log₂ w⌉ + 3` (r3's draft was `+4`) | The inner `⋀` adds `⌈log₂ w⌉ + 1`. The outer `⋁` over at most `w^w` maps adds `≤ w⌈log₂ w⌉ + 1`. P7 sweep: slack ≥ 2. |
| **F3** gadget depths | +1, +1, +2, +4, +3 (r3's) | Follow from the constructions, `neg` being depth-preserving. `const` has depth 1. |
| **F5** | `+4` over `max 1 D` | `xor3` +4, `maj3` +3, padding depth 1. |
| **F6** `csaLevels_le` | `csaLevels k ≤ 2⌈log₂ k⌉` (r3's draft was `+3`) | Two layers take `k` to `≤ ⌈k/2⌉` for `k ≥ 20`; small cases by computation. Kernel `decide +kernel` for `k < 512`; `#eval` for `k < 100000`; 0 failures. The stronger bound makes F10's closed form follow. |
| **F7** `depth_carryOut_le` | `max 1 D + 2⌈log₂ b⌉ + 3` (r3's draft was `2⌈log₂(b+1)⌉ + 2`) | Item `+1`, inner balanced `∧` `+⌈log₂ b⌉ + 1`, outer balanced `∨` `+⌈log₂ b⌉ + 1`. |
| **F8** | `max 1 D + 2⌈log₂ p⌉ + 7`, `p = max |U| |W| + 1` | `csaStep` +4 then `carryOut` at `p`. |
| **F10** `modSumDepth M q` | `4·csaLevels M + ⌈log₂ M⌉ + 2⌈log₂(⌈log₂ M⌉ + ⌈log₂ q⌉ + 1)⌉ + 10` | `modSumDepth_le` is **r3's closed form verbatim**: `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉ + 21`. `#eval` on `M, q < 300` (90,000 cases, minimum slack 11) and on a sparse grid up to `M ≈ 1.3·10⁵`, `q ≈ 2^59`; 0 failures. No depth term is linear in `log q` (r3 §H3.3). |
| **N11** `layerNAND_size_le` | `2n + (2·depth + 1)·size` (r3's) | A column has ≤ `2(D − δ) + 1` gates. The `+1` comes from the fan-in-0 twin `NAND(NAND(x₀,¬x₀))`. Input columns have `2D − 1` gates; dead vertices have none. P9 checks it on three circuits. |
| **topDepth / C21 consistency** | `toFormula` depth `≤ (⌈log₂ w⌉+2)·⌈log₂ l⌉ + topDepth w` | — |

## 8. Builds (checks 1–2)

**Order.** `evidence/build/order-final.txt` is `order.txt` with the 13 new modules inserted after their imports, facades after their children (1,353 modules).

**Closure, O1 head** (`evidence/build/o1/`):
- The prefix, modules 1–10 of `order.txt`, was checked first in the lead's clone `/home/user/gsw6a` (`bootstrap.log`).
  - Eight of them are unchanged at base, O1 and final (`evidence/build/root/prefix-identity.txt`).
  - The other two, `TreeNCAC` and `NCAC`, are checked again in both closures below.
- The lead's TCSlib oleans were then copied into the separate worktree `wt-o1`'s own tree (TCSlib oleans only; no Mathlib or package tree).
- There, at `413e9aa4`: `Combinators`, `FormulaArith`, `TreeNCAC`, `NCAC`, `Parity`, `Hierarchy`, the facade `CircuitComplexity`, and `ComputationalModels` (`closure-o1.log`).

All rc=0, 0 errors, 0 `sorry`.

**Closure, final head** (`evidence/build/final-closure/summary.txt`), 19 modules, in final order: the 13 new modules and the six downstream ones (TreeNCAC, NCAC, Parity, Hierarchy, the facade, `ComputationalModels`). All rc=0, 0 errors. The `sorry` warnings equal the targets per module.

**Downstream** of a changed module, within `order.txt`: TreeNCAC, NCAC, Parity, Hierarchy, the facade, `ComputationalModels` and the root `TCSlib` (`evidence/build/downstream.txt`). Nothing else imports a changed file.

**Root build** (`evidence/build/root/summary-all.tsv`: 1,353 rows, one per module of `order-final.txt`, each tagged with its part) has four parts, all in the lead's olean tree:
- The 8 unchanged prefix modules, from the O1 prefix run above (`prefix-identity.txt`: base = O1 = final for each).
- The 1,325 other unchanged, non-downstream modules of `order.txt`, checked one at a time (`evidence/build/bootstrap/`, all rc=0).
  - Each record carries the source SHA-256 at check time.
  - `evidence/build/root/source-identity.txt` shows every one equal to the pack's `SOURCE-SHA256SUMS` (the base) and to the final head.
  - So these checks are checks of the final head's bytes.
- The 19 new and downstream modules at the final head (above).
- The root `TCSlib` last, at the final head (`evidence/build/root/summary.txt`, `mods/TCSlib.log`).

`evidence/build/root/closure-identity.txt` shows that the source hash recorded for each of these 20 is the final head's.

**Result: the root builds.**
- `TCSlib` at `ec36703b`: rc=0, 0 errors, 0 `sorry` warnings, 19 s, max RSS 4.29 GiB.
- All 1,353 modules: rc=0, 0 errors.
- `source-identity.txt`: `RESULT modules=1325 identical_to_base_and_final=1325 differing=0`.

**Interruptions, disclosed.** The bootstrap took several driver runs of `tools/sweep.py`. Each appended to `bootstrap/summary.txt` and skipped the modules already recorded (`bootstrap/skip-bootstrap*.txt`; driver logs `bootstrap-driver*.log`).
- One run was stopped by the 2-hour limit on background commands.
- One was cut by a container restart at about 23:11Z (`bootstrap/interrupted/README.txt`).
  - Its unfinished module log, `CookLevin/Hardness`, is kept in `bootstrap/interrupted/`.
  - That module was checked again from the start in the next run.
- Before the last run, the disk was down to 2.66 GB free. I deleted my own scratch reproduction clone (`/home/user/work/scratch-repro`, already used for `evidence/git/reproduce.txt`), which gave 7.8 GB.
- No module was recorded twice. The olean tree was never cleared, and every module ran against prerequisites already checked.

## 9. Admissions (check 4)

`evidence/build/root/admissions.txt` (`tools/admissions.py`) compares, per module, the `declaration uses 'sorry'` warnings of the root build with `base-sorries.txt` (229 declarations in 52 modules) and with the new targets.

`RESULT modules_built=1353 base_admissions=229 (expected 229 in 52 modules) new_admissions=100 (expected 100 in 11 modules) mismatches=0`.
- Every one of the 52 base modules has exactly its `base-sorries.txt` count.
- The 11 new modules with targets have exactly their target counts: Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, Combinators 26, CarrySave 7, Compare 7, ModSum 4, NANDForm 6, NANDLayering 7.
- No other module has a `sorry` warning. In particular, TreeNCAC, NCAC, Parity, Hierarchy, the facades and the registries have none.

## 10. Axioms and dependency trace (check 5)

`evidence/stmt/AxiomProbe.lean` and `.log` cover **548 constants** of the 13 new modules and TreeNCAC, declarations and auxiliary constants alike. The facades and registries define nothing.

- **Standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`, or none) for every constant except the 105 below.
- **`sorryAx` appears in exactly 105 declarations, and in no auxiliary constant:**
  - the **100 targets**;
  - `DAGCircuit.toNANDForm` and `toNANDForm_eq`, through **N2** `nandGadget_correct`;
  - `DAGCircuit.layerNAND`, `layerNAND_gates` and `layerNAND_output`, through **N12** `layerGates_acyclic` and **N13** `layerOutput_lt`.
- **Dependency trace.** Every `TRACE` line names, for each constant reaching `sorryAx`, the constants of the modules in its closure whose own value or type mentions `sorryAx`. Lines like `TRACE BoolCircuit.DAGCircuit.layerNAND via [layerGates_acyclic, layerOutput_lt]` confirm the two routes above.
- **O1's constants:** 141 in `Combinators`, `FormulaArith` and `TreeNCAC` at the O1 head, all standard axioms only (`evidence/o1/AxiomProbe.log`).

## 11. Rule 10 (check 6)

**Seals.** These are whole-file seals A and B, strict and coe.
- They use the GSW statement phase's tools (`evidence/tools/xr/`) with paths adapted, plus `runner_lock.py`. That is `runner_full.py` with the host lock: `lean -DmaxErrors=0`, no `-o`.
- The seals cover every new and changed Lean file over its full TCSlib import closure.
- The collector's elaborated-term rows of every owner are inside the requests or recorded as notation, abbreviation or reducible.
- coe-A is canonical. The coe exclusion (`FinDist`'s `CoeFun`) is in no closure here except the root's, so for the 16 files coe and strict coincide. For the root, coe-A and coe-B have exactly one request fewer than A and B: `TCSlib.InformationTheory.FinDist.instCoeFunForallReal` (diff of the runs' component lines).

**Results** (`evidence/rule10/final/seal-{A,B,coeA,coeB}.tsv`; columns: probe, requests, rc, errors, install record, EOF record, failing declarations):

| File sealed | Requests (A) | A | B | coe-A | coe-B |
|---|---|---|---|---|---|
| `BranchingPrograms/Defs` | 0 | pass | pass | pass | pass |
| `BranchingPrograms/Eval` | 25 | pass | pass | pass | pass |
| `BranchingPrograms/Barrington` | 119 | pass | pass | pass | pass |
| `BranchingPrograms/BarringtonConverse` | 244 | pass | pass | pass | pass |
| `BranchingPrograms/NC1` | 334 | pass | pass | pass | pass |
| `BranchingPrograms` (facade) | 336 | pass | pass | pass | pass |
| `FormulaArith/Combinators` | 174 | pass | pass | pass | pass |
| `FormulaArith/CarrySave` | 254 | pass | pass | pass | pass |
| `FormulaArith/Compare` | 270 | pass | pass | pass | pass |
| `FormulaArith/ModSum` | 274 | pass | pass | pass | pass |
| `FormulaArith` (facade) | 277 | pass | pass | pass | pass |
| `NANDForm` | 180 | pass | pass | pass | pass |
| `NANDLayering` | 187 | pass | pass | pass | pass |
| `TreeNCAC` | 219 | 2 failures | 2 failures | 2 failures | 2 failures |
| `CircuitComplexity` (facade) | 3,727 | pass, chunked | pass, chunked | pass, chunked | pass, chunked |
| `ComputationalModels` | 1,107 (B: 1,108) | pass | pass | pass | pass |
| `TCSlib` (root) | 13,762 (B 13,763; coe-A 13,761; coe-B 13,762) | pass, chunked | pass, chunked | pass, chunked | pass, chunked |

- `Defs` has 0 requests because it imports no TCSlib file. Its seal is still run, and it checks that the file elaborates under the harness.
- **Chunked seals (disclosed).** The unchunked `CircuitComplexity` facade probe stops with rc −6 (a stack overflow in one 3,727-row `attribute [local irreducible]` command) in all four variants (`seal-*.tsv`, row `…_CircuitComplexity`).
  - So `mkseals_ab.py`/`mkseals_coe.py` gained `SEAL_CHUNK`, which splits the same rows into several complete commands of at most 1,000 rows each. The set of sealed constants is unchanged.
  - The chunked facade seal passes in all four variants (`seal-chunked-*.tsv`).
  - The root `TCSlib` was sealed the same way, in its own directory `rule10/final-root/`, with `SEAL_CHUNK=1000`.
  - For a dotless module name, the probe label uses `Root` (a one-line change in both scripts; `tools/xr/`). The first root attempt failed on that label before any probe ran; its logs are kept as `final-root/*-label-error.log`.
  - The root rerun reused that attempt's collector output (`SKIP_COLLECT=1` in `seal_pipeline.sh`).
  - **Root seal results** (`rule10/final-root/seal-*.tsv`, `run-*/`): 14 chunks per variant, every chunk `G06-SEAL-END … requested = verified`.
    - A: rc 0, 0 errors, 64 min.
    - B: rc 0, 0 errors, 49 min.
    - coe-A: rc 0, 0 errors, 45 min.
    - coe-B: rc 0, 0 errors, 47 min.
    - Max RSS about 4.8 GiB each.
  - **A second container restart** stopped the root seal during variant B, after A had finished. B, coe-A and coe-B were run again from scratch (`VARIANTS='B coeA coeB'`). The interrupted run is kept in `final-root/interrupted/`.

- **TreeNCAC's two failures** are `maxDepth_map_le` and `maxFaninL_map_le`.
  - They are untouched private lemmas whose `| [], _ => Nat.zero_le _` reads `maxDepth []` and `maxFaninL []` by definition.
  - Both are byte-identical to the base (frozen check). They are pre-existing, outside O1's named repairs, and recorded for clean-up part 2.
- **Explicit-unfold scan** (`rule10/final/explicit-unfold-scan.txt`, `tools/scan_unfold.py`) covers `simp`/`rw`/`dsimp`/`unfold`/`delta` arguments resolved against every TCSlib definition.
  - All 13 new files: **0 foreign unfolds**.
  - `TreeNCAC.lean`: 4 pre-existing, at `:188` (`eval_node_map`, the line-366 read the brief keeps) and `:228`/`:250`/`:268`. Those three are the `hlit` cases `simp [TreeCircuit.toBinary, TreeCircuit.maxFanin/size/depth]` of `toBinary_maxFanin_le`, `toBinary_size_succ_le` and `toBinary_depth_le`; O1 changed those proofs only by the rename.
- **Paired controls on every new owner that defines something** (`rule10/controls/summary.txt`: 30 runs, all as expected).
  - Each owner has three runs: the unsealed body read passes; the sealed body read fails with exactly 1 error; the sealed reader passes.

| Owner | Definition | Reader |
|---|---|---|
| Defs | `yield` | `yield_eq` |
| Eval | `evalWith` | `evalWith_eq` |
| Barrington | `sigma1` | `sigma1_eq` |
| BarringtonConverse | `topDepth` | `topDepth_eq` |
| NANDForm | `DAGGate.IsNAND` | `isNAND_iff` |
| NANDLayering | `litInput` | `litInput_eq` |
| Combinators | `balanced` | `balanced_nil` |
| CarrySave | `val` | `val_eq` |
| Compare | `bitAt` | `bitAt_eq` |
| ModSum | `modSumDepth` | `modSumDepth_eq` |

  - `NC1.lean` defines nothing, so it gets no pair; nor do the two facades.
- **Reader census:** `evidence/rule10/reader-census.md`.
  - **MISSING**, with proposals:
    - `GadgetCorrect` → `gadgetCorrect_iff`. This one was **expected** (r3 §H2).
    - `GatesAcyclic` → `gatesAcyclic_iff`.
    - `TreeCircuit.depth`/`maxFanin`/`size` on literals → `depth_lit`, `maxFanin_lit`, `size_lit`.
    - `Lit.eval` → `Lit.eval_eq`.
    - `carryBit` → `carryBit_zero`, `carryBit_succ`.
    - `DAGCircuit.IsWellFormed` → `isWellFormed_iff`.
    - `Language.InTreeNC` → `inTreeNC_iff`.
    - `TreeCircuitFamily.HasFaninTwo`, `IsPolySize`, `HasPolylogDepth` → their `_iff` readers.
  - All the missing readers are in frozen files and are not added here (Q3).

## 12. Probes (check 7)

The probes are under `evidence/probes/`, outside the library. They were rerun against the final tree (`evidence/probes-final/summary.txt`).
- Kernel `decide`/`rfl` only, never `native_decide`.
- Where the kernel cannot reduce (well-founded `barrington`, `compTree`, `TreeCircuit.eval`, `Nat.clog`), `#eval` output is recorded as evidence.

| Probe | Checks | Result |
|---|---|---|
| **P1** yield order | Bar89 p004-b001 in BV14 order yields `formPerm [0,2,1,4,3]` exactly on `x₁ = x₂ = 1`, `id` elsewhere; the accepted yield is `sigma2⁻¹*sigma1⁻¹*sigma2*sigma1`. The width-2 example of p001-b002 (0-based variables 6, 3, 7) yields the transposition exactly when `x₇ ⊕ ¬x₄ ⊕ x₈`, on all 256 inputs. `yield_append`'s direction holds and the reverse fails. | pass (kernel) |
| **P2** commutator | `= formPerm [0,2,1,4,3]` (Bar89's (13254)); the right-to-left reading `formPerm [0,3,2,4,1]` (14352) differs; `IsFiveCycle` of `sigma1`, `sigma2` and the commutator. | pass (kernel) |
| **P3, P3b** conjugator | Computable (`#eval`). The 24 explicit five-cycles are all of them (kernel). C10 `θσθ⁻¹ = τ` on all 24×24 pairs by kernel `decide +kernel` in 46 s (P3b). | pass |
| **P4** Lemma 2 | `complementLast`: yield `σ⁻¹ ∘ B(x)`, `id` on `A`, `σ⁻¹` off it; length unchanged. | pass (kernel) |
| **P5a–c** Theorem 1 | On `x₀ ∧ x₁`, `x₀ ∨ ¬x₁`, both constants, a fan-in-1 node, two depth-2 XORs and a depth-4 formula, for all 24 output five-cycles and every input: recognition with output σ (C13), the `σ 0` reading (C16), `0 < length ≤ 4^depth` (C14), bijective maps (C15). Lengths 4, 4, 1, 1, 1, 16, 16, 40. A transposition output fails (why C13 needs `IsFiveCycle`). | pass (`#eval`) |
| **P6** host | C8 on a width-3 non-permutation program (a constant map collects mass 3); C6's pull form on `Instr.ofPerm 0 sigma1 sigma2`. | pass (kernel) |
| **P7** Theorem 2 | `compTree` wires equal `decide (yield x i = j)` on all inputs of P1's XOR program. `toFormula` is `noncomputable`, so a probe-local copy of its body taking the accepting set as a list was checked against `decide (yield ∈ F)` for four sets. Depth bounds C19, C21 swept. | pass (`#eval`) |
| **P8** NAND gadget | Every row of r3 §H3.9 (∧, ∨, ¬ with 0, 1, 2 and repeated arguments), with an empty prefix and with a one-gate prefix: extends, acyclic, vertex in range, value equal to the old gate on every input, ≤ 2 levels, ≤ fan-in + 2 gates, only NAND gates. Gate counts and depths per row equal the table. | pass (kernel) |
| **P9** layering | `layerNAND` on XOR in NAND form, on a circuit with an odd gap of 3, and on one with a fan-in-0 gate. The layered circuit is rebuilt with its fields proved by `decide`, so N12–N13 hold on these instances. Checks: `eval (litInput x) = C.eval x` on every input, `IsLayered`, `IsNANDForm`, depth equal, size within N11. The same checks run on `C.layerNAND`. The XOR truth table records the odd-gap finding. | pass (kernel) |
| **P10a, P10b1–b5, P10c1–c7** formula arithmetic | `xor3`/`maj3` truth tables; `csaStep_val` (3,375 triples); `carryOut` against `carryBit` (1,350); `geConst` (4,500); `modSumInterval_eval` exhaustively for `q` 2–7 with `M ≤ 2`, and `M = 3` with `q ≤ 7`, all `a`, all `lo ≤ hi ≤ q`, all inputs; the closed forms of F6 and F10 on ranges. | pass (`#eval`, 0 failures; `csaLevels` by kernel `decide`) |
| **T0_Env** | fa's environment probe. It shows **by its expected errors** that the kernel cannot reduce `TreeCircuit.eval`/`depth` or `Nat.clog`, the reason P10 uses `#eval`. | expected errors (4) |

- **One `#eval` row was dropped in the final rerun of P10b5.** The `(M, q) = (12, 61)` depth row took 8 minutes and 13.6 GB of the shared lock. Its result (depth 39 against the bound 42) is the sub-agent's recorded run (`subagents/fa/P10b5.log`). The edit is marked in the probe.
- **P0** (bp): every definition and reader of BranchingPrograms uses standard axioms only.

## 13. Frozen-file check (check 8)

`evidence/headers/` holds the runs of `tools/frozen_check.py`. It extracts every declaration, private ones included, of each changed existing Lean file at base and head, and compares header and whole text byte for byte.
- **Final head**, over `TreeNCAC.lean`, `CircuitComplexity.lean`, `ComputationalModels.lean`, `TCSlib.lean`: `violations=0`.
  - O1's 16 documented removals (the moved block).
  - Five documented body-only changes: `toBinary` and the four `toBinary_*` proofs. Their headers are identical.
  - The three registries have no declarations.
- **O1 head:** the same result.
- **Controls:**
  - One character of `clog_poly_le`'s statement altered (`≤`→`<`): exactly 1 violation (HEADER).
  - The reader `TreeCircuitFamily.mem_language_iff` deleted: exactly 1 violation (REMOVED).
- **No other frozen file changed.** The `git diff --stat f6f295a6 ec36703b` lists 17 Lean files and `machine-library-design.md`, nothing else (`evidence/git/diffstat.txt`).
  - Nothing under `Cryptography/` or `blueprint/`.
  - `DAGCircuit.lean`, `DAGTransform.lean`, `DAGFanin.lean`, `TreeDAG.lean`, `Basic.lean`, `NCAC.lean`, `Adder.lean`, `Parity.lean` unchanged.

## 14. Lint and sizes (checks 9–10)

**`style_lint.py`** on the 17 new and changed Lean files (`evidence/lint/style_lint-final.txt`):
- **0 findings in the new files.**
- 11 findings, all in `ComputationalModels.lean` (5) and `TCSlib.lean` (6): missing `set_option` lines and docstring sections.
- They are **identical at the base** (`style_lint-base-registries.txt`) and pre-existing in the two shared registries. Changing those headers is outside this job's registrations.

**`campaign_style_lint.py TCSlib/Complexity --check8b`:**

| Head | FAIL | WARN | Files |
|---|---|---|---|
| Base | 25 | 390 | 500 (the maintainer's baseline) |
| O1 | 25 | 390 | 502 |
| Final | 25 | 390 | 513 |

- The FAIL/WARN line sets of base and final are **equal** (`campaign-diff-base-final.txt` is empty), so there is no new FAIL and no new WARN.
- The one check-8 WARN seen during integration (`BranchingProgramFamily.language`) was removed by adding the reader `language_eq`.
- `TCSlib/Complexity/CircuitComplexity` alone: 0 FAIL / 79 WARN over 111 files (base: 0 / 79 over 104).

**Sizes** (`evidence/sizes/sizes.txt`; Python `len`):
- Every new file has max width ≤ 100.
- Lines at the final head, with r3 §H7's expected filled size in brackets:

| File | Lines | r3 §H7 expected (filled) |
|---|---|---|
| Defs | 412 | 120–180 fill |
| Eval | 172 | 150–230 |
| Barrington | 463 | 550–720 filled |
| BarringtonConverse | 304 | 250–400 |
| NC1 | 135 | 180–320 |
| NANDForm | 284 | 300–450 filled |
| NANDLayering | 388 | 300–450 filled |
| Combinators | 659 | 150–220 F1–F3 fill, plus O1's 246 |
| CarrySave | 297 | 250–400 |
| Compare | 238 | 150–250 |
| ModSum | 196 | 150–250 |
| facades | 39, 31 | — |

- Every file is under 1,000 lines.
- `Combinators.lean` (659) is above the 600-line target, because it holds O1's moved block plus nine gadgets with 26 targets. A filled split (gadgets into their own child) is a natural follow-up if the fills grow it.
- Lines over 100 in changed existing files are all pre-existing:
  - `TreeNCAC.lean` lines 62 and 165 (base 61, 164);
  - `CircuitComplexity.lean` line 284 (base 272);
  - `ComputationalModels.lean` line 164 (the `[AFM26]` reference).

## 15. Name clashes (check 11) and overlap and reuse (check 12)

**Clash scan** (`evidence/clash/final.txt`, `tools/clash_scan.py`):
- 290 new names, public and private, with namespaces resolved.
- 11 are O1's moved privates, re-declared in `Combinators` after their removal from `TreeNCAC` by the same change.
- **0 clashes** with any declaration of `TCSlib/` at the base. No `NAnd`, no `toLayered`.

### Overlap and reuse

The searches were the clash scan, `git grep` at the base for every r3 §H2 item, and the sub-agents' searches (their reports, §6). Confirmations of r3 §H2, with base `path:line`:

| Item | Base location | Relation | Disposition |
|---|---|---|---|
| `NAndCircuit` / `TreeCircuit.toNAnd` | `Basic.lean:356/465` | AND-rooted alternating normal form, not NAND | **Name clash avoided** (`IsNAND`, `IsNANDForm`, `toNANDForm`); cross-referenced in docstrings |
| `DAGCircuit.toLayered` / `TreeCircuit.toLayered` | `LayeredDAG.lean:208/623`, into `LayeredCircuit` (`LayeredCircuit.lean:54`) | Another model, one vertex per layer, needs `IsWellFormed` and no `∨` | **Not reused**; name `layerNAND` |
| `combine` | private, `TreeNCAC.lean:252` | — | **Promoted by O1** (`balanced`), moved, no copy left |
| `toBinary` | `TreeNCAC.lean:353`, `toBinary_depth_le` :442 | Rebuilds every child; multiplicative depth | Not a replacement for `balanced`; re-pointed to it |
| `xorNode` / `IsDual` | private, `Parity.lean:60/65` | — | **Not copied**; re-pointed to `neg`/`xor2` later (P6-Q6, dedup queue) |
| `Complexity.BinArith.carry` / `sumBit` | `ClassP/BinaryArith/AddSub.lean:49/52`, `serial_add` :62 | Same Boolean functions as `maj3`/`xor3` | **Not imported** (it would pull polynomial-time machinery into the formula layer); `maj3_eval`/`xor3_eval` state them with `Bool` operations |
| `FormulaKit/Gate.lean` `template` / `gate` | `:90/:142` | Truth-table CNF over `Std.Sat.CNF ℕ` | Different model; excluded by r3 §H3.3 |
| `dnfDAG` | `BookModelBasics.lean:406` | Truth-table DAG | Excluded (§H3.3) |
| `stdGateOps` | `LayeredCircuit.lean:115` | Basis `{id, ¬, ∧}`, no NAND | Not reused |
| `SLOp` | `StraightLine.lean:87` | Basis `{∧, ∨}` | Not reused |
| `unfoldGate` | `TreeDAG.lean:388` | Pushes negations by De Morgan on **DAG** input | Not a tree-to-tree `neg`; not reused |
| `StraightLine.dualRail` | `StraightLineDualRail.lean:122` | Straight-line programs with both rails; another model | Not reused; `litInput` is one line |
| `bitsVal` / `prefixVal` / `carryBit` | `Adder.lean:78/82/377`; `bitsVal_eq_prefixVal` :136, `prefixVal_add` :397 | — | **Reused as the semantics** of F5–F9 (`val`, `carryOut_eval`) |
| `fullAdderGates` / `adderGates` | `Adder.lean` | Linear-depth DAG adders | Not used (§H3.3) |
| `GadgetCorrect` | `DAGTransform.lean:68` | No `_iff` reader | Census MISSING, expected (N2 is admitted and does not unfold it) |

**New material that restates existing material: none.**
- Every new definition is new to the library.
- The readers state only their own files' definitions.
- No public lemma was copied. O1 moves code and leaves no duplicate (frozen check: the 16 declarations are removed from `TreeNCAC.lean`).
- The `deMorganGadget` pattern (`DAGFanin.lean:475`) is followed in style by `nandGadget`, not copied.

## 16. Scope requests and questions for Seyoon

**Scope requests:** none. No frozen file was changed.

**Questions** (none blocks the delivery; each has a default already applied):
- **Q1 (O1, two extra Rule 10 repairs).** The whole-file seal of the new owner exposed two definitional reads in the moved proofs, beyond the three the brief names: `le_refl 0` and `Nat.zero_le _` on `sumSize []` and `maxFaninL []`.
  - **Applied:** both now read through `sumSize_nil`/`maxFaninL_nil`, so `Combinators.lean` passes all four seals.
  - **Alternative:** keep the three-repair byte form and record a seal exception for the two lines.
- **Q2 (N12's form).** N12 is stated in the field's form because `GatesAcyclic` has no reader.
  - **Alternative:** approve an owner-side `gatesAcyclic_iff` (`Iff.rfl`, `DAGCircuit.lean`); N12 then takes r3's form `GatesAcyclic (n + n) C.layerGates` and `layerNAND` fills its field through the reader.
- **Q3 (missing readers).** Approve the owner-side readers of the census (§11) before the fills that need them:
  - `gadgetCorrect_iff` for N2 (expected);
  - `depth_lit`/`maxFanin_lit`/`size_lit` and `Lit.eval_eq` for F1–F3, C13, C17;
  - `carryBit_zero`/`_succ` for F7;
  - `isWellFormed_iff` for C22;
  - `inTreeNC_iff` and the `TreeCircuitFamily` `_iff` readers for C23–C24.
- **Q4 (`c[…]`).** `sigma1`/`sigma2` are written with `List.formPerm`, because `Mathlib.GroupTheory.Perm.Cycle.Concrete` is outside the fetched closure.
  - The meaning is the same. Switching to the `c[…]` notation needs one more narrowed cache fetch.
- **Q5 (F9's `lo ≤ hi`).** P10 finds `hlh : lo ≤ hi` unnecessary on every tested instance. It is kept, as r3 states it. Drop it at the fill if the proof does not need it.

## 17. Evidence

- `evidence/SHA256SUMS` lists every evidence file.
- The top-level `SHA256SUMS` lists every delivered file except itself.
- The delivered paths equal the manifests' paths: nothing missing, nothing extra, no leading `./`. Checked before the push.

| Path | Contents |
|---|---|
| `logs/` | preflight, toolchain, cache store and fetch, roots, package check |
| `build/` | `order-final.txt`; `downstream.txt`; `o1/` (prefix bootstrap and O1 closure); `pfr/` (PFR modules); `bootstrap/` (the 1,325 unchanged modules, one log each, skip lists, the interrupted log); `final-closure/`; `root/` (the root's summary and log, `summary-all.tsv`, source, prefix and closure identity, admissions) |
| `o1/` | byte comparison, frozen check and controls, seals (four variants) with controls, axioms, statement dump, decls2, clash, sizes, reproduction |
| `stmt/` | decls2, statement dump, axiom probe with trace, row map, definitions and readers, per-module targets, quotation check |
| `rule10/` | `final/` (seals of the 16 files, four variants: collector, seal sources, runs, summaries; chunked facade seals; explicit-unfold scan), `final-root/` (the root's chunked seals), `controls/`, reader census |
| `probes/`, `probes-final/` | probe sources and the final run's logs |
| `headers/` | frozen-file check and controls |
| `lint/` | both lints, base/O1/final |
| `sizes/`, `clash/` | sizes; clash scan |
| `git/` | series hashes, diffstat, reproduction |
| `subagents/{bp,fa}/` | the sub-agents' reports, logs, probe copies and tools |
| `tools/` | every tool used, including the adapted GSW statement-phase seal tools (`tools/xr/`) |
