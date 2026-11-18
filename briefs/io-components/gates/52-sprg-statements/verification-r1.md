# Gate 52 · io-sprg checkpoint 0 · in-house Lean verification r1

**Verdict: PASS.** The maintainer replay that G52-11 asked for is complete. The source rebuilds
byte for byte from the base and the delivered patches. The changed modules and their downstream
elaborate on the base with rc 0, 0 errors and exactly the 146 expected `sorry` warnings. The
state check passes over the full order (1480) and the 127-module closure. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`, plus `sorryAx` on the stated obligations. The
census matches the worker's self-report in every count. Every headline `#check` elaborates.
The probes confirm G52-03 and G52-04 as **literal** duplicates: `rfl` closes each of them.

Run on 2026-11-18, 22:01–22:19 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work
directory is `$SP/io-c0/`.
- **Evidence:** `verification-r1.zip`, beside this file. Its SHA-256 is in
  `verification-SHA256SUMS`, and it holds an inner `SHA256SUMS`.
- **Constraints observed:**
  - no `lake build`, no cache get;
  - one Lean process at a time, with 0 other `lean` processes on the host at every start
    (`slots.log`);
  - Lean ran only through the recipe tools (`runner.py`, `runner_full.py`), on `cp -al` copies;
  - nothing was written into `$SP/olean-snapshot`, `$SP/olean-snapshot-10` or any existing
    `$SP/olean-replay-*` tree;
  - nothing was committed, pushed or branched in the repository. The scratch git work used a
    private bare repository, `$SP/io-c0/git.git`, with the records objects as alternates.

## Expectations against results

| # | Check | Expected | Result |
|---|---|---|---|
| 1a | Bundle | verifies on base `5ed465f6`; head `d10a560b` | `git bundle verify` OK; requires `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`; ref `fill/io-sprg` = `d10a560b34d58919bc1a5206ce66a444613f94c7`; 15 commits, all unsigned (`%G?` = N) |
| 1b | Delivered patches, base + patches | tree of `d10a560b` | 16 files verify against the delivery's `SHA256SUMS`. 0001–0014, applied with `git apply --cached` on `5ed465f6`, give tree **`626078106e494cfc64971d77e0870e09ec9780cb`**. This equals the tree of `d10a560b` and of `d286bafc`; 0015 is the empty marker commit |
| 1c | Patch regeneration | byte-identical | `git format-patch --full-index --no-signature 5ed465f6..d10a560b`: **15/15 identical** to the delivered patches |
| 1d | `src/` vs tree | byte for byte | **23/23** `src/` blobs equal the blobs at `d10a560b`; path sets equal |
| 1e | Changed paths | 22 new modules + `TCSlib.lean` | `git diff --name-status 5ed465f6 d10a560b`: **22 A + 1 M (`TCSlib.lean`)**, nothing else |
| 1f | Static census | 146 `sorry`, 5,911 lines | **146** `sorry` tokens (146 outside comments), **5,911** lines over the 22 new files. The gate's `source-head.json` `src_files`: **23/23** SHA-256 match the export and the runner's records |
| 2a | Closure | 127 modules = delivered `evidence/logs/order.txt` | `downorder.py` `order-noroot`: **127**, byte-identical to the delivered `order.txt` (SHA-256 `00efd6fb…`) |
| 2b | Build | every module rc 0, 0 errors | **42/42 rc 0**; `error:` 0, `error(` 0, substring "error" 0; `permod.py` 0 log/record mismatches |
| 2c | `sorry` warnings | 146 (direct) | **146**, all in the 22 new modules; **per file equal** to the static token counts. The new modules have **no other warning** (warnings = 146) |
| 2d | State check | RESULT OK | `stateplan update` 42/42 taken; `check` **1480/1480 OK** (full order: root and both `Checks`) and **127/127 OK** (closure) |
| 2e | Link counts | rebuilt oleans have 1 link | **42/42 link count 1**; exactly 42 non-Mathlib files with link count 1; tree has 1523 files (1501 + 22) and 3346 symlinks |
| 2f | Source trees | rehash 0/0/0 before and after | Snapshot #11: **0/0/0** before. EF-D1 tree: state check 1469/1469 OK before and after; rehash **0/0/0** after. The end-of-run figures are in *State after the run* |
| 3 | Axioms | only the three standard axioms, plus `sorryAx` on obligations | **0 non-standard** over all 1036 stored constants. Headlines: 20 via `sorryAx`; `PrimeSchedule.nonempty` standard-only. The control is flagged |
| 3' | Worker self-report | 1036 constants; 511 public theorems; 146 direct holes; 265 `sorryAx` dependents; 0 other | **1036; 511; 146; 265; 0**, all equal |
| 4 | Headline `#check`s | elaborate | `Heads`: rc 0, 0 errors; the only warning is the control's `sorry` |
| 5 | Duplication probes | G52-03, G52-04 | G52-03: both inverses **are** `PadQuad.nu` by `rfl`, and the four readers are one-term consequences of the public `PadQuad` API. G52-04: all five LPN-side equivalences **are** the `ConstructionEncoding` ones by `rfl` |

## 1. Source reconstruction

- **Inputs.**
  - The delivery commit is `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d` on `exchange/pass-shelat-ch5-8`, at `inbox/fills/io-sprg/`.
  - The bundle SHA-256 is `118b8213…97fc`, equal to its `SHA256SUMS` line.
  - `REPORT.md` SHA-256 is `af2c15b6…7c1`, equal to its `SHA256SUMS` line.
- **The bundle** was fetched only into the scratch bare repository (ref `refs/c0/sprg-bundle`),
  never into `/home/user/tcslib`.
- **Patch application.** The delivered patches were applied to a private index
  (`GIT_INDEX_FILE`) read from `5ed465f6`, and `git write-tree` gave `62607810…`. No worktree
  and no commit were made.

## 2. Replay (snapshots.md job recipe, on the EF-D1 kept tree)

**Start tree.**
- `$SP/olean-replay-efd1` was chosen because it is EF-D1's accepted tree on `iO/phase-a-base`.
  It holds oleans for the merge of `5ed465f6` with `bff0567b`, plus EF-D1's three modules.
- Before use, `stateplan check` with EF-D1's `state.json` (`02a21ac1…`) at its check head
  `e3fc2ce29436efeb3870f883f8a8e40cb9292c0f` gave **1469/1469, RESULT OK**.
- A rehash baseline of the tree was then recorded: 4847 entries (1501 files and 3346 Mathlib
  symlinks), map `efa200d3…0475`. `tools/treehash.py` was used because `snapmap.py` refuses
  symlinks.
- Snapshot #11 (`snapmap.py verify` against `e7bb03b4…`) gave **0/0/0**, 1487 files.

**Copy.**
- `cp -al $SP/olean-replay-efd1 $SP/olean-replay-ioc0-sprg`: 1501 files and 3346 symlinks,
  0 files with link count 1.
- The tree already carries the `NthRootLemmas` overlay (`c0a9cff0…`). It was inherited, not
  rebuilt.

**Export.**
- `git archive` of `d10a560b` (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, `lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`): 1632 files.
- `.lake/packages` is symlinked to the repository's packages. Mathlib is at
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` and the toolchain is `v4.25.0`.
- The manifest is equal to the repository's.

**Plan.**
- `downorder.py`: 23 changed, 23 down, order 1478, `order-noroot` 127.
- `fullorder.py`: 1480, with roots `TCSlib` and both `audits/*/Checks`.
- `stateplan plan` against EF-D1's state: **42 to build, 1438 reused.** The 42 are:
  - the 22 new modules;
  - root `TCSlib`;
  - 19 base-delta modules whose closure key at `5ed465f6` differs from the merge tree:
    `LWE/BitEncoding`, `LWE`, `SIS`, the 9 `Encryption/{Symmetric,PublicKey}/Regev` and facade
    modules, the 5 `GSW` modules, `Homomorphic` and `AdvancedEncryption`.
- Of the 127 closure modules, **22 were built and 105 reused** under identical closure keys. The
  105 are base modules whose oleans descend from the snapshot lineage. They were not
  re-elaborated.
- None of the base-delta modules is in the 127 closure. They were rebuilt only so that root
  `TCSlib` checks at the base state.

**Build.** `runner.py`, 22:05:23–22:12:19.
- **42/42 rc 0**, with errors 0 in both forms.
- Peak maxrss 4.56 GB, for root `TCSlib`.
- The 20 base modules give 0 `sorry`. They give 3 warnings that are already present at the
  base: `Regev/Basic` 1 and `Regev/Experiments` 2. These are the simp-lemma `_def` linter and an
  unused section variable, in files this delivery does not touch.

**Accept.** As in the table, rows 2b–2e.

## 3. Axioms

Every probe ran through `runner_full.py`: `lean -DmaxErrors=0`, no `-o`, so nothing was written
to the tree. The probe directory holds only the probe sources and `lean-toolchain`.
- **Attempt 1** had no `lean-toolchain` in the probe directory. Elan reported "no default
  toolchain" and no Lean ran (`probe-logs-attempt1/`).
- **Attempt 2** is the run reported here.

**`Heads.lean`** (rc 0). It holds 21 `#print axioms`: the REPORT's 19 headline prints, plus
`lemma42` and `Params.G4_degrees`, and a `sorry` control.
- 20 are `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PrimeSchedule.nonempty` is `[propext, Classical.choice, Quot.sound]`.
- `ioc0SorryControl` is `[sorryAx]`.
- The 19 shared prints **equal REPORT.md's "Headline axiom prints at M0"** line for line.

**`Census.lean`** (rc 0, 273 s): core `Lean.collectAxioms` on every constant whose module is one
of the 22.

| Population | Constants | Standard-only | Via `sorryAx` | Other axiom |
|---|---:|---:|---:|---:|
| All stored constants | **1036** | 771 | **265** | **0** |
| Public (non-private, non-internal, non-auxiliary) | 881 | 635 | 246 | 0 |
| — with a source declaration range | 801 | 555 | 246 | 0 |
| — public theorems | **511** | 298 | 213 | 0 |
| — public definitions, structures, constructors | 370 | 337 | 33 | 0 |

- **Direct holes.** 146 constants mention `sorryAx` in their own value. All 146 are public
  theorems, one per `sorry` token.
- **Transitive-only dependents.** There are 119: 86 theorems and 33 definitions. The 33
  definitions are stored-field assemblies such as `jlsSPRG_raw` and `lpnFamily_raw`, which carry
  named admitted proof fields. Intake F14 expects this.
- **Kinds:** 433 def, 561 thm, 16 ctor, 13 induct, 13 rec.
- **Against the worker.** The REPORT's "1036 stored constants … 511 public theorem prints … 146
  direct holes and 265 transitive sorry dependents … zero nonstandard axioms" is **reproduced
  exactly**: 265 is all `sorryAx` dependents, the direct 146 included. Its "948 public full
  kernel-expression types" uses a different public filter. This census's widest public count
  is 881.

**`Census2.lean`** (35 s) is a memoized collector with the same edges as `CollectAxioms.collect`.
Its 1036-row table is **byte-identical** to `Census`'s, and it was then used for Gate 51.

## 4. Headline `#check`s (`Heads.lean`, rc 0, 0 errors)

All of the following elaborate as stated:
- **Def 3.1/3.2:** `SPRG.Raw`, `SPRG`, `SPRG.Raw.game`, `Secure`, `SubexpSecure`, and
  `#print SPRG.Raw.HasPolyStretch`. The last is ∃ τ > 1, ∃ κ₀, ∀ κ ≥ κ₀, κ ≤ seedBits κ ∧
  seedBits κ ^ τ ≤ outLen κ.
- **Def 3.3:** `#print` of `SPRG.Raw.HasComplexity`, `HasComplexityEff` and the `SPRG` wrappers,
  and `HasComplexityEff.hasComplexity`.
  - `HasComplexity` is ∀ κ I, ∃ Q, the per-output public/private degree bounds, ∧ `AllOutputs`
    of `sdSamp κ I` with `eval` = `MvPolynomial.eval (Sum.elim pub priv) (Q j)`.
  - `HasComplexityEff` adds one `PolyTimeComputable f` before κ, I. It outputs `encTerms` of `Q j`
    from `pairEncode (encPP κ) (pairEncode (encIdx κ I) (encFin j))`.
- **Def 3.4 / 2.3:** `BoolPRG`, `BoolPRG.Secure`, `BoolPRG.MultilinearRep`,
  `LPNFamily.Raw.Assumption`, `lpnNoise_law`.
- **Claim 4.1:** `jls_hasPolyStretch` (under `1 < τ`, `G.HasStretch τ`, `E0 d δ τ ≤ E`).
- **Claim 4.2:** `Params.claim42`: ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp, `errProb κ pp ≤ 2⁻¹ ^ κ`, under
  `HasLocality`.
- **Lemma 4.2:** `lemma42`.
- **Prop 4.1:** `prop41`: ∃ ωL ωG, ∀ BL BG realisers, ∀ κ,
  `adv ≤ 2κ·LPNadv(ℓ κ) + Gadv(n κ) + 2·errProb`.
- **Theorem 4.1:**
  - `jls_hasComplexity`, `jls_secure`, `jls_subexpSmall`, `jls_subexpSecure`, `theorem41`,
    `theorem41_subexp`;
  - `exists_sprg_raw` and `exists_sprg_raw_subexp`, each concluding
    `∃ S, (∀ κ, S.modulus κ = (π κ).p) ∧ … ∧ S.HasComplexity d 2 ∧ S.HasPolyStretch`;
  - `theorem41_of_targets`, `exists_sprg_of_targets`, `exists_sprg_of_targets_subexp`, `jlsSPRG`
    and `#print Params.Targets`.

The full printed statements are in `logs/probes/Heads.log` in the zip.

## 5. Duplication probes (the items G52-11 lists)

**`Dup.lean`** (rc 1: its one error is the last `exact?`, which failed, as recorded below; every
other line passed).

| Item | Probe | Result |
|---|---|---|
| G52-03 | `P.kappaOf L = PadQuad.nu P.E L := rfl`; `P.kappaOfN N = PadQuad.nu (P.E * P.D) N := rfl` | **both pass**: the definitions are `PadQuad.nu` |
| G52-03 | `kappaOf_le`, `kappaOfN_le` as `PadQuad.nu_le _ _`; `kappaOf L ^ E ≤ L` as `nu_pow_le P.one_le_E L`; `κ ≤ kappaOf (ℓ κ)` as `le_nu P.one_le_E le_rfl`; `kappaOf_pow` as `le_antisymm (pow_le_pow_iff_left.mp (nu_pow_le …)) (le_nu …)` | **all pass**: four of the delivery's `sorry` readers are one-term consequences of the public API |
| G52-03 | `exact?` on the unfolded goal `Nat.findGreatest (fun κ => κ ^ E ≤ L) L ≤ L` | `exact Nat.findGreatest_le L` |
| G52-03 | `exact?` on the folded goals, in the module prefix just before each lemma (`Pfx_kappaOf_le`, `Pfx_kappaOfN_le`, `Pfx_kappaOf_pow`, `Pfx_kappaOfN_n`) | **could not close** in all four. `exact?` does not see through `kappaOf`/`kappaOfN`, so the overlap is invisible to search; the `rfl` probes above are the evidence |
| G52-04 | On `P.lpnFamily_raw π` at dimension L: `residueEquiv`, `vectorEquiv`, `matrixEquiv`, `noiseSeedEquiv`, `noiseVectorEquiv` = `ConstructionEncoding.{same}` at `π (P.kappaOf L)` (with `samples L`, `noiseDen L` as the extra arguments), each `:= rfl` | **all five pass**: the two families are the same terms at the shared modulus |
| G52-04 | `exact?` for a generic `(Fin n → Fin q) ≃ Fin (q ^ n)` | `exact finFunctionFinEquiv` |
| G52-04 | `exact?` for `[NeZero q] : (Fin n → ZMod q) ≃ Fin (q ^ n)` | **could not close**: no ready-made modulus-generic equivalence exists in the imported environment, so G52-04's "one shared owner" would be new glue, not a reuse |

The probe sources are in `probes/` in the zip and their SHA-256 in `logs/probe-src.sha256`.
`mkprefix.py` builds the `Pfx_*` files: a copy of the module up to the lemma, plus its
signature as an `example … := by exact?`.

## 6. State after the run

These are the final figures, recorded at the end of both checkpoints at 22:35Z. Gate 51 ran
second.

- **Kept:** `$SP/olean-replay-ioc0-sprg`: the accepted tree, 1523 files (42 own, 8.1 MB) and 3346
  symlinks. `stateplan check` gives 1480/1480 OK at the end.
  - Free disk after this checkpoint was 2,927 MB, above 2.5 GB, so the tree was kept while
    Gate 51 ran.
  - It is a hard-link copy, so deleting it frees only its 8.1 MB.
- **Source trees at the end:**
  - Snapshot #11 rehashes **0/0/0** (1487 files, map `e7bb03b4…`).
  - `$SP/olean-replay-efd1` rehashes **0/0/0** against the baseline taken before the copy, and
    its state check gives 1469/1469 OK.
- **Disk.** Free space was 3,023 MB at the start and 2,819 MB after both checkpoints.
- **Work directory.** `$SP/io-c0/sprg/` holds the export, plan, logs and probes;
  `$SP/io-c0/git.git` is the scratch repository.
- **Host slots.** There were 0 other `lean` processes at every start of this gate's runs.
- **Not touched:** `$SP/olean-snapshot-10`, and other agents' trees and processes.
