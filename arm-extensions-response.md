# Response: ARM extensions for chapters 3–4

*Reply to `arm-extensions-proposal.md` (Seyoon, chapters 3–4 campaign).
Branch `complexity/arm-extensions`, cut from `complexity/arora-barak-ch3-4` at `50678912`.
Status: built and independently verified; merged into `complexity/arora-barak-ch3-4`
(at `069cde82`) on 2026-10-14.*

## Summary

**All three extensions are accepted and implemented.** Each one also has a real consumer
filling a sorry from your campaign:

| Extension | Status | Concrete use |
|---|---|---|
| 1. Nondeterministic ARM | done | `PATH_mem_NL` (Path.lean), now proved |
| 2. Poly-width ARM | done | `searchLang_mem_PSPACE` (example); Savitch below |
| 3. Configuration codec | done | `PSPACE_eq_NPSPACE` (Savitch.lean), now proved |

After the first round, the remaining customers the proposal names were proved too (section
"The remaining customers" below):

| Theorem | [AB09] | Engine |
|---|---|---|
| `PATH_NLComplete` | Thm 4.18 | codec + deterministic ARM (implicitly logspace reduction) |
| `compl_PATH_mem_NL`, `NL_eq_coNL` | Thm 4.20 | nondeterministic ARM, inductive counting over codes |
| `NSPACE_compl_eq` | Cor 4.21 | same machine, window growing (needs only `logSpace ≤ S`) |
| `TQBF_mem_PSPACE` | Thm 4.13 | poly-width ARM, depth-first AND/OR walk |
| `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` | Thm 4.13 | codec + Cook–Levin tableau + Tseitin |
| `NSPACE_subset_exp_dtime` (hence `NL_subset_P`, `polyTimeReducible_of_mem_NL`) | Thm 4.2(iii) | new memory-tape ARM with a time bridge, BFS over codes |

Two ground rules held throughout:

- **No statement of yours changed.** Only bodies of your sorried theorems were filled, and
  their docstring sketches rewritten to match the proofs (with the `[AB09 …]` tags kept).
  One relocation: `NSPACE_subset_exp_dtime`, `NL_subset_P` and `polyTimeReducible_of_mem_NL`
  moved, byte-identical, from `ConfigGraph.lean` to the new `SpaceComplexity/ExpTime.lean`
  (the proof needs the codec, and `Codec/Word.lean` imports `ConfigGraph` — an import cycle
  otherwise). Nothing referenced their old module path.
- **One pre-existing file of mine changed.** In `Machines/Compile.lean` I added
  `compile_correct_from`. `compile_correct` is byte-identical and is now a corollary of it.

All `#print axioms` checks of the main theorems give `[propext, Classical.choice, Quot.sound]`.

On process: we went straight to filled proofs, not your sorried-statement → audit → fill
loop. Every package did go through an adversarial verifier (builds, axioms, honesty of
statements, policy, duplication). You are welcome to run your external audit over the
statements listed below before merging.

## 1. Nondeterministic ARM — accepted

You can choose between extending the current machine and building a sibling. I extended it.
The design avoids re-proving the simulation:

- **Instructions.** `NIns = det (Ins …) | choose ℓ₀ ℓ₁` and `NARM m d Λ := Λ → NIns m d Λ`
  (`Machines/NARM.lean`). They have abstract semantics `nastep`/`narun`, driven by a choice word.
- **Compilation.** `ncompileTM`/`ncompileFinNDTM` (`Machines/NARMCompile.lean`) go to a
  `FinNDTM`. For each choice bit β, the ND transition agrees with the *deterministic* compile
  of `detPart β` everywhere except at choose-start states. So every branch replays the
  existing deterministic `compile_correct_from` piece by piece.
- **Bridges** (`Machines/NARMRun.lean`, `Machines/NARMProof.lean`):
  - `narm_space`: all-branch halting, all-branch space, and acceptance ↔ some branch answers `true`.
  - `narm_decides` / `narm_decides_poly` give `L ∈ NL`.
  - `narm_decides_npspace` gives `L ∈ NPSPACE`.
  - These are the ND twins of `arm_decides*`, with the same hypothesis shapes.
  - Halting is stated as `NHalts` (every choice word of a uniform length halts) and
    acceptance as `NAns` (some word answers).
- **Ergonomics for loops** (`Machines/NARMKit.lean`):
  - an inductive termination/acceptance layer `NTerm`/`NAcc`/`NSem`;
  - `NSem.decides` turns it into the uniform-bound hypotheses;
  - per-instruction lemmas and loop lemmas (`nsem_guess`, `nsem_copy`, …).

**Example — `PATH ∈ NL`** (`Logspace/PathWalk*.lean`, filled in `Path.lean`).

- The machine is `pathA : NARM 9 2 PathLabel`.
- It parses `⟨1ⁿ, ⟨M, ⟨s, t⟩⟩⟩` by indexed input reads, through your `inputBitLang` and
  `inputLenLang`.
- It then walks: at most `n` steps, guessing each next vertex by a bounded `choose` loop and
  checking the matrix bit.
- Correctness uses walk shortening: `walkLe_short` and `reach_iff_walkLe` in `PathWalk.lean`.
- Registers stay below `4(|x|+1)`, so `narm_decides_poly` applies.
- `PATH_NLComplete` is now proved as well; see "The remaining customers".

## 2. Polynomial-width ARM — accepted, as a generalization

**No new compiler was needed.** `arm_space` was already width-parametric; only the
`arm_decides*` wrappers fixed `W = O(log n)`. `Machines/ARMWidth.lean` adds:

- `arm_decides_space` (general width `S` with `logSpace ≤ S`) and `arm_decides_SPACE`.
- `arm_decides_pspace`, with guard `∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ C₀ * (|x|+1)^c₀`
  and PSPACE deciders, giving `L ∈ PSPACE`.
- `arm_decides_pspace_of_logspace` (LOGSPACE deciders) and `arm_decides_pspace_val`
  (value bound `≤ 2^(C₀ (|x|+1)^c₀)`).
- `LOGSPACE_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE`.

**Example** (`Machines/ARMWidthExample.lean`):

- `searchLang P := {x | ∃ u < 2^|x|, ⟨x, bits u⟩ ∈ P}`.
- `searchLang_mem_PSPACE (hP : P ∈ PSPACE)`: an exponential counter in a polynomial-width
  register, with one call per value.
- This is the skeleton of `NP ⊆ PSPACE` and of the outer search in Savitch.
- `TQBF ∈ PSPACE` is the second customer; see "The remaining customers".

## 3. Configuration codec — accepted

Everything is in `SpaceComplexity/Codec/`: 16 files, all under the 600-line target except
`Valid.lean` (601 lines).

**The codec.** For a fixed `N : FinNDTM Bool`:

- `cfgCode N x s` encodes a configuration with work tapes windowed to `[-s, s]`.
- Fields are fixed-width, so a logspace decider can extract them.
- `cfgCode_lt` bounds every code by `2^(codeK N · (s + logSpace|x| + 1))`.
- `decodeCfg_cfgCode` is the decoder; `cfgWord_congr` / `coreSum_eq_of_cfgWord_eq` give
  injectivity up to your `coreSum`.

**Four tests, all `∈ LOGSPACE`:** `validLang`, `initLang`, `acceptLang`, `stepLang`.

- Each is decided by a deterministic ARM. The transition table of `N` is hard-wired into the
  labels, and the machine reads its input by index.
- They are callable in `whole` mode with argument registers `[c, s]`, or `[c, c', s]` for
  `stepLang`.
- `stepLang` is characterized through your `CfgStep`.
- `acceptLang` is literally the acceptance condition of `DecidesInSpace`.

**Bridge** (`Codec/Bridge.lean`). `mem_iff_codeChain` says: for every window
`s ≥ sp |x|`, `x ∈ L` iff there is a code chain `init c₀`, `step cᵢ cᵢ₊₁`, `accept c_t`,
with `t ≤ N.configBound |x| s` and all codes below the width bound.

On the "counting half" of your extension 3: your `ConfigGraph.lean` already has
`FinNDTM.configBound`, and the codec builds on it. Nothing from cslib was vendored or
adapted.

**Example — `PSPACE = NPSPACE`** (`SavitchARM/`, 7 files; filled in `Savitch.lean`).

- Proved as `NPSPACE_subset_PSPACE` plus your `PSPACE_subset_NPSPACE`.
- A deterministic poly-width ARM computes `s`, `w = poly(|x|)` and `K = 2^w`.
- It searches for an initial code `u < K` and an accepting code `v < K` with
  `Reach K R w u v`. This is Savitch's midpoint recursion of depth `w`.
- The recursion runs on an explicit stack: endpoints are packed as `w`-bit digits of one
  register, and phase bits as binary digits of another.
- Every register stays below `2^(w²)`, so `arm_decides_pspace_val` applies with the codec's
  LOGSPACE tests as deciders.
- The proof does **not** go through your general `savitch`. That theorem and
  `spaceConstructible_poly` remain sorried, and no sorry lies in
  `PSPACE_eq_NPSPACE`'s dependency chain.

## The remaining customers

All sorry-free, `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`, each through an
independent adversarial verification.

- **`PATH_NLComplete`** (`Logspace/PathHard*.lean`). For `L ∈ NL` decided by `N`, the reduction
  outputs the configuration graph on `2^E` vertices (polynomially many): vertex `c+2` is code
  `c`, a source `0` joined to every initial code, a target `1` reached from every accepting
  code, and `StepRel` edges. No accepting normalization is needed. Each output bit is decided
  by a deterministic ARM calling the codec deciders, so the map is implicitly logspace
  computable; correctness is `mem_iff_codeChain` / `mem_of_codePath`.
- **Immerman–Szelepcsényi** (`Logspace/ISCount*.lean`). One nondeterministic ARM proves
  `compl_mem_NSPACE : (∀ n, logSpace n ≤ S n) → L ∈ NSPACE S → Lᶜ ∈ NSPACE S`. It runs the
  inductive counting over codes at radius `s = 0, 1, …` and stops when the reachable count
  stops growing (`ExpBFS/Radius.lean`: equal counts at consecutive radii mean no branch leaves
  the window). It never computes `S`, so it is stronger than Corollary 4.21 as stated.
  `NSPACE_compl_eq` uses only `hS.1`; `compl_mem_NL` is its `S = logSpace` case, giving
  `compl_PATH_mem_NL` and `NL_eq_coNL`. Your sketch's route through `PATH_NLComplete` and an
  `NL` reduction-closure lemma is not needed.
- **`TQBF_mem_PSPACE`** (`ClassPSPACE/TQBFARM/`). Validate the whole input first (non-encodings
  decode to a true fallback, so they are accepted), then walk the `2^m` assignments depth
  first with the assignment as a binary stack register; leaves stream the CNF from the input.
  `arm_decides_pspace_val` with registers `≤ 2^(|x|+1)`. Your private `b4m*` block is left in
  place; `TQBFARM/Semantics.lean` has public twins of three of its lemmas.
- **`TQBF_PSPACEHard`, `TQBF_PSPACEComplete`** (`ClassPSPACE/TQBFHard*.lean`). [AB09]'s
  ∀-folded `ψᵢ` over code blocks of width `w` with `configBound ≤ 2^w`; the matrix is one
  polynomial-time predicate (initial / accepting / step via the codec and `LOGSPACE_subset_P`),
  turned into a circuit by the existing Cook–Levin tableau and into a CNF by Tseitin, with the
  gate variables quantified existentially after the prefix. **This does not use the RD-2
  `ConfigCodec` lemmas or `FormulaKit`**; they are untouched, still sorried, and currently
  have no consumer. Whether to keep RD-2 is your call.
- **`NSPACE_subset_exp_dtime`** (`Machines/MARM*.lean`, `ExpBFS/`, `ExpTime.lean`). The plain
  ARM has no useful time bound (its instructions are unary in register values), so this adds
  a fourth extension: **MARM**, the ARM plus a monotone bit tape (`mread`, `mset`, `mleft`,
  `mright`), compiled with the same `detPart` trick, and `marm_dtime`, a general bridge into
  `DTIME`: because the memory only gains ones, time ≤ `2^{O(W + log n)}·(P+1)²` by counting
  configurations. A BFS over codes at growing radii then gives the theorem, again needing only
  `logSpace ≤ S`. `NL_subset_P` and `polyTimeReducible_of_mem_NL` are now sorry-free.

What remains sorried on the chapter-4 side: `savitch` (general `S`) and
`spaceConstructible_poly`, the hierarchy theorems, the RD-2 `ConfigCodec` lemmas, and the
`FormulaKit` items.

**Your design §16b.** Item 4 (C2 as Light programs with coins, removing the dependency on the
ND ARM) and the Savitch part of item 1 are now covered by the ARM proofs above; you may want to
drop or re-scope those stage-2 obligations. Item 2's RD-2 route is likewise no longer on the
critical path for `TQBF_PSPACEHard`.

## The `CounterProg` question

**Use indexed access.** It is what the ARM already does, through your
`InputAccess.lean`: an `inputBitLang` call on a register-held index. Every consumer above
(PATH, all four codec deciders) reads the input this way, at no extra cost. A rewind
instruction would cost `O(i)` time per read and would need a new `CounterProg` simulation
proof for no benefit. I would leave `CounterProg` as is and steer `2^O(S)`-time searches to
the ARM.

## Provenance

Both answers are **no**.

- **Bonnet's `TimeCompiler` (lax-434930):** the `LogProg` compiler (`Machines/`) was written
  from scratch in the chapter-6 campaign (`f70c57c2`). Neither the code nor the campaign's
  working notes reference Bonnet's archive; it also targets Lean 4.33 against our 4.25.
- **cslib's `Cfg.core`:** `ConfigCount.core` was written in the same campaign, likewise without
  reference to cslib's `MultiTape/ConfigBound.lean`. Any similarity is convergent (both
  forget the parts of a configuration that do not affect its future).

## Addendum items

1. **Hosting `InputAccess.lean` / `PreimageHost.lean`.** Fine where they are under
   `Logspace/`. If they become general infrastructure, a move to `Machines/` can happen at
   integration. `InputAccess` now has four consumers here.
2. **Oracle-input call mode for the ND ARM.** Agreed in principle but **not implemented**
   yet. The `detPart β` architecture means it would come almost for free once the
   deterministic layer has the mode (i.e. once `OIS` is folded into the compiler). I suggest
   doing that together with `mem_NL_of_logspaceReducible`.

## Requests back to you (payback ledger)

To remove copies made because the originals are private in `ConfigGraph.lean`, please make
these public:

- `InWindow`, which `Codec.InWin` copies;
- `runWith_take_inWindow`;
- the accept ⇒ membership argument. `Codec.mem_of_acceptsWithin` replays it (used once,
  by `Codec.mem_of_codePath`, which both `Codec.mem_iff_codeChain` and the Savitch machine
  use).

Also:

- the private `values_getD_eq_of_eval_tseitinGates` in `DAGCircuitSat.lean` (copied in
  `TQBFHardTseitin.lean`), and `inWindow_of_coreSum_eq` in `ConfigGraph.lean` (re-proved as
  `ExpBFS.inWin_of_coreSum_eq`).
- Dead code you may delete: the private `s1b_*` block in `ConfigGraph.lean` (the record-table
  route, now unused) and, if nothing else needs it, its `Build.RecordTable` import.
- Stale planning text: `AroraBarakChapters3-4Plan.md` rows B2 and fills-6, `backlog.md` MIG-19,
  `machine-library-design.md` S1b row (§12) and §16b items 1, 2 and 4.

Once they are public, the copies are deleted. The smaller in-house clean-ups are done:
`PathKit` moved to `Machines/NARMKit.lean`; `getD_drop` and `vword_whole₂/₃` live in
`Machines/VWord.lean`; the bounded-run guard (`GuardLe`) and the generic counting loops live
in `Machines/ARMLoops.lean`.

## Merge coordination

This work was merged directly into `complexity/arora-barak-ch3-4` on top of `069cde82` (your
branch head at the time), with the whole library building (`lake build`, 4248 jobs, exit 0).
Files of yours whose bodies or docstrings changed: `Path.lean`, `Savitch.lean`,
`ImmermanSzelepcsenyi.lean`, `TQBF.lean`, `ConfigGraph.lean` (the move above), and the
`SpaceComplexity` / `ClassPSPACE` facades. In `Machines/Compile.lean` (mine) `compile_correct`
became a corollary of the new `compile_correct_from`.
