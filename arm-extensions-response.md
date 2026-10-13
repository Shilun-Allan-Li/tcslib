# Response: ARM extensions for chapters 3–4

*Reply to `arm-extensions-proposal.md` (Seyoon, chapters 3–4 campaign).
Branch `complexity/arm-extensions`, cut from `complexity/arora-barak-ch3-4` at `50678912`.
Status: built and independently verified, not yet committed.*

## Summary

**All three extensions are accepted and implemented.** Each one also has a real consumer
filling a sorry from your campaign:

| Extension | Status | Concrete use |
|---|---|---|
| 1. Nondeterministic ARM | done | `PATH_mem_NL` (Path.lean), now proved |
| 2. Poly-width ARM | done | `searchLang_mem_PSPACE` (example); Savitch below |
| 3. Configuration codec | done | `PSPACE_eq_NPSPACE` (Savitch.lean), now proved |

Two ground rules held throughout:

- **No statement of yours changed.** Only the bodies of `PATH_mem_NL` and
  `PSPACE_eq_NPSPACE` were filled, and their docstring sketches rewritten to match the proofs
  (with the `[AB09 …]` tags kept).
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
- `PATH_NLComplete` is untouched and still sorried. The codec (extension 3) is the intended
  tool for its hardness half.

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
- `TQBF ∈ PSPACE` is not done here. It is a natural next customer: a recursion over
  quantifier depth in the same stack style as Savitch below.

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

## The `CounterProg` question

**Use indexed access.** It is what the ARM already does, through your
`InputAccess.lean`: an `inputBitLang` call on a register-held index. Every consumer above
(PATH, all four codec deciders) reads the input this way, at no extra cost. A rewind
instruction would cost `O(i)` time per read and would need a new `CounterProg` simulation
proof for no benefit. I would leave `CounterProg` as is and steer `2^O(S)`-time searches to
the ARM.

## Provenance

> **TO CONFIRM BEFORE SENDING (only the author can answer these):**
> - Bonnet's `TimeCompiler`: ☐ no / ☐ yes (cite).
> - cslib's `Cfg.core`: ☐ no / ☐ yes (cite).

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

Once they are public, the copies are deleted. The smaller in-house clean-ups are done:
`PathKit` moved to `Machines/NARMKit.lean`; `getD_drop` and `vword_whole₂/₃` live in
`Machines/VWord.lean`; the bounded-run guard (`GuardLe`) and the generic counting loops live
in `Machines/ARMLoops.lean`.

## Merge coordination

The branch is based on `complexity/arora-barak-ch3-4` and touches your files `Path.lean`
and `Savitch.lean` (bodies only) and the `SpaceComplexity` facade. I propose merging it
into your ch3-4 branch before your chapter-4 PR, so it carries the sweep and axiom evidence
as you planned.
