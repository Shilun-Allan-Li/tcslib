# Word RAM ⇒ efficiency for the cryptography campaigns: assessment and requests

2026-11-18. Maintainer assessment for the iO-components campaign (sPRG and degree-2 PHFE jobs),
for forwarding to the RAM campaign's maintainer chat. It was made by static reading only: no Lean,
no `lake`.

**Sources.**
- **RAM branch:** `origin/complexity/ram-simulation` at tip `cb44316a22c258628bf571da8c84b72c347ee493`,
  read with `git show` and `git grep`. Unmarked `file:line` references are to this tip.
- **Records branch:** `cryptography/pass-shelat-ch2-4` at `cb1b0b8a`. References to it are marked
  "(records)".

Rulings in force (`IOComponentsPlan.md`, decision log of 2026-11-18):
- the deterministic algorithms are proved efficient now;
- the security reductions are word-RAM programs too, and carry `sorryAx` only through the RAM
  simulation chain;
- the word-RAM ⇒ `PolyTimeComputable`/NUPPT bridge is held, pending Seyoon's own bridge branch.

Seyoon's decision, relayed during this assessment: the RAM campaign also delivers the reverse
simulation, TM → word RAM. The recommendation (§7) is built around two deliverables: **(a)** the
crypto-facing bridge and **(b)** the TM → RAM conversion.

---

## 1. Summary for forwarding

**What exists at the RAM tip.**
- **Stage 2, function mode included, is stated.** `WordRAM.exists_simulation`
  (`RAMSimulation/Simulation.lean:142`) concludes `M.ComputesInTime x (outputOf fn v o) (simTime …)`.
  This is the same predicate that `PolyTimeComputable` is built from.
- **It is the only admission that its corollaries reach.** Gate 163's dependency probe found that
  `mem_P_of_decides` and `computesInSpace_of_computes` reach only `WordRAM.exists_simulation`.
- **The rest of the chain is proved:**
  - the run calculus (`WordRAM/Extended.lean`, 0 `sorry`);
  - the word-size witnesses (`WordSize.lean`, 0 `sorry`);
  - all nine class corollaries (`Classes.lean`, 0 `sorry`).
- **The `sorry`s left in the RAM work are 17:**
  - the 2 targets, `exists_simulation` and `exists_ndSimulation`;
  - the 15 tier-2 statements (jobs A–E).
- **What already reaches function mode:**
  - `mem_P_of_decides` (`Classes.lean:147`) is the polynomial-time corollary, but only in verdict
    mode;
  - `computesInSpace_of_computes` (`Classes.lean:260`) is function mode, but log-space only.
- **There is no function-mode, polynomial-time bridge** to `PolyTimeComputable` anywhere on the
  branch.
- **The "existing bridge sketches" on the branch** are these:
  - PLAN §5's draft `WordRAM.exists_oneTape_simulation` (`campaign/items/ram-tm/PLAN.md:115–135`):
    function mode, `M.ComputesFunInTime g …`, with `T` and `F` indexed by `|x|`;
  - the stated goal of design §15, "feeding `∈ P`, `PolyTimeComputable` and `SPACE`
    memberships" (`machine-library-design.md:3155–3159`);
  - §15c's "for BPP it produces a deterministic machine that takes the coins as a second input"
    (`machine-library-design.md:3484`), which is not stated in Lean.
- **No fetched remote** (`origin/ram/*`, `origin/complexity/ram-simulation`) contains a
  `PolyTimeComputable` bridge.

**Black-box answer (§2).** Yes. The crypto bridge can use `exists_simulation` purely as a black
box.
- An `NUPPT` is a deterministic `FinTM Bool` on the whole input `z = ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`.
- `NUPPT.ofPolyTime` takes the coin polynomial, the advice polynomial and the advice function as
  arguments, and gets `halts` from `PolyTimeComputable`.
- So the RAM program reads advice and coins with `rdIn`. It needs no `coin` instruction.
- Adversaries stay at the TM level: `exists_handlerMachine`, `exists_interactiveHandlerMachine`,
  `exists_comp` and `exists_reparam_pre_post_adv` take only `PolyTimeComputable` hypotheses for
  the reduction's own pieces.
- The adapter from `exists_simulation` to `PolyTimeComputable` is about 100–200 lines. It is the
  proof of `mem_P_of_decides` with `fn := true`.

**Uniformity (§3, binding).**
- Honest algorithms get a **uniform** form: one `XProgram` for all parameters, reading `n` from
  `1^n`, gives `PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`.
- The advice-taking NUPPT form is for reductions and adversaries only. A bare
  `∃ A : NUPPT, A.Computes f` holds even for uncomputable `f` (`PPT.lean`'s warning).
- The shapes make κ-indexed program families and per-κ constants impossible.
- TM → RAM maps a uniform machine to a uniform program, and takes any advice as input.

**What is missing, in priority order.**

| # | Item | Side | Size (lines) | `sorry` dependence |
|---|---|---|---|---|
| (a1) | `WordRAM.polyTimeComputable_of_computes`, and the `progOut` form (totality on every input, correctness only on well-formed inputs) | RAM | 150–300 | `exists_simulation` only |
| (a2) | A stock **polynomial** word size: `wordSizeComputable_of_timeConstructible` and `wordSizeComputable_poly`. Today only `c·logSpace` exists, which is too small for κ-bit moduli. | RAM | 40–120 | none (on the RAM base) |
| (a5) | **An authoring language with string I/O.** Light today has no `inBit` or `emit`, and its compiler emits `List Instr`, not `XInstr`. The choice is PROG-2 (design §15c/§15d) or a load–run–emit wrapper around compiled Light. Either way, it comes with the Light-run ⇒ `HaltsWithin` link. | RAM | wrapper 800–1,500; PROG-2 1,400–2,300 plus compiler edits | none |
| (a4) | **I/O adapters:**<br>- "views" of nested `pairEncode` inputs, with the `1^n` reader;<br>- fixed-width big-endian fields (`natToList`/`listToNat`) to and from words;<br>- `pairEncode`-formatted emission. | RAM (generic) and crypto (layout-specific) | 500–1,200 | none |
| (a3) | NUPPT forms of (a1): the **uniform** `NUPPT.exists_uniform_ofProgram` (honest algorithms) and the advice-taking `NUPPT.exists_ofProgram` (reductions only), with the `runAtL` equations | crypto (needs `PPT.lean`, absent on the RAM branch) | 50–120 | as (a1) |
| (b1) | **TM → RAM**, as a Light *procedure* running any `FinTM Bool` on a bit string in memory, specified by `Meets`, with linear overhead in `t + |x|` | RAM | 1,500–3,000 | none |
| (b2) | The standalone corollary `PolyTimeComputable g ⇒` a polynomial-time `XProgram` computing `g` (input by `rdIn`, output by `emit`) | RAM | 150–400 over (b1) and (a5) | none |
| (b3) | Procedure relocation for Light, so that library procedures (b1, the adapters, `emod`) can be appended to any program. This is upstream `Lang/Renumber.lean`, deferred in design §15b. | RAM | 300–600 | none |

**Unblocking order.**
- **For sPRG** (ℤ_p and Boolean arithmetic only): (a1), (a2), (a5), (a4), (a3).
- **For PHFE:** the same, plus **(b1)**. Its bilinear-group operations are only given abstractly
  (`Pairing.BilinearGen.Ops`, a bundle of `PolyTimeComputable` string functions). A RAM program
  can execute them only by running their machines as subroutines. Without (b1), PHFE keeps its
  group-operation glue in the `PolyTimeComputable` closure algebra, as BB1 does today.

**Branch bases.** The RAM pieces and the NUPPT layer are not on a common base today.
- The RAM branch is cut from `main` `5cb25d52` (#364). It lacks `Randomized/PPT.lean`,
  `Randomized/Closure.lean` and `Games/Efficiency.lean`.
- The records branch is cut from `main` #200. It carries stale RAM files: `Extended` with 18
  `sorry`s, `WordSize` 3, `Classes` 9, no `Sim/*`, and `TimeConstructible` with 2 `sorry`s.
- The two branches differ in 853 `TCSlib` files (1,297 and 1,762 own commits).
- So the RAM side should deliver (a1), (a2), (a4)-generic, (a5) and (b) on its own branch, which
  imports no cryptography. (a3) is a short crypto-side file, written once the lines meet.

---

## 2. The black-box question

> Can the crypto-facing bridge use the RAM → TM simulation purely as a black box, forwarding advice
> and coins?

**Answer: yes, on every point.** Each point was verified in the code.

**(1) Advice and coins are just input.**
- `NUPPT` (`Randomized/PPT.lean:137`, records) is a structure with these fields:
  - `M : FinTM Bool`;
  - `Ct` and `ct`;
  - `coins` and `adv : PolyExpr`;
  - `advice : ℕ → List Bool`, with `advice_length`;
  - `halts : ∀ z, ∃ out, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)`.
- The machine sees advice and coins only inside its input:
  - `runAt n y r := output (pairEncode (pairEncode (advInput n y) (advice n)) (List.ofFn r))`
    (`:235`);
  - `runAtL` (`:240`) is the same with an untyped coin string;
  - `advInput n y = pairEncode (1^n) y` (`:210`).
- **`NUPPT.ofPolyTime hf coins adv advice hα`** (`:345`) does take an advice function, with its
  bound `hα`. It obtains `M`, `Ct`, `ct` and `halts` from `hf : PolyTimeComputable f`.
- `runAtL_ofPolyTime` (`:398`) gives
  `runAtL n y r = f (pairEncode (pairEncode (advInput n y) (advice n)) r)`.
- `ofPolyTimeUniform` (`:406`) is the empty-advice case.
- So a RAM program that reads `z` with `rdIn` and parses it needs neither `coin` nor any special
  treatment of advice. The bridge is the following chain:
  1. the function-mode simulation;
  2. `PolyTimeComputable`;
  3. `ofPolyTime`, with advice and coins supplied by the caller.
- Building the structure directly is also easy: `halts` comes from the bridge's per-input
  `ComputesInTime`. Going through `ofPolyTime` reuses its readers (`coins_ofPolyTime`,
  `advice_ofPolyTime`, `runAtL_ofPolyTime`) and is shorter.
- **On `coin`:** `exists_simulation` runs the program with the empty coin stream (`[]`,
  `Simulation.lean:145`), so every `coin` reads `0` (`xstep`, `Extended.lean:122–124`). This is
  harmless, but it means randomness must come from the coin slot of `z`.
  `HaltsWithin.coin_irrel` (`Extended.lean:684`) covers `CoinFree` programs.

**(2) The predicates line up. The adapter is small and the arithmetic already exists.**
- `PolyTimeComputable f := ∃ M C c, M.ComputesFunInTime f (fun n => C * (n + 1) ^ c)`
  (`ClassNP/PolyTime.lean:69`; records `:73`).
- `ComputesFunInTime f T := ∀ x, M.ComputesInTime x (f x) (T x.length)`
  (`TuringMachine/Finite.lean:312`).
- `ComputesInTime` means: halted (state `none`) by time `t`, with completed output exactly `w`
  (`computesInTime_iff`, `:414`).
- `exists_simulation P fn hW` concludes `M.ComputesInTime x (outputOf fn v o) (simTime A TW |x| (W |x|) t f)`.
  This is the same predicate, the same output-tape convention and the same halting state.
  `outputOf_true` (`Simulation.lean:101`) rewrites the output to `o`.
- The only adaptation is enlarging the per-input deadline to a polynomial in `|x|`, by
  `ComputesInTime.mono` (`Finite.lean:368`). The arithmetic is proved, but **private**:
  - `polynomial_time_bound` (`Classes.lean:72`) bounds the deadline;
  - `mem_P_of_decides` (`Classes.lean:147–171`) does exactly this in verdict mode;
  - the steps are `HaltsWithin.touches_le` (no cell hypothesis), then `t ≤ C(n+1)^d`, `f ≤ 3t` and
    `TW n + W n ≤ C(n+1)^d`;
  - the result is `simTime ≤ (A + 1)·a·(n + 1)^(3d+1)`, with `a = C + (C+1)(4C² + 3C + 1)`.
- So `simTime ≤ Ct·(|z|+1)^ct` is just arithmetic. The time is measured in `|z|`, the same length
  that NUPPT's budget uses.
- The adapter is therefore the proof of `mem_P_of_decides`, with `fn := true` and
  `polyTimeComputable_iff` in place of `mem_DTIME_iff`/`mem_P_iff`. It goes in `Classes.lean`, or
  `polynomial_time_bound` is made public.
- **Stock `WordSizeComputable` instances, and their limits.**
  - `wordSizeComputable_logSpace c` (`WordSize.lean:853`) gives `W = c·(⌊log₂ n⌋+1)` in linear time.
  - `wordSizeComputable_of_spaceConstructible` (`:893`) has an **uncontrolled** time `TW`, so it is
    useless for time.
  - Neither suits ℤ_p with κ-bit `p`, which needs `W ≥ 2κ + O(log ℓ)`; see (a2).
  - The ingredients for a polynomial instance exist: `Complexity.timeConstructible_poly C c`
    (`ClassNP/TMSAT.lean:571`) and `MultiTapeTM.spaceUsed_le_mul_succ` (`Finite.lean:149`, space at
    most `k·(t+1)`).

**(3) Totality is the caller's obligation, and nothing in the simulation obstructs it.**
- `exists_simulation`'s hypothesis is per input: `∀ x t f v o, HaltsWithin P x [] (W |x|) t v o f → …`.
  It promises nothing on inputs where the program does not halt.
- `PolyTimeComputable g` constrains every `x : List Bool`. `NUPPT.halts` constrains every `z`.
- So the bridge hypothesis must cover all strings, malformed layouts included:
  `∀ x, ∃ t ≤ C(|x|+1)^d, ∃ v, HaltsWithin P x [] (W |x|) t v (g x) f`.
- To spare the crypto side from specifying `g` off the layouts, (a1) should also offer the
  `progOut` form (§5).

**(4) Adversary composition stays at the TM level and is black-box.**

| Wrapper (records) | Hypotheses on the reduction's own pieces |
|---|---|
| `Games.exists_handlerMachine` (`Games/Efficiency.lean:332`) | `PolyHandler` (`:163`): `run`, `advIn`, `out` with `poly`, `advIn_poly`, `out_poly : PolyTimeComputable …`; lengths as `PolyExpr`; `init` arbitrary, put in the advice by the wrapper |
| `Games.exists_interactiveHandlerMachine` (`:844`) | `InteractiveHandler` (`:411`): `run`, `advIn`, `finRun` with `PolyTimeComputable` fields |
| `NUPPT.exists_comp` (`Randomized/Closure.lean:272`) | `PolyTimeComputable pre`, `PolyTimeComputable post` |
| `NUPPT.exists_reparam_pre_post_adv` (`Cryptography/Asymptotic/UniversalLemmas.lean:125`) | `PolyTimeComputable pre`, `PolyTimeComputable post`, `φ ≤ p`, `|β m| ≤ b m` |
| `exists_withAdvice` (`Closure.lean:358`), `exists_split` (`:390`), `exists_reparam_advice` (`:325`) | none on the adversary; they forward advice and coins |

- These wrappers forward the adversary's advice and coins themselves. For example,
  `exists_handlerMachine` uses `pairEncode (A.advice n) (init n)` as advice and the seed as coins.
- The adversary itself enters only through `A.polyTimeComputable_output` (`PPT.lean:194`).
- So, if the handler or pre/post pieces are RAM programs, (a1) supplies exactly the
  `PolyTimeComputable` facts the wrappers ask for. No RAM program ever runs the adversary.
- The one thing this route does not cover is a handler that must call an **abstract** operation,
  such as `G.Ops.mulG`, *inside* a RAM program. That is (b1), §6.

**(5) Admission dependence of a black-box bridge.**
- **At this tip: exactly `WordRAM.exists_simulation`.**
  - Its proof is literally `sorry` (`Simulation.lean:149`).
  - The proved word-size witnesses and tier 0 introduce no other admission. Gate 163's dependency
    walk (`campaign/gates/163-ram-fill-classes/evidence/REPORT-tier3.md`, table under "Targets and
    exact admission dependencies") found this for the analogous `mem_P_of_decides`,
    `mem_P_of_decides_logWord` and `computesInSpace_of_computes`.
  - A new polynomial word-size witness built on `timeConstructible_poly` should be admission-free
    on the RAM base, where `ClassP/TimeConstructible.lean` and `ClassNP/TMSAT.lean` have no
    `sorry`. This needs a probe.
  - On the records base, `TimeConstructible.lean` still has 2 `sorry`s
    (`Turing.FinTM.lengthBitsTM_computes`, `lengthBitsTM_spaceUsed`), which `timeConstructible_poly`
    may reach.
- **After job E fills `exists_simulation`, and until jobs A–D land,** the bridge transitively rests
  on the 15 tier-2 statements:
  - `Build/WordArith.lean`: `Turing.bvBits_injective`, `exists_wordAddTM`, `exists_wordSubTM`,
    `exists_wordMulTM`, `exists_wordHalfTM`, `exists_wordSignExtendTM`, `exists_wordIntTM`,
    `exists_wordSignTM`, `exists_wordNonzeroTM`;
  - `Build/KeyTable.lean`: `exists_keyLookupTM`, `exists_keyAssignTM`;
  - `Build/InputBit.lean`: `exists_inputBitTM`;
  - `RAMSimulation/Sim/Startup.lean`: `WordRAM.Sim.exists_startup`;
  - `RAMSimulation/Sim/Phases.lean`: `WordRAM.Sim.exists_phase`, `WordRAM.Sim.exists_verdictPhase`.
- `RecordTable`'s 4 admissions (`exists_tableFindTM`, `exists_tableAppendTM`,
  `exists_recordValidTM`, `exists_recordNextTM`) are not used by tier 2 (TIER2-DESIGN §4 item 3).
- `exists_ndSimulation` is not needed by any crypto bridge.

---

## 3. Uniformity (binding: Seyoon, 2026-11-18)

**The rule.** Honest algorithms must not become non-uniform through these conversions. The
advice-taking NUPPT form is for reductions and adversaries only.

**Why it matters.** `PPT.lean` (records, `:309–327`, docstring of `NUPPT.Computes`) warns that a
bare `∃ A : NUPPT, A.Computes f` holds even for **uncomputable** `f`. Advice `[h n]` for an
arbitrary `h : ℕ → Bool` is read back by the machine. So efficiency of an honest algorithm is
`A.Uniform ∧ A.Computes f`, or `PolyTimeComputable` of the uniform function.

**What the library already offers on that side** (records):
- `NUPPT.ofPolyTimeUniform` (`PPT.lean:406`);
- `exists_uniform_computes` (`:448`);
- the converse `NUPPT.Computes.polyTimeComputable` (`Randomized/Closure.lean:458`, which assumes
  `A.Uniform`).

**How the statement shapes enforce uniformity.**
- **One program.** (a1) quantifies one `P : XProgram`, fixed before every input. A κ-indexed family
  `ℕ → XProgram` does not fit its type.
- **No per-κ constants.** One `XProgram` has finitely many immediates, so it cannot hard-wire a
  constant per κ, such as a prime `p(κ)`.
- **The parameter is read from the input.** The program reads `n` from `1^n` and must compute
  `p(κ)` or read it from `y`, for example from public parameters.
- **The word size cannot smuggle information.** `W` is a function of `|z|` only, and
  `WordSizeComputable` requires a machine computing `Nat.bits (W |z|)`.
- **No silent advice.** No advice argument appears anywhere in (a1), (a2) or the uniform forms
  below. Advice enters only through (a3)'s explicit `advice` parameter.

**Uniform forms (honest algorithms). Proposed.**

```lean
/-- (proposed) An honest deterministic algorithm, one word-RAM program for all parameters and
inputs, reading `n` from `1^n`, is computed with probability one by a PPT. -/
theorem NUPPT.exists_uniform_ofProgram (P : WordRAM.XProgram) {W TW SW : ℕ → ℕ}
    (hW : WordRAM.WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ m, TW m + W m ≤ C * (m + 1) ^ d)
    (hhalt : ∀ z : List Bool, ∃ (t f : ℕ) (v : Bool) (o : List Bool),
      t ≤ C * (z.length + 1) ^ d ∧ WordRAM.HaltsWithin P z [] (W z.length) t v o f)
    (f : List Bool → List Bool)
    (hf : ∀ n y, WordRAM.progOut P W (advInput n y) = f (advInput n y)) (coins : PolyExpr) :
    ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧ A.Computes f

/-- (proposed) The same with the coin slot read by the program (a randomized honest algorithm;
the coins are input, never `coin`). -/
theorem NUPPT.exists_uniform_ofProgram_coins (P : WordRAM.XProgram) … (coins : PolyExpr) :
    ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧
      ∀ n y r, A.runAtL n y r =
        WordRAM.progOut P W (pairEncode (pairEncode (advInput n y) []) r)
```

The proofs are short:
- the first: (a1)'s `polyTimeComputable_progOut`, then `exists_uniform_computes` for `progOut P W`,
  then `hf`;
- the second: `ofPolyTimeUniform` and `runAtL_ofPolyTimeUniform` (`PPT.lean:437`).

At the `Complexity` level, the uniform form is (a1) itself: `PolyTimeComputable g` from one
program.

**Non-uniform form (reductions and adversaries only).** This is (a3), `NUPPT.exists_ofProgram`,
with an explicit `advice : ℕ → List Bool`. The program is still one `XProgram`. The advice is part
of its *input*, as for every NUPPT, and never part of its text. Its docstring should say
"reductions only".

**For (b), TM → RAM.**
- `exists_program_of_finTM M` and `Light.exists_tmProc M` produce a program depending on `M` only,
  fixed before all inputs. So a uniform machine gives a uniform program.
- **Applied to an NUPPT `A`,** the interpreter runs `A.M` on a string that the *caller* assembles
  in memory, including `A.advice n`. In an honest algorithm, `A` must be uniform: the slot is
  `[]`, as in `ofPolyTimeUniform`.
- **In a reduction,** the adversary's advice is copied from the reduction's own advice slot, as
  `exists_handlerMachine` already does.
- The shapes forbid baking advice in. One program for all `n` cannot hold `A.advice n` for every
  `n`.
- **Classically chosen subroutines stay uniform.** A machine chosen with `Classical.choose` from a
  `PolyTimeComputable` witness (`G.Ops` fields, `ArithmeticFP` fields, `BinaryArith`) is one fixed
  machine, so a program calling it through (b1) stays uniform. The group description `G.desc κ r`
  is input.

---

## 4. What exists (precise)

### 4.1 The word RAM (`TCSlib/Programs/WordRAM/`)

**The instructions and the program.**
- `WordRAM.Instr` (`Basic.lean:40`) has nine instructions over cells `ℤ`: `one`, `add`, `sub`,
  `mul` (mod `2^W`), `load`, `store` (indirect), `bltz i l` (immediate target only),
  `accept`, `reject`.
- `exec` (`:53`) is the functional run of base programs.
- `WordRAM.XInstr` (`Extended.lean:80`) is `base` plus four new instructions:
  - `rdIn i j` sets `[i]` to the input bit at position `[j]`, as 0 or 1, and to 0 off the input
    (`inBitWord`, `:101`);
  - `emit i` appends the bit "`[i] ≠ 0`" (`:121`);
  - `coin i` reads the next coin of the stream ρ, and 0 past its end (`:122–124`);
  - `half i j` is the arithmetic shift right.
- `XProgram := List XInstr` (`:88`).
- **No indirect jump, and no call or return.**

**Words and memory.**
- A word is `BitVec W`, read signed (`toInt`). `wd W v = BitVec.ofInt W v` (`Steps.lean:76`).
- **The word size** `W` is a run parameter. The simulation sets it as `W (|x|)`, a function of the
  input length only.

**Input and output conventions.**
- The input is read in place by `rdIn`.
- `|x|` arrives in cell `-1`, as `wd W |x|`, so modulo `2^W` (`initMem`, `:572`). Every other cell
  is 0.
- The output is the list of emitted bits (`XCfg.out`, `:95`).

**Halting.**
- `HaltsWithin P x ρ W t v o f` (`:583`): from `XCfg.init W |x|`, the program gives verdict `v`
  after `n < t` steps (the verdict step is counted), has emitted `o`, and stays within a footprint
  of at most `f` cells.
- Proved readers and lemmas: `.mono` (`:596`), `.touches_le` (`:607`, `f := 3t`), `.unique`
  (`:656`) and `.coin_irrel` (`:684`). The file has 0 `sorry`.

**Vendored `Steps.lean` (0 `sorry`).** It has `exec_of_steps` (`:208`, Steps ⇒ exec) and
`exec_mono` (`:220`). It has **no converse** (exec ⇒ Steps). That converse is needed to connect
Light's compile theorem, stated with `exec`, to `HaltsWithin`.

### 4.2 Stage 2 (`TCSlib/Complexity/RAMSimulation/`)

**`Simulation.lean`.**
- `simTime A TW n W t f = TW n + A·(t+1)·(f·(W+1) + W² + n + 1)` (`:74`); `simSpace` (`:79`).
- `outputOf fn v o = if fn then o else [v]` (`:85`), with readers at `:98` and `:101`.
- **`exists_simulation (P) (fn) (hW : WordSizeComputable W TW SW) : ∃ M A, ∀ x t f v o, HaltsWithin P x [] (W |x|) t v o f → M.ComputesInTime x (outputOf fn v o) (simTime …) ∧ spaceUsed ≤ simSpace …`**
  (`:142`, **`sorry`** at `:149`). `M` depends on `P`, `fn` and the witness; `A` is fixed before
  `x`.
- `exists_ndSimulation` (`:170`, **`sorry`** at `:178`) is not needed by crypto.

**Unit-cost multiplication is sound under this charging.**
- Every simulated step is charged `W²` (`simTime`).
- The multiplication row is `exists_wordMulTM`, at `C·(W+1)²` steps (`Build/WordArith.lean:166`).
- So any `W` polynomial in `|x|` keeps `simTime` polynomial: with `f ≤ 3t`, the total is
  `O(t·(t·W + W² + n))`.

**`WordSize.lean` (0 `sorry`).**
- `WordSizeComputable W TW SW` (`:829`): one machine writes `Nat.bits (W |x|)` within `TW |x|`
  steps and `SW |x|` cells.
- Proved: `.mono` (`:837`), `wordSizeComputable_logSpace` (`:853`) and
  `wordSizeComputable_of_spaceConstructible` (`:893`, with uncontrolled `TW`).
- The useful private helpers are `constant_multiplier` (`:217`), `scale_computes` (`:291`) and
  `logarithmic_computation` (`:578`).

**`Classes.lean` (0 `sorry`; the only admission reached is `exists_simulation` or
`exists_ndSimulation`, per gate 163).**
- `mem_DTIME_of_decides` (`:111`), `mem_P_of_decides` (`:147`; any `W` with
  `TW n + W n ≤ C(n+1)^d`) and `mem_P_of_decides_logWord` (`:181`).
- `mem_SPACE_of_decides` (`:210`) and `mem_LOGSPACE_of_decides` (`:236`).
- **`computesInSpace_of_computes`** (`:260`): function mode, but with `W = c·logSpace`, `O(1)`
  cells, and a conclusion `ComputesInSpace`, not a time bound.
- `mem_SPACE_mul_of_decides` (`:287`), `mem_NSPACE_of_accepts` (`:321`) and `mem_NL_of_accepts`
  (`:348`).
- Private: `polynomial_time_bound` (`:72`).

**`Sim/*` (tier-2 internal interfaces).** `Encoding.lean` is proved (`Encodes`, `:136`).
`Startup.lean` has `exists_startup` (`:62`, `sorry`). `Phases.lean` has `exists_phase` (`:123`,
`sorry`) and `exists_verdictPhase` (`:149`, `sorry`).

**`sorry` counts at the tip** (declarations, scanned with `git grep`):

| File | Count |
|---|---|
| `Simulation` | 2 |
| `Sim/Phases` | 2 |
| `Sim/Startup` | 1 |
| `Build/WordArith` | 9 |
| `Build/KeyTable` | 2 |
| `Build/InputBit` | 1 |
| `Build/RecordTable` (not used by tier 2) | 4 |
| `WordSize`, `Classes`, `Extended`, `Steps`, `Basic` | 0 each |

This agrees with `campaign/maintainer/HANDOFF.md` ("2 + 15 admissions … plus `RecordTable`'s 4").

### 4.3 Light, the vendored structured language (`TCSlib/Programs/Light/`)

**Syntax** (`Syntax.lean:80`):
- statements: `skip`, `set`, `store`, `seq`, `ite`, `while`, and `call p args x` (with recursion);
- expressions: `const`, `var`, `+ − ×`, `load`; tests `<` and `=`;
- integer locals, and a memory `ℕ → ℤ`;
- limits `word`, `space` and `depth`.

**There is no `inBit`, `emit` or `coin`: PROG-2 was never done.** `git grep` of
`inBit|emit|coin|XInstr|EndsIO` in `Programs/Light` finds nothing.

**Logic.** `Ends` (`Logic.lean:94`). `Meets lim P p d vals μ T R` (`Calls.lean:57`) is a
procedure specification; callers use only the spec. `Ends.append` (`Logic.lean:105`) keeps proofs
when procedures are appended.

**The compiler.**
- `compileProgram_correct` (`Compiler/WholeProgram.lean:241`) is stated about the vendored `exec`
  on `List Instr`.
- From any memory satisfying `Input lim μ i j m` (`:212`: cells `≥ 0` hold `μ`, and cells
  `-1`, `-2` hold the two arguments), the compiled program gives `verdictOf dec (result)`
  (`:70`) within `startCost + stepsPerStep·c` steps. Then `Outcome` holds (`:221`): the result is
  in cell `-3`, and the final memory is in cells `≥ 0`.
- Calls compile through a dispatcher. The machine has no indirect jump, so a return costs
  `2(r+1)` steps (`Compiler/Dispatcher.lean`, module docstring).

**I/O, in short.** A Light program's input is the preloaded memory and two integer arguments. Its
output is one integer and a verdict. Run from `initMem`, it sees only `|x|` (as argument 1, cell
`-1`), with `μ = 0` and argument 2 equal to 0. So **a Light program cannot read a bit-string input
or emit a bit-string output today.**

**Cost composition with the simulation.** For time, it composes:
- `HaltsWithin.touches_le` removes the need for a footprint;
- the Light → `XProgram` link needs only the exec ⇒ Steps converse, `XSteps.of_steps`
  (`Extended.lean:236`) and `Steps.exists_stepsIn`/`XStepsIn.of_stepsIn_proj` (`:393`, `:543`);
- none of these links is stated today as one theorem.

**Useful routines:** `Lib/Emod.lean` (remainder without division, `O(log(|x|/M))` rounds), `Copy`,
`Seg`, `ArrayAt`, `PowTable`, `Logs`. **Not vendored:** upstream `Lang/Renumber.lean`, procedure
relocation (deferred, design §15b).

### 4.4 What the records branch has and what it would gain

The diff `git diff --stat cryptography/pass-shelat-ch2-4...origin/complexity/ram-simulation` over
`TCSlib/Programs`, `TCSlib/Complexity/RAMSimulation` and `TCSlib/Complexity/TuringMachine/Build`
covers 43 files, +9,512/−12,824.

**What the records branch has.**
- `Programs/Light/**` is identical, with no I/O.
- `Programs/WordRAM/Basic` is identical.
- Older versions of `Steps`, `Extended` (18 `sorry`s), `RAMSimulation/{Simulation (2), WordSize (3), Classes (9)}`.
  The statements are the same, but the readers are absent.
- **None of `Sim/*`, `Build/WordArith`, `Build/KeyTable` or `Build/InputBit`.**

**What a merge would bring.**
- Tiers 0, 1 and 3 proved, and the tier-2 statements.
- Large `Build/` changes from `main` (#200 → #364).
- `TimeConstructible` without its 2 `sorry`s.

The RAM branch in turn lacks the whole NUPPT and Games layer: `Randomized/PPT.lean`,
`Randomized/Closure.lean` and `Cryptography/Games/Efficiency.lean` are absent there.

---

## 5. Deliverable (a): the crypto-facing bridge

Everything here is **proposed**. The statement shapes are drafts for the RAM campaign's statement
gate.

### (a1) Function mode, polynomial time ⇒ `PolyTimeComputable` (RAM side; 150–300 lines)

```lean
namespace WordRAM
/-- (proposed) A word-RAM program that computes `g` on every input within polynomially many steps,
with a word size of polynomial value computable in polynomial time, computes a polynomial-time
function. [AB09, Definition 1.13 and Exercise 1.9] -/
theorem polyTimeComputable_of_computes (P : XProgram) (g : List Bool → List Bool)
    {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hcomp : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool), t ≤ C * (x.length + 1) ^ d ∧
      HaltsWithin P x [] (W x.length) t v (g x) f) :
    Complexity.PolyTimeComputable g
```

The proof is `mem_P_of_decides`'s, with `exists_simulation P true hW` and `outputOf_true`. Its
only admission is `exists_simulation`.

**The `progOut` form, which removes the need to define `g` off the layouts:**

```lean
/-- (proposed) The output of `P` on `x` at word size `W |x|`, if it halts, else `[]`
(well defined by `HaltsWithin.unique`). -/
noncomputable def progOut (P : XProgram) (W : ℕ → ℕ) (x : List Bool) : List Bool
theorem progOut_eq {P W x t v o f} (h : HaltsWithin P x [] (W x.length) t v o f) :
    progOut P W x = o
theorem polyTimeComputable_progOut (P : XProgram) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) (C d : ℕ) (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hhalt : ∀ x : List Bool, ∃ (t f : ℕ) (v : Bool) (o : List Bool),
      t ≤ C * (x.length + 1) ^ d ∧ HaltsWithin P x [] (W x.length) t v o f) :
    Complexity.PolyTimeComputable (progOut P W)
```

The crypto side then proves halting within the bound on every string, which is a property of the
program's loops (bounded by `|x|`, which is in cell `-1`). It proves *correctness* only on
well-formed layouts: `progOut P W (layout 1^n y α r) = …`.

**Not needed:** the single-tape route D of PLAN §5 (`exists_oneTape_simulation`). `PolyTimeComputable`
allows multi-tape machines.

### (a2) A stock polynomial word size (RAM side; 40–120 lines)

```lean
/-- (proposed) A time-constructible function is a word size computable in linear time in its
value. -/
theorem wordSizeComputable_of_timeConstructible {T : ℕ → ℕ}
    (hT : Complexity.TimeConstructible T) :
    ∃ a : ℕ, WordSizeComputable T (fun n => a * (T n + 1)) (fun n => a * (T n + 1))
/-- (proposed) Polynomial word sizes. -/
theorem wordSizeComputable_poly (C c : ℕ) (hC : 0 < C) :
    ∃ a : ℕ, WordSizeComputable (fun n => C * (n + 1) ^ (c + 1))
      (fun n => a * (n + 1) ^ (c + 1)) (fun n => a * (n + 1) ^ (c + 1))
```

**Where the ingredients are.** `TimeConstructible` (`ClassP/TimeConstructible.lean:73`) supplies
the machine. `spaceUsed_le_mul_succ` (`Finite.lean:149`) supplies the space bound.
`timeConstructible_poly` (`ClassNP/TMSAT.lean:571`) supplies the instance. Its home should avoid a
heavy import of `TMSAT` into `RAMSimulation`; moving `timeConstructible_poly` into
`ClassP/TimeConstructible.lean` is one option.

**Why the crypto side needs a polynomial word size.**
- ℤ_p elements with `p` a κ-bit prime, products, and sums of ℓ products before reduction need
  `W ≥ 2κ + ⌈log₂ ℓ⌉ + 2`. Words are signed: `bltz` and the addresses read `toInt`.
- `|x|` must also be exact in cell `-1`, which needs `W ≥ log₂|x| + 2`.
- `W` depends on the input length `|z|`, not on the security parameter. For NUPPT layouts,
  `|z| ≥ 8n + 14`, so `W(|z|) = C(|z|+1)^(c+1)` dominates any fixed polynomial `κ(n)`.

### (a3) The NUPPT bridge (crypto side; 50–120 lines, once both layers share a base)

Two forms. The **uniform** forms of §3 (`NUPPT.exists_uniform_ofProgram`, `…_coins`) serve honest
algorithms. The advice-taking form below serves **reductions and adversaries only**.

```lean
/-- (proposed) A word-RAM program on the NUPPT layout, with advice supplied as input, is a
non-uniform PPT. For reductions and adversaries only; honest algorithms use the uniform form. -/
theorem NUPPT.exists_ofProgram (P : WordRAM.XProgram) {W TW SW : ℕ → ℕ}
    (hW : WordRAM.WordSizeComputable W TW SW) (C d : ℕ)
    (hWpoly : ∀ n, TW n + W n ≤ C * (n + 1) ^ d)
    (hhalt : ∀ z : List Bool, ∃ (t f : ℕ) (v : Bool) (o : List Bool),
      t ≤ C * (z.length + 1) ^ d ∧ WordRAM.HaltsWithin P z [] (W z.length) t v o f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    ∃ A : NUPPT, A.coins = coins ∧ A.adv = adv ∧ A.advice = advice ∧
      ∀ n y r, A.runAtL n y r =
        WordRAM.progOut P W (pairEncode (pairEncode (advInput n y) (advice n)) r)
```

The proof is `ofPolyTime (polyTimeComputable_progOut …)` with `runAtL_ofPolyTime`. The uniform
forms use `ofPolyTimeUniform` and `exists_uniform_computes` (§3). The handler pieces need no wrapper: they consume (a1) directly
(`PolyHandler.poly`, `advIn_poly`, `out_poly`).

### (a4) I/O adapters for the library's string encodings (500–1,200 lines)

**The encodings to support** (records):
- `pairEncode x α = x.flatMap (fun b => [b, b]) ++ [false, true] ++ α`
  (`TuringMachine/Encoding.lean:136`);
- the NUPPT layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`, where `1^n` ends up 8-fold doubled;
- handler inputs such as `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (`PolyHandler.input`);
- fixed-width fields `List.ofFn (b : Fin k → Bool)`;
- big-endian numerals `natToList k N` and `listToNat` (`Candidates/Arithmetic.lean:100`,
  `NumberTheory/Primality.lean:655`), whereas the RAM side uses little-endian `Nat.bits`;
- outputs that must be `pairEncode y s'` with fixed-length parts (`PolyHandler.answer`, decoded by
  `pairDecode`/`decodeFin`).

**Proposed generic layer (RAM side): a "view" API.**
- A view `(o, s, ℓ)` of the input denotes `List.ofFn fun i : Fin ℓ => x.getD (o + s·i) false`.
  Parsing is then pure position arithmetic in place, with no copying. This keeps logspace intact,
  which matters for other consumers.
- A pure list lemma: if view `v` denotes `pairEncode a b`, then `(o, 2s, |a|)` denotes `a` and
  `(o + s(2|a|+2), s, ℓ − 2|a| − 2)` denotes `b`.
- Routines, with specs:
  - `pairSplit`: scan the aligned pairs for the separator; `O(|a|)` steps; returns the two views;
  - `unaryLen` (`1^n` ↦ `n`);
  - `readFieldBE k`: a `k`-bit big-endian field to a word, `O(k)` steps;
  - `emitBE k`: a word to `k` big-endian bits, by `half`, `O(k)`;
  - `emitDoubled` and `emitSep`, for `pairEncode` output.

**Crypto side.** The layout-specific parsers (layout, handler input, group-element encodings) are
built on top of this layer.

**Authoring level.** In Light, after (a5), each routine is roughly 100–250 lines. As raw
`XProgram` fragments, each needs relocation and sequencing lemmas, roughly +300–600 lines for a
composition kit. Recommendation: Light.

### (a5) An authoring language with I/O (RAM side; the largest item of (a))

Writing nontrivial algorithms, such as matrix–vector products mod `p` or polynomial maps over
ℤ_p, as raw `XProgram`s is impractical. The code has absolute addresses and absolute jump targets,
there is no call mechanism, and correctness would be proved by stepping `XSteps`. Light has the
program logic (`Ends`/`Meets`, frames, tactics) and `emod`, but no string I/O. Two options:

- **Option A: PROG-2 as designed** (design §15c/§15d).
  - Add `inBit` and `emit` (and `coin`, for other consumers) to `Stmt`/`Exec`, with the I/O
    indices on `Exec` and `EndsIO`.
  - Make the compiler emit `List XInstr`.
  - Estimate: 1.4k–2.3k lines plus the compiler cases. This is the cleanest option, and it is what
    the design intended.
- **Option B: a load–run–emit wrapper.** It leaves Light unchanged.
  - A raw prologue copies `x` into Light memory (`μ i = x_i` for `i < |x|`; `|x|` is already
    argument 1).
  - The relocated compiled Light code follows.
  - Its verdict instructions are patched into jumps to an epilogue, which emits a memory region
    (its length taken from the result cell).
  - It needs: exec ⇒ Steps (about 40 lines), relocation of compiled code (absolute `bltz` targets)
    and the patch, and a Light-run ⇒ `HaltsWithin` theorem from `compileProgram_correct`, whose
    `Input` holds with `μ = x`, `i = |x|`, `j = 0`.
  - Estimate: 800–1,500 lines.
  - Cost: memory-loaded input uses `|x|` cells, which is fine for time but not for logspace.

Either way, the deliverable theorem has this shape:

```lean
/-- (proposed) The I/O program of a Light program halts within a constant times its cost plus the
input and output lengths, with the emitted output. -/
theorem Light.haltsWithin_ioProgram (Q : Light.Program) (p0 : ℕ) …
    (hrun : <Light run of p0 on input x, cost c, output o, within lim>) (hfit : Fits W lim …) :
    ∃ t ≤ K₀ + K₁ * (c + x.length + o.length + 1), ∃ v f,
      WordRAM.HaltsWithin (Light.ioProgram Q p0) x [] W t v o f
```

Here `K₀` and `K₁` depend on the program text only, as `startCost` and `stepsPerStep` do.

### (a6) Smaller items and conventions (G7)

- **`coin` versus coins as input.** The deterministic bridge runs with `ρ = []`, so programs
  should be `CoinFree` and read the coin slot with `rdIn`.
  - A lemma "a program with `coin` equals a coin-free program reading a coin segment of its input"
    is optional; NUPPT does not need it.
  - §15c's "coins as a second input" form for BPP is not stated anywhere.
- **Totality.** See §2 (3); `progOut` addresses it.
- **Output length.** `emit` appends exactly one bit per instruction, and the output is all emitted
  bits. Fixed-length outputs are the program's job: (a4)'s `emitBE`/`emitDoubled` and the
  `fixLen`/`decodeFin` conventions downstream.
- **Parameters.** A fixed prime schedule `p(κ)` (ruling Q-S2) is not computed by the RAM bridge.
  The algorithms must read `p` from their input (for example from public parameters) or compute
  it. This is a crypto-side design point.
- **Word-size ordering.** `W` is a function of `|z|` only. Every bound that a program proves must
  be uniform in that sense.

---

## 6. Deliverable (b): TM → word RAM

**Nothing on the branch does any part of it.**
- `Programs/` mentions no `MultiTapeTM` or `FinTM`.
- The TM-level interpreters (`TuringMachine/Universal*.lean`, `CodeSimulator.lean`) are machines
  simulating machine codes, not RAM programs.
- Upstream `Lang/Renumber.lean` (procedure relocation), deferred in design §15b, is the one piece
  that (b) needs for subroutine use.

### What (b) enables for cryptography

1. **Subroutine calls to any existing polynomial-time function.**
   - **Which functions:**
     - `ClassP/BinaryArith`;
     - the abstract `Pairing.BilinearGen.Ops` fields `mulG`, `powG`, `pairStr`, `mulT`, `memT`,
       `orderStr` (`Pairing/Operations.lean:68`), all `PolyTimeComputable` string functions with
       equational specs (`mulG_spec`, …);
     - the `Candidates.ArithmeticFP` fields (`Candidates/Arithmetic.lean:314`).
   - **How:** the RAM program builds the argument string in memory, calls the interpreter on the
     machine chosen from the `PolyTimeComputable` witness, and reads the result back. The program
     text then contains a classically chosen machine. That is fine for existence statements.
   - **PHFE needs this for its group operations.** It is the only way a RAM program can perform
     them, since they are given only by the contract.
2. **Whole-RAM reductions.** A reduction can be one RAM program that runs a fixed adversary's
   `A.M` inside it.
   - `A.advice n` is not computable, so it must come from the reduction's own advice slot, as
     `exists_handlerMachine` already arranges.
   - `A`'s coins come from a segment of the reduction's coins.
   - `NUPPT.halts` and `output_spec` (`PPT.lean:183`) give the interpreter's time hypothesis on
     every input.
   - **Caveat:** for oracle or interactive adversaries, the RAM program would re-implement T1's
     next-move loop. Its correctness with respect to
     `simulate (H.impl …) (A.toCompOn …)` would have to be re-proved; T1 does this once, as
     `EffFill.hRaw_spec`.
   - So for oracle adversaries, the TM-level handler route of §2 (4) stays cheaper. Whole-RAM
     reductions pay off for single-call adversaries and where the reduction's own computation
     needs abstract operations interleaved with the adversary's runs.

### Where the subroutine has to live

- **`XProgram` has no call mechanism.** `bltz` takes an immediate target, there is no indirect
  jump, and the Light compiler emulates returns with a dispatcher. At the `XProgram` level, (b) is
  usable only by **inlining** with jump relocation.
- **Light has calls** (`Stmt.call`, recursion, spec-only `Meets`), so (b) should be delivered as a
  **Light procedure** with a memory-to-memory interface.
- Procedures are called by absolute index, and `Ends.append` keeps proofs only for procedures
  appended *after*. So library procedures either come first in every program, or need relocation:
  (b3), porting `Renumber`.

### Proposed statement shapes

```lean
/-- (proposed; b1) A Light procedure running a finite binary machine on a bit string in memory,
with overhead linear in its running time and the input length. -/
theorem Light.exists_tmProc (M : Turing.FinTM Bool) :
    ∃ (Q : Light.Program) (p A k : ℕ), ∀ (R : Light.Program) (lim : Limits) (d : ℕ)
      (a len b sc : ℕ) (μ : ℕ → ℤ) (x out : List Bool) (t : ℕ),
      Q <+: R →  -- or the relocated form, after (b3)
      x.length = len → (∀ i < len, μ (a + i) = (x.getD i false).toNat) →
      M.ComputesInTime x out t →
      sc + A * (t + len + 1) ≤ lim.space → (A * (t + len + 1) : ℤ) ≤ lim.word →
      d + k ≤ lim.depth →
      Meets lim R p d [a, len, b, sc] μ (A * (t + len + 1)) fun r μ' =>
        r = out.length ∧ (∀ i < out.length, μ' (b + i) = (out.getD i false).toNat) ∧
        (∀ c, c < b ∨ b + out.length ≤ c → c < sc ∨ sc + A * (t + len + 1) ≤ c → μ' c = μ c)

/-- (proposed; b2) Standalone: the word RAM simulates a finite binary machine in linear time. -/
theorem WordRAM.exists_program_of_finTM (M : Turing.FinTM Bool) :
    ∃ (P : XProgram) (A : ℕ), CoinFree P ∧ ∀ (x out : List Bool) (t W : ℕ),
      M.ComputesInTime x out t → A * (Nat.log 2 (t + x.length + 2) + 1) ≤ W →
      ∃ (t' : ℕ) (v : Bool), t' ≤ A * (t + x.length + 1) ∧
        HaltsWithin P x [] W t' v out (A * (t + x.length + 1))

/-- (proposed; b2) Every polynomial-time function is computed by a polynomial-time word-RAM
program, at every word size above a logarithmic one. -/
theorem WordRAM.exists_program_of_polyTimeComputable {g : List Bool → List Bool}
    (hg : Complexity.PolyTimeComputable g) :
    ∃ (P : XProgram) (c C d : ℕ), CoinFree P ∧ ∀ (x : List Bool) (W : ℕ),
      c * Complexity.logSpace x.length ≤ W →
      ∃ (t : ℕ) (v : Bool), t ≤ C * (x.length + 1) ^ d ∧ HaltsWithin P x [] W t v (g x) (3 * t)
```

The `∀ W ≥ …` form matters: crypto programs run at polynomial `W`. Composing with (a1) gives
`PolyTimeComputable g` back, which is a sanity check of the pair.

### Design notes and size

**Encoding.**
- A blank is 0, `false` is 1 and `true` is 2. The input tape is the region at `a`, read-only, and
  blank past `len`. The output is appended at `b`.
- Work tapes are bi-infinite in head position. They need either an offset by the run's bound or two
  half-arrays per tape, since Light memory is indexed by `ℕ`.
- The state is `Fintype.equivFin`.
- The transition function is either a table in memory, written by a constant prologue generated
  from `M` (one universal interpreter verified once), or a decision tree of code per `M`. The
  table form is recommended: one proof, with a per-step cost of `O(k)` Light steps.

**Word size.** Addresses up to `sc + O(k·(t + len))` need `W ≥ log₂(t + |x|) + O(1)`. This fits
both `c·logSpace` and polynomial `W`.

**Estimates:**

| Part | Lines |
|---|---|
| (b1) encoding, table and interpreter procedure with `Meets` | 900–1,800 |
| (b1) relation to `Turing.Cfg` and the run induction | 600–1,200 |
| (b2) over (b1) and (a5) | 150–400 |
| (b3), the `Renumber` port | 300–600 |
| **Total** | **about 2,000–4,000** |

So (b) is conceptually easy, as Seyoon says. It is roughly a third of stage 2's 6–11k, and it
needs **no** TM-construction proofs and **no** `sorry`d rows.

**`sorry` dependence:** none for (b1) and (b2). They are statements about RAM and Light semantics
and TM runs. Only round trips through (a1) inherit `exists_simulation`.

---

## 7. Recommendation

**Minimal path to unblock the two jobs, in order.**

1. **(a1) and (a2)** on the RAM branch, together, as a small statements-and-proofs PR on top of
   `Classes.lean`. It carries exactly `exists_simulation`.
   - This alone already lets the crypto side prove `PolyTimeComputable` for anything written as an
     `XProgram`, and so feed every TM-level wrapper of §2 (4).
2. **(a5)**, the authoring language, after a decision between Option A (PROG-2) and Option B (the
   wrapper). Neither is in flight.
   - Recommendation: Option A if the RAM campaign wants Light I/O for its own consumers (L, NL,
     transducers); otherwise Option B, which is smaller and leaves the vendored files untouched.
3. **The generic part of (a4)** (views, `pairSplit`, big-endian fields, doubled emission), as
   Light routines with `Meets` specs, plus **(b3)**, relocation, so that library routines can be
   appended.
4. **(a3)** on the crypto side, as soon as a base has both `Randomized/PPT.lean` and the RAM layer.
   - Honest algorithms use the uniform forms of §3 only. The advice-taking form is for
     reductions only.
   - Then the sPRG job can write Eval′ and Q_I generation, and its reductions' handler pieces, in
     Light.
5. **(b1)**, as a Light procedure; then **(b2)**.
   - PHFE's KeyGen, Dec and Enc core, which need group operations, use it.
   - Until it lands, PHFE writes its ℤ_p parts as Light programs and composes group operations in
     the `PolyTimeComputable` closure algebra, as BB1's handler does today.

**Who builds what.**

| RAM campaign (library, no crypto imports) | Crypto side, on top of the RAM API |
|---|---|
| (a1) bridge and `progOut`; (a2) word sizes | (a3) `NUPPT.exists_ofProgram` |
| (a5) Light I/O (PROG-2 or the wrapper), exec ⇒ Steps, Light-run ⇒ `HaltsWithin` | Layout-specific parsers (NUPPT layout, handler inputs, group-element encodings) over the view API |
| (a4) generic views and codecs as Light routines | The algorithms (sPRG Eval′, Q_I; PHFE KeyGen, Dec, Enc core) as single uniform programs (§3), their halting bounds on every input and their correctness on well-formed inputs |
| (b1) TM interpreter procedure; (b2) standalone corollaries; (b3) `Renumber` port | Handler pieces as programs, fed to `exists_handlerMachine`/`exists_interactiveHandlerMachine`; optional whole-RAM reductions for single-call adversaries via (b1) |

**Disclosure for the crypto statements.** Efficiency theorems built this way carry `sorryAx` only
through `WordRAM.exists_simulation`. After job E, they carry it through the 15 tier-2 statements
listed in §2 (5), until jobs A–D land. They should be kept separate from the security and
correctness theorems, as the 2026-11-18 rulings require.

**Integration.** The records branch must not build on its own stale copies of the RAM files.
Those copies carry 32 admissions: Extended 18, WordSize 3, Classes 9, Simulation 2. Beside them
are `TimeConstructible`'s 2 and, in `Build/`, `Loop` 5, `Primitives` 3, `Wrappers` 2 and
`RecordTable` 4. Of these, only `RecordTable`'s 4 remain at the RAM tip. The crypto work on the bridge should start from a base that includes
`main` ≥ #364 and the RAM branch's merged PRs #370–#373.
