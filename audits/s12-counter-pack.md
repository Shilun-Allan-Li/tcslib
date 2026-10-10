# External audit pack — §12.7 counter-driven loops (statement gate)

**Surface under audit:** the new file
`TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`.
- **13 definitions** (one of them an inductive type): `Action.mapWorkSymbols`, `Cfg.mapWorkSymbols`,
  `MultiTapeTM.mapWorkSymbols`, `decFixed`, `decrementTM`, `counterWord`,
  `counterOverhead`, `CounterLoopState` (with its `DecidableEq` and
  `Fintype` instances), `counterLoopRedirect`, `counterLoopDecExit`,
  `counterLoopTM`, `counterLoopCfg` and `counterLoopOrbit`.
- **10 sorried theorems:** `MultiTapeTM.mapWorkSymbols_runFrom`,
  `decrementTM_run_succ_ofCfg`, `decrementTM_run_underflow_ofCfg`,
  `counterWord_length`, `counterWord_value`, `counterOverhead_le_of_le`,
  `counterOverhead_le`, `counterLoopTM_run_done`,
  `counterLoopTM_run_escape` and `counterLoop_time_le`.

All names are in namespace `Turing`. No existing file changes. Record
findings in `audits/s12-counter-findings.md`. **The gate closes on zero
blockers and zero majors**, which commissions the fill batch.

## Why these exist

ZF-B3's agent (`audits/zone-agent-reports/f1-B3-REPORT.md` and
`f1-B3-CONTINUATION.md`, attached) stopped on two shared-interface requests:

- a public fixed-width **decrement** with a framed contract;
- a loop whose number of rounds is a **binary counter on a tape**, over
  **persistent** body tapes.

Every existing public loop host (`Build/Loop.lean`) runs a number of rounds
fixed by the input's length, between canonical `Cfg.ofWords` seams. The same
pattern is also needed by `Diagonalization/EXPCOM.lean`,
`Diagonalization/NTimeHierarchy.lean` (a fused countdown at **linear**
overhead) and `SpaceComplexity/Hierarchy.lean`, all attached. The design is
`machine-library-design.md` §12.7 (attached). It records the user's six
decisions:

1. a dedicated counter tape;
2. two live exits, `done` and `escape`;
3. an exact per-round cost function `τ` of the round's starting
   configuration, with a uniform bound as a corollary;
4. decrement by symbol-complement transport, never by copying increment's
   proof;
5. a new file;
6. an amortized whole-run total.

## The construction (verify against the definitions)

- **Symbol transport.** `M.mapWorkSymbols e` reads the work tapes through
  `e.symm` and writes through `e`. The input tape and the output are not
  renamed.
- **Decrement.** `decrementTM k i` is `incrementTM k i` conjugated by
  `Equiv.boolNot`, and `decFixed` is its word function. The verdict is in the
  exit anchor: `done true` for success, `done false` for underflow, which
  leaves the word all `true`.
- **The host.** `counterLoopTM M a exit` has `k + 1` tapes: the body's `k`
  tapes are embedded by R1 (`embedEmitTM` along `Fin.castSucc`), and the
  counter is the last tape. Its states are `CounterLoopState S`.
  - It starts in `dec .run`.
  - A body transition into the anchor `a` goes to `dec .run`, and one into
    `exit` goes to `escape`; `a` is checked first. Every other body state is
    kept.
  - A decrement transition into `done true` goes to `body a`, and one into
    `done false` goes to `done`.
  - There are **no dispatch steps**. Both exits are stationary self-loops.
- **Host configurations.** `counterLoopCfg q c ct cp` is the R1 transport of
  the body configuration `c`, with the counter tape `ct` and head `cp` as the
  ambient frame and host state `q`. The field `c.state` is ignored.
- **The orbit.** `counterLoopOrbit M τ c r` iterates `c ↦ M.runFrom c (τ c)`.
- **Counter arithmetic.** `counterWord w r` is the counter after `r`
  decrements, and `counterOverhead w r` is the exact cost of the first `r`
  decrements, `Σ (2·|takeWhile not| + 2)`.

## Specific questions

1. **Truth at every boundary.** Attempt at least three adversarial
   instantiations per theorem. In particular:
   - an empty counter, an all-`false` counter (`d = 0`: immediate
     underflow, final body part `c` itself, whatever `c.state` is), and
     `q = 0` and `q = |w| − 1` for the decrement;
   - negative counter and body coordinates;
   - one-step rounds (`τ = 1`);
   - `exit = some a`, and `exit = none`;
   - a body that moves the input head or emits;
   - escape at the last allowed round, `r₀ = value − 1`.
2. **Hypotheses: necessary and sufficient.** For each conjunct of `hround`,
   and for `hea` and `hr₀` in the escape theorem, give a counterexample when
   it is dropped, or show it is redundant. Is anything missing? For example,
   the body cannot touch the counter tape by construction, and
   `counterLoopCfg` ignores `c.state`.
3. **Exactness of time.** Verify the total from the transition tables: the
   round times plus `counterOverhead w (d + 1)` in the returning case, and
   `r₀ + 1` round times plus `counterOverhead w (r₀ + 1)` in the escape case.
   Is the redirection really free, with no off-by-one at the seams between a
   round and its decrement?
4. **The finish configurations.** In the returning case, is the counter
   window all `true` and the counter head at `cp`? In the escape case, does
   the window hold `counterWord w (r₀ + 1)`? Are the body part, input
   position and output exactly the orbit's? Note that `embedEmitCfg` with
   prefix `[]` sets the host output to the body's output.
5. **The trajectory clauses.** Is the body-head clause right at every time,
   including during decrements, where the body heads should equal the
   round's start configuration? Is it the clause a space consumer needs, or
   should a `spaceUsedByTape` corollary be stated now?
6. **Amortized bounds.** Are `counterOverhead_le_of_le` (`4r + 2|w|` for `r`
   at most the value) and `counterOverhead_le` (`4d + 2|w| + 2`) true? The
   sketches use Legendre and Kummer. Is the uniform corollary
   `counterLoop_time_le` stated at the right strength?
7. **Symbol transport and decrement.** Is `mapWorkSymbols_runFrom` true for
   every equivalence and every configuration? Do the two decrement contracts
   follow from the audited §12.6 increment contracts by it, as the sketches
   claim? Are they the exact mirrors of those contracts?
8. **Fitness for the consumers.** Can each attached consumer be built on
   these contracts?
   - **Two-tape uniform scheme:** one simulated step per round, a cost
     depending on the code and the configuration, and the exit at a
     simulated halt.
   - **EXPCOM:** the same.
   - **NTIME hierarchy:** linear overhead, so is about 4 steps per tick plus
     one counter sweep enough?
   - **Space hierarchy:** a configuration-count clock.

   Do the two live exits compose with `seamCompTM_run_ofCfg` (`Build/Seam.lean`,
   attached), whose first-return cut is the no-earlier-exit clause? Name any
   missing contract, for example a `FinTM` wrapper or a canonical
   specialization.
9. **Duplication (TEMPLATE failure mode 5).** Does any new declaration copy
   existing material?
   - Private clocks already exist: Loop's fuel debit, Catalog's
     `f2_loopDebitTM`, and Universal's `timedUniversalTM`. These are 12.2c
     item 12, re-derivation targets for this host, not inputs to it.
   - `decrementTM` is defined by conjugation, with no table copy.
   - The counter value is Mathlib's `Nat.ofDigits 2 (w.map Bool.toNat)`,
     written inline. The same expression appears as the definition
     `BoolCircuit.bitsVal` in `CircuitComplexity/Adder.lean`, outside this
     closure; no new value function is defined.

## Repository-side attestations (verify or challenge)

- **Elaboration.** `Build/CounterLoop` elaborates via
  `scripts/lean_check_tree.sh` with exactly the 10 `sorry` warnings and no
  errors. Lint reports 0 FAIL. Nothing imports the file yet, and like
  `Build/Zone.lean` it is not in the `TuringMachine` facade during the
  statement phase.
- **Executed check.** The attached `audits/evidence/s12-counter/` harness and
  results evaluate every theorem on concrete machines and configurations:
  - symbol transport over five catalog machines and an echo machine that
    moves the input and emits;
  - the decrement contracts over all 63 words of length at most 5, at three
    head positions, with a nonblank frame;
  - the counter arithmetic over all words of length at most 8;
  - the host over a body with configuration-dependent rounds (3, 4, 6, 8,
    10 steps), counters of values 0 to 7 at three placements, and an
    exit-at-round-2 body.

  It checks each theorem's hypotheses and every conclusion clause, including
  exact final configurations, no-earlier-exit, the counter-head range and the
  body-head trajectory. All pass, and four negative controls fail as
  expected. This is evidence, not proof.

## Brief for the auditor

Audit the definitions and the ten statements, not tactic scripts. Hunt
infidelity, vacuity, and missing or excess hypotheses. Blind-restate each
statement before reading its docstring. Report in the standard findings table
(blocker / major / minor / note). Justify an empty table with your
restatements and adversarial instantiations.
