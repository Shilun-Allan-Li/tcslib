# External audit pack — Chapter 3, phase P3.3 (NDTM codes, the linear-overhead universal, the nondeterministic time hierarchy), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P3.3 — codes for nondeterministic machines with their representation-scheme
laws, the clocked universal NDTM of [AB09, Exercise 2.6] at **linear
overhead** (decision CH34-Q8), the exponential deterministic evaluation of
nondeterministic acceptance, the linear-overhead coded normal form, and the
nondeterministic time hierarchy theorem ([AB09, Theorem 3.2]) **at book
strength** with its positive-bound form and a showcase instance. Statement
phase per `workflow.md` §2-3; the gate closes on a round with zero blockers
and zero majors.

Audited at commit `a664c3e4` (branch `complexity/arora-barak-ch3-4`); the two
files under audit are byte-identical to their landing commit `72718693`
(verify:
`git diff 72718693 a664c3e4 -- TCSlib/Complexity/TuringMachine/NDCodes.lean TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`
is empty). Under audit: `TCSlib/Complexity/TuringMachine/NDCodes.lean` and
`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean` — **7 sorried
statements (NDCodes 1, NTimeHierarchy 6), 7 definitions**
(`Turing.CodeNDTM`, `CodeNDTM.toFinNDTM`, `Turing.workPair`,
`Turing.actionBits₂`, `CodeNDTM.serialize`, `Turing.NDMachineCode`,
`Turing.EffectiveNDMachineCode`), **and one skeleton-time proof**
(`Turing.NDMachineCode.decode_encode`, a three-line mirror of the proved
`Turing.MachineCode.decode_encode` — declared part of the audited surface,
the `runWith`-algebra precedent of `workflow.md` §2).

**Layering.** This phase sits on **closed surfaces only**: the chapter-1
code-and-universal layer (`TuringMachine/Encoding.lean`'s `CodeTM`,
`MachineCode`/`EffectiveMachineCode`, the serialization fields, and
`Turing.universal`/`timed_universal`; `MathlibBridge.lean`'s proved
`exists_effectiveMachineCode`; `CodeParser.lean`), the chapter-2 NDTM and
`NTIME` layers (`Nondeterministic.lean`, `ClassNP/NTIME.lean`:
`AcceptsWithin`, `HaltsWithin`, `DecidesInTime`), `TimeConstructible`, and
the P0-received deterministic hierarchy surface
(`audits/ch34-p0-resolutions.md`: `TimeHierarchy/{Diagonal,CodePrefix,Separation}.lean`).
**No sorried statement of any concurrent round is consumed by a statement
here.** Concurrent rounds touch this phase only as declared fill engines in
sketches: the §12 routine layer (`audits/routine-infra-pack.md` —
`incrementTM` discipline, the loop combinator, W1 capture), cited for fills,
never for statements. Also live and disjoint: P3.2 (which freezes the
`Diagonalization.lean` facade — hence this phase is **root-wired** through
two temporary imports in `TCSlib.lean`, attached; the `TuringMachine.lean`
facade is untouched; facade wiring lands at the respective gate closes, the
P4.2 precedent) and P4.3 round 2 (disjoint files). The truncation argument
cited by deviation 6 below was independently confirmed by the closed P4.2
round (`audits/ch4-p42-resolutions.md`, attached).

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **a universal or normal-form statement whose
quantifier order or budget shape silently surrenders the linear overhead**
(the `C`-after-`α` order and the fused clock are the entire point of
decision CH34-Q8 — a quadratic slip reduces Theorem 3.2 below book
strength), and **a hierarchy hypothesis that is not the book's
`f(n+1) = o(g(n))`** (too strong: the theorem weakens; too weak: the lazy
diagonalization cannot pay for its stage tops). Blind restatements for all 7
definitions; a line-by-line verification of the one skeleton-time proof;
true-as-stated arguments for all 7 sorried statements; at least
**5 adversarial instantiations**; no blanket approvals. Sources: [AB09]
§1.4 (the code-scheme laws), §2.1.2 and Exercise 2.6 (the universal NDTM),
§3.2 (Theorem 3.2, Figure 3.1, the lazy-diagonalization proof, pp. 69-71);
[Coo72] and [BGW70] are cited through [AB09] — no external text is required
for this audit.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p33-sweep.log`, revision recorded at
  start: `a664c3e4`): both modules, 0 `error:` lines, fresh `.olean`s,
  exactly **7** `declaration uses 'sorry'` warnings (NDCodes 1,
  NTimeHierarchy 6). No facade is touched by this phase, so none is swept
  (the sweep-hygiene rule binds only touched facades).
* Style lint (`audits/logs/ch3-p33-stylelint.log`): `Diagonalization`
  0 FAIL / 0 WARN over 4 files; `TuringMachine` 0 FAIL over 39 files with
  only the 8 pre-existing size WARNs (unchanged from before this phase;
  `NDCodes.lean` adds none — its lint row: 185 lines, 9 public / 0 private
  declarations; `NTimeHierarchy.lean`: 278 lines, 6 public / 0 private).
* Declaration inventory, counted programmatically: 9 public declarations in
  `NDCodes.lean` (7 definitions + 2 theorems, one proved), 6 in
  `NTimeHierarchy.lean` (all sorried theorems).
* Statement-freeze baseline: commit `a664c3e4`.
* Drafting provenance: maintainer-drafted; landing commit `72718693` (the
  files under audit are that commit's, unchanged).

## Known deviations and design decisions (declared — verify each, flag others)

1. **The coded normal form has two work tapes** (`NDTM 2 Bool`), not the
   deterministic `CodeTM`'s one: the [BGW70]-style guess-then-verify
   reduction is linear into **two** tapes (display tape + replay tape), and
   a one-work-tape target is not known to suffice at linear overhead.
   Deterministically the one-tape form was acceptable because the chapter-1
   conversion eats a quadratic slowdown anyway; here linear overhead is the
   point (CH34-Q8).
2. **The serialization mirrors `Turing.CodeTM.serialize` record for
   record** — the same `signBits`/`optOptBoolBits`/`optBoolBits`/
   `optStateBits` fields, a second work-tape record per action
   (`actionBits₂`), the table enumerated with the choice bit outermost
   (`false` then `true`), then states in `Fin` order, then the input read
   and the two work reads each over `none`, `some false`, `some true`
   (2 · 27 records per state).
3. **The scheme laws are verbatim mirrors** (total decode; recovery under
   arbitrary `true`-padding — the property the lazy diagonalization uses to
   pick large indices; the canonizer targets the scheme-independent
   `CodeNDTM.serialize`, inheriting the chapter-1 audit's Argument-A
   exclusion by construction). `NDMachineCode.decode_encode` is proved at
   skeleton time (mirror of proved infrastructure, declared above).
4. **The universal is iff-packaged with an unconditional clock**: on every
   budget-shaped input, all-branch halting within `C·(t+1)` **and**
   acceptance iff the coded machine accepts within `t`. [AB09]'s step 1
   says "if `M_i` has not halted in this time, halt and accept"; under the
   contradiction's budget assumption the timeout polarity never bites — the
   packaging is a simplification, not a strengthening (declared in the
   module docstring).
5. **Linear overhead `C·(t+1)` with `C` per code** (CH34-Q8): the clock is
   fused into the interpreter loop — one countdown tick per simulated
   step — not the deterministic `clockTM` re-scan; the received
   `Turing.timed_universal` pays `C·(t+1)²` exactly there (attached for
   contrast), while the received *unclocked* `Turing.universal` is already
   linear. The budget carries **no `|x|` term**: the virtual-input startup
   reads only the `⟨bits t, α⟩` prefix, and a `t`-step run visits at most
   `t` input cells.
6. **The normal-form transfer's backward direction is deliberately
   unbounded** (`∃ t'`): runaway guessing branches never accept, and no
   all-branch-halting claim is made for the simulator. The hierarchy
   recovers the budgeted form from the assumed decider's own all-branch
   halting by truncation (`Turing.NDTM.runWith_of_halt` — the argument the
   closed P4.2 round confirmed for the packaged-iff backward direction).
7. **The domination hypothesis carries an extra `f n` addend**:
   `∀ A, ∃ N, ∀ n ≥ N, A·(f(n+1) + f n + n + 1) ≤ g n`. The `f(n+1)` term
   is the book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion
   half `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (for
   monotone `f` it is absorbed, so no strength is lost against [AB09]); the
   `n + 1` term covers linear startup and virtual-input costs.
8. **The larger class is `NTIME (g + 1)`**, as in the received
   deterministic `Complexity.time_hierarchy`; `ntime_hierarchy_of_pos`
   recovers `NTIME g` for never-vanishing `g` by the same absorption.
9. **The showcase instance is `NTIME(n+1) ⊊ NTIME((n+1)²)`** — the
   ℕ-rendering of the book's displayed `NTIME(n) ⊊ NTIME(n^{1.5})`
   (fractional exponents have no normal form in the campaign); its
   docstring records that the received deterministic hierarchy's quadratic
   overhead provably cannot deliver this instance (`A·(2n+2)² ≤ (n+1)²`
   fails for every `A ≥ 1`), so the linear-overhead universal is
   load-bearing. Its two constructibility witnesses are named fill
   obligations (an input-scan counter for `bits (n+1)`; a grade-school
   square for `bits ((n+1)²)`).
10. **The exponential evaluator's budget is `C · 2^{C·(t+1)}`**, again with
    no `|x|` term (each of the `2^t` replays is cut at exactly `t`
    simulated steps over the virtual input, halting or not, with
    fixed-bank cleanup between replays).

## Specific questions (prioritized)

1. **The coded carrier and its serialization**: blind-restate `CodeNDTM`,
   `workPair`, `actionBits₂`, and `CodeNDTM.serialize`. Check `actionBits₂`
   against the deterministic `actionBits` field by field (one extra
   work-tape record, same field order), the `workPair` tape order against
   the two records' order (tape `0`'s read is the `if j = 0` branch — is
   the serialized table's `(w₀, w₁)` enumeration consistent with how
   `tr` consumes `workPair w₀ w₁`?), and the fixed enumeration (choice
   outermost; 2·27 records per state; `unaryFin q₀` self-delimiting against
   the table, as in the deterministic precedent). Is the two-work-tape
   choice (deviation 1) the right normal form for the phase's three
   consumers?
2. **The scheme structures**: are `NDMachineCode`'s three laws exactly the
   [AB09, §1.4] properties (total decode; `true`-padding recovery), and
   does the Argument-A rationale for the scheme-independent canonizer
   target transfer verbatim to the ND setting? Verify the skeleton-time
   proof of `NDMachineCode.decode_encode` line by line.
3. **`exists_effectiveNDMachineCode`** — true as stated? The sketch reuses
   the chapter-1 parser architecture (`CodeParser`, attached) at the
   extended record format with the single-state do-nothing fallback and
   end-marker pad tolerance; the proved deterministic
   `exists_effectiveMachineCode` (`MathlibBridge.lean`, attached) is the
   mirror target. Flag anything in the ND format (the choice-indexed
   double table, the second work record) that breaks the mirror.
4. **`exists_timed_universal_NDTM` — the CH34-Q8 deliverable**:
   blind-restate both clauses. Check the `C`-after-`α` quantifier order
   (per-code constants, nothing per-input); the **unconditional**
   `HaltsWithin` clause at `C·(t+1)`; the acceptance iff between budget
   `C·(t+1)` and budget `t` — the choice-word alignment must deliver both
   directions despite `AcceptsWithin`'s exact-length words (padding
   absorbs the slack; deterministic bookkeeping steps ignore their bits).
   Adversarial: `t = 0` (no genuine initial configuration is accepting —
   the closed P4.2 round's A3 — so the universal must *reject* within `C`
   while still halting all branches); junk codes (`decode` is total — the
   clauses bind the fallback machine too); huge `|x|` against small `t`
   (deviation 5's no-`|x|` claim: can the startup really avoid scanning
   `x` under the attached `pairEncode` layout?).
5. **`exists_ndAcceptsWithin_decider`**: the two-clause deterministic form
   and the `C · 2^{C·(t+1)}` ledger (deviation 10) — `2^t` replays, each
   cut at exactly `t` steps (no waiting for halts — branches that diverge
   within `t` must not stall the enumeration), counter increments, and
   inter-replay cleanup. Is the no-`|x|` exponent sound? `t = 0` (one
   replay of the empty word).
6. **`FinNDTM.exists_codeNDTM_accepts_linear`** — the [BGW70]-style
   normal form: the display format with its **on-the-fly control check**
   (only reads are non-local), the `k + 1` verification sweeps (input
   replay; tape `j` replayed on tape B at unit cost per step), the
   `O_N(k·t)` ledger into `C·(t+1)`, and the two transfer directions —
   forward with the explicit constant, **backward unbounded** (deviation
   6): confirm the weak backward direction suffices for the hierarchy's
   chain given the assumed decider's all-branch halting (the truncation
   step, spelled in `ntime_hierarchy`'s sketch). Adversarial: `k = 0`
   machines (no work tapes — degenerate sweeps); `x = []`.
7. **`ntime_hierarchy` — the summit**: is the hypothesis (deviation 7)
   equivalent to the book's `f(n+1) = o(g(n))` for monotone `f`, and
   correctly stronger-only-in-form otherwise? Work the lazy-diagonalization
   sketch: the stage ladder `ℓ_{i+1} := BFbound(ℓ_i) + ℓ_i + 1` with the
   top-rung affordability `BFbound(ℓ_i) ≤ ℓ_{i+1} ≤ n ≤ g n` **through
   constructibility's floor `n ≤ g n`** — check that inequality chain; the
   ladder locator within `O(g n)`; the unranking `α_i` with the
   `decode_encode_pad` padding trick to pick a large index; the chain
   (3.3)/(3.4) with the truncation step; `D`'s totality from the
   universal's unconditional clock plus the evaluator's determinism; the
   inclusion half from the `f n` addend with finite absorption. Adversarial:
   `f = g` (the hypothesis must fail); `g 0 = 0` is impossible under
   `TimeConstructible` — check the `g + 1` seam anyway, as in the
   deterministic precedent.
8. **The positive form and the showcase**: `ntime_hierarchy_of_pos`'s
   absorption mirror; `NTIME_linear_ssubset_square`'s domination
   (`A·(3n+4) ≤ (n+1)²` eventually), its two named constructibility
   obligations (do they fit `TimeConstructible`'s `c·(T+1)` budget?), and
   the deviation-9 impossibility note against the deterministic route —
   verify the arithmetic `A·(2n+2)² ≤ (n+1)²` fails for every `A ≥ 1`.

Adversarial instantiations to attempt: `t = 0` through both universal
clauses and the evaluator; `α = []` and `α = [true]` through every
scheme-consuming statement; `x = []` throughout; a `k = 0` machine through
the normal form; the immediate-accept one-state machine through the
universal at `t = 0` versus `t = 1`; `f = id, g = fun n => 2 ^ n` through
`ntime_hierarchy` (both witnesses exist on the received surface —
`timeConstructible_id`, `timeConstructible_two_pow`); `f = g`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p33-findings.md`; the gate closes on zero blockers and majors.
