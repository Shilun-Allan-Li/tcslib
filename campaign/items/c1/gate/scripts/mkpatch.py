"""Write the docstring-only patch of NTimeHierarchy.lean: every replacement is asserted to match
exactly once in the original. Read-only on the checkout."""
import os
import sys

src_path, out_path = sys.argv[1], sys.argv[2]
s = open(src_path, encoding="utf-8").read()


def rep(a, b):
    global s
    assert s.count(a) == 1, a[:80]
    s = s.replace(a, b)


# 1. Module docstring, decision 4: the quadratic belongs to timed_universal, not clockTM.
rep("""  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not the deterministic `clockTM`'s
  re-scan: the received `Turing.timed_universal` pays `C·(t+1)²` exactly
  there, and the quadratic would surrender the book-strength hierarchy.
""", """  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
""")

# 2. Module docstring: the guess-first route, declared.
rep("""* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
""", """* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`.
""")

# 3. Statement 1: the guess-first sketch (decisions 1, 3, 5; the decision-4 fix of line 110).
rep("""**Proof sketch.** Direct interpretation, not guess-then-verify: the coded
normal form has two work tapes (`Turing.CodeNDTM`), so `UN` maintains both
simulated tapes on two dedicated real tapes, holds the canonized table
(`Turing.EffectiveNDMachineCode.canonizer`) on a third, reads `x` in place by
the received virtual-input startup discipline
(`TCSlib.Complexity.TuringMachine.UniversalStartup` — no copying, so the
budget need not dominate `|x|`), and **passes its own choice bits through**:
at each simulated step boundary `UN` consumes one choice bit and applies the
corresponding table row, so `UN`'s branches at length `C·(t+1)` project onto
the coded machine's branches at length `t` (the alignment lemma, both
directions of the iff; deterministic bookkeeping steps ignore their bits, the
binary-choice semantics' absorption). The clock is the budget word `bits t`
counted **down one tick per simulated step, fused into the interpreter
loop** — not the deterministic `clockTM` re-scan, whose `C·(t+1)²` is
exactly what decision CH34-Q8 forbids — and every branch halts when the
counter dies or the simulated machine halts, whichever is first. The tick
is **amortized**, not pointwise (round-1 finding 5): a decrement from `j`
borrows across `ν₂(j)` trailing zeros, unbounded for a single tick, but
`Σ_{j≤t} ν₂(j) ≤ t`, so a counter that maintains its significant end and
tests zero without full-width scans has linear total cost. Per simulated
step the remaining cost is one table scan, `O(|table|)` — a constant for
fixed `α`, absorbed into `C`. Fill obligations, named: the startup reuse at the
ND record format; the fused countdown; the two alignment directions; the
halting absorption on exhausted budgets; the `C`-ledger per code. -/""",
"""**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`. Fill obligations, named: the startup and per-code installation;
the choice writer's bounded contract; the window copy; the interpreter core
(H1's hosted clock over the step block at three work tapes, harvested with
H2's promotion); the guess-then-run assembly; the `C`-ledger per code. -/""")

# 4. Statement 2: BF := E(UN) (decision 2).
rep("""**Proof sketch.** Enumerate the `2^t` choice words on a binary counter tape
in lexicographic order (`incrementTM` discipline); replay each word through
the deterministic core of `Turing.exists_timed_universal_NDTM`'s interpreter
— choices read from the counter instead of guessed — at cost `C_α·(t+1)` per
replay (virtual input, no copying), clearing the two simulated tapes between
replays (`O(t)` each); emit `[true]` on the first accepting replay, `[false]`
after the last. Ledger: `2^t · O_α(t+1) + 2^t` increments `≤ C·2^{C·(t+1)}`.
Fill obligations, named: the counter-driven replay loop (a §12 loop/catalog
consumer); the inter-replay cleanup; the first-accept/last-reject control;
the exponent arithmetic. -/""",
"""**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. Fill obligation, named: `E`
itself (iterative deepening over the choice words of the fixed `UN`, each
replayed by its replay machine under the step-clocked runner, with a window
clear between replays; no `|x|` term). -/""")

# 5. Statement 4 (iii): the guess-first mid-rung, the prefix clause as a contract clause.
rep("""**(iii) the self-clocked mid-rung**: for
`ℓ_i < n < ℓ_{i+1}`, `D` runs the fixed interpreter core on the virtual
input `⟨α_j, 1^{n+1}⟩` at nominal simulated budget `g n`, under `D`'s
**own fused countdown of `K·(g n + 1)` steps** — `K` fixed by `D`'s
architecture, independent of the code, **with the allowance split stated**
(round-2 finding 2): a fixed share is reserved ahead of simulation for the
one `g`-witness run (bounded by its own `c_g·(g n + 1)` clause — it runs
*before* the countdown exists and is not cut by it), for budget and
countdown preparation, and for the worst single binary borrow; the
interpreter core carries a named **prefix-bound obligation** (an accepting
simulation prefix under a larger nominal budget costs at most its own step
count times the fixed per-step constant), so the remaining share covers
the relevant branches — passing its choice bits through; branches cut by
the countdown **reject** (sound: a cut branch is non-accepting, and
completed accepting simulations are sound).""",
"""**(iii) the self-clocked mid-rung, guess first** (user decision 1 of
2026-10-13; a declared sketch deviation from passing choice bits through):
right after computing `g n`, `D` **guesses a stream of `g n` choice bits**
with the bounded choice writer (`Turing.ndWriterTM_run_block`), its only
nondeterministic phase; every later phase is deterministic. For
`ℓ_i < n < ℓ_{i+1}`, `D` materializes `⟨⟨bits (g n), α_j⟩, 1^{n+1}⟩` and
runs the deterministic interpreter core `Turing.exists_ndInterpreterCore`
on it, hosted by Z1, with the guessed stream, at nominal simulated budget
`g n`, under `D`'s **own step-clocked countdown of `K·(g n + 1)` steps**
(the step clock `Turing.exists_stepClockTMVia`, shared with the B6 hosts)
— `K` fixed by `D`'s architecture, independent of the code, **with the
allowance split stated** (round-2 finding 2): a fixed share is reserved
ahead of simulation for the one `g`-witness run (bounded by its own
`c_g·(g n + 1)` clause — it runs *before* the countdown exists and is not
cut by it), for the guess, for budget and countdown preparation, and for
the worst single binary borrow; the **prefix-bound obligation is a clause
of the core's contract**: when the simulated branch halts at `t' ≤ g n`,
the core stops within `C_α·(t' + |x| + |bits (g n)| + 1)` (here
`|x| = n + 1`, the bounded window copy of user decision 5), so the
remaining share covers the relevant branches; `D` accepts iff the core
accepts within the countdown, and branches cut by the countdown **reject**
(sound: a cut branch is non-accepting, and completed accepting simulations
are sound).""")

# 6. The mid-rung arithmetic of the chain, with the window term of the prefix clause.
rep("""late stages of `α`'s subsequence: the genuine simulation of an accepting
`N`-branch costs at most `C_α·(C₁·(c₀·f(n+1) + 1) + 1) ≤ A*·(f(n+1) + 1)`
host steps with `A* := C_α·(C₁·c₀ + C₁ + 1) + 1` **fixed**, which the
domination hypothesis (its `f(n+1)` addend) puts below `K·(g n + 1)`
eventually — so the countdown never cuts the relevant branches, and""",
"""late stages of `α`'s subsequence: by the core's prefix clause the genuine
simulation of an accepting `N`-branch costs at most
`C_α·(C₁·(c₀·f(n+1) + 1) + (n + 1) + |bits (g n)| + 1)`, which is at most
`A*·(f(n+1) + n + 1) + C_α·|bits (g n)|` host steps with
`A* := C_α·(C₁·c₀ + C₁ + 2) + 1` **fixed**, and the domination hypothesis
(its `f(n+1)` and `n + 1` addends; the logarithmic term is `o(g n)`) puts
that below `K·(g n + 1)` eventually — so the countdown never cuts the
relevant branches, and""")

# 7. Statement 4's named fill obligations.
rep("""locator with its amortized ledger; the self-clocked interpreter core at
fixed `K`; the two transfer instantiations""",
"""locator with its amortized ledger; the guess and the step-clocked
interpreter core at fixed `K`; the two transfer instantiations""")

# 8. Rewrap the one pre-existing line over 100 characters (sketch (ii)); no word changes.
rep("""an explicit recurrence over `f`'s constructibility witness; the locator compares `n` against `ℓ_{i+1}` by
**bit-length arithmetic with capped witness runs** (the ladder value is
""", """an explicit recurrence over `f`'s constructibility witness; the locator
compares `n` against `ℓ_{i+1}` by **bit-length arithmetic with capped
witness runs** (the ladder value is
""")

open(out_path, "w", encoding="utf-8").write(s)
print("patched copy written")
