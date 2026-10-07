# Machine-library fill campaign — Batch L: the loop

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-L`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-L.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

This is the campaign's declared risk concentration
(`machine-library-design.md` §10): the bounded-loop combinators. The
statements went through **three adversarial audit rounds** — the original
was refuted outright (zero-step advances), the redesign was refuted at
its round domain, and the configuration-level export closed the last gap
— so the statement freeze here is as hard as it gets: **you change
nothing; a statement you cannot prove is an escalation.** The enormous
compensation: the auditors left you a construction ledger. Round-3
findings items 4–5 (`audits/ch1-infra-r3-findings.md`) specify the host
design segment by segment — controller phases, the configuration family,
the three-row segment-endpoint table, the width-based worst-case counter
estimate, the constant ledger `K = max {1, a₀, a₁+a₂+a₃}`, and the
zero-fuel and last-candidate-accepts edge cases. **Follow it**; the
round-1 item-7 realizability argument (`audits/ch1-infra-findings.md`) is
its companion for the final-answer forms.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/TuringMachine/Build/Loop.lean` — targets, in order:
  1. `Turing.loop_run` (3 pts — harvest: `enumLoop_run`,
     `ClassNP/EXP.lean:630`, is the proved template; generalize its
     induction to the arbitrary `accept` family and the
     `(List.range N).any` verdict)
  2. `Turing.FinTM.exists_loopCfgTM` (8 pts — **the construction**; the
     round-3 item-4 ledger end to end)
  3. `Turing.FinTM.exists_loopTM` (3 pts — corollary of 2 through an
     **already-halted-terminal summation lemma**, a new private lemma
     you add: induction over remaining rounds with the halted `[false]`
     terminal, the `enumLoop_run` shape; the frozen `loop_run` does
     **not** apply directly — its `hout` wants an empty-output terminal
     and the exported terminal is `[false]` (round-3 finding R3-1).
     Startup absorbs with `ComputesInTime.mono`.)
  4. `Turing.FinTM.exists_loopFindTM` (4 pts — the same host with the
     payload surfaced: the accepting round's captured output is replayed
     verbatim instead of the fixed verdict; `List.range.find?` picks the
     least accepting index because the host halts at the **first**
     accepting round)

## The construction, as the audit fixed it (binding)

- **Phases.** Distinct finite-control phases for: fuel capture (run `F`
  relocated-and-captured, lay `Nat.bits (R |x|)` on the counter tape),
  rewinds (counter head and input head — each bounded by the fuel run's
  own budget, since heads moved at most `T |x|` cells), body startup,
  active body execution (embedded via the W1 capture discipline —
  instantiate `Turing.capture_run` with your controller as host), counter
  handling, and final dispatch/emission. After releasing a seam, execute
  one body action before recognizing another anchor entry.
- **Configuration family.** `cfg i` = the host's body seam for the orbit
  word `s_i`, empty physical output, counter value `R |x| − i` in the
  same `L ≤ T |x|` cells (fixed width, high zeros retained), fuel-phase
  residue preserved.
- **Segments** (the round-3 table): acceptance at `i` → run body, detect
  the captured halt, emit `[true]`, halt. Rejection at `i < R` → body to
  `s_{i+1}`, debit the positive counter, rewind, enter `cfg (i+1)`.
  Rejection at `i = R` → last body round, **underflow of the zero
  counter belongs to this same segment**, emit `[false]`, halt at
  `cfg (R+1)`. The initial anchor entry is free (debits start at the
  second entry), so `R = 0` with `Nat.bits 0 = []` still tests `s0 x`.
- **Counter estimate** (round-3 finding R3-2, binding): per-segment
  counter work is bounded **worst-case** by the width — every debit,
  rewind, and the final underflow each cost `O(L + 1) = O(T |x| + 1)`.
  Do not argue amortization for the per-segment bound.
- **Unreachable branches.** If the last candidate accepts, the rejection
  terminal is unreachable — it may be **any** halted configuration with
  output `[false]`; configurations after an earlier acceptance need only
  their local contracts from their specified seams; `cfg` beyond the
  terminal is unconstrained.
- **Budget.** `K = max {1, a₀, a₁+a₂+a₃}` over your startup, body,
  counter, and dispatch constants gives the single exported `c`,
  uniformly; the delay-machine separation closes because an accepting
  candidate zero forces halting within `2K(T+1)`.

## Sanctioned `sorryAx`, this batch only

Batch W runs concurrently. The three combinator targets (2–4) may show
`sorryAx` **solely** through `Turing.capture_run` (the frozen, audited W1
statement your body embedding instantiates); at merge the dependency
closes. `loop_run` must be admission-free. Any other root is a defect;
verify roots by kernel-environment traversal
(`audits/programs/ch1-infra-*.lean` are the committed templates) and
report them.

## Environment and verification

As batch W: pinned toolchain, `lake exe cache get` once, **never
`lake build`**; bootstrap the 57-module order list; iterate the owned
module (position 11) plus later modules; final full 57-module fresh
sweep, zero `error:` lines. Axiom prints for all four targets: at most
the standard triple; `sorryAx` only per the sanctioned root above.

## Ground rules (binding; `workflow.md` §4 in full force)

Exclusive ownership; `private` helpers, all listed (the
already-halted-terminal summation lemma among them); **statement freeze
absolute; escalation over alteration**; docstrings stay (append-only
notes allowed, disclosed); precise imports; no out-of-scope sorries.
**18 points — continuation budget anticipated**: if exhausted, deliver a
partial zip with the frontier exact (the epoch-2 enumerator batch's
continuation report is the model — it reduced its target to one named
admitted lemma; aim for that discipline). Lint 0 FAIL; keep the file
under 1000 lines if feasible, else record the justification.

## Out-of-scope sorries you will see (leave untouched)

The 4 Wrappers and 15 Primitives contracts (concurrent batches W and P);
the three TMSAT `D-*` sites; `enumMachine_contracts`/`EXP_subset_NEXP`;
`mem_NP_iff_exists_length_le`; the `Nondeterminism.lean` cluster;
everything in `SAT.lean`, `Tautology.lean`, `CookLevin/*`.

## REPORT.md checklist

- [ ] Four targets filled in order (or the continuation frontier exact);
      a mapping from the round-3 item-4 ledger rows (phases, family,
      three segment cases, counter estimate, unreachable branches,
      constant ledger) to your discharging lemmas.
- [ ] The already-halted-terminal summation lemma named and listed.
- [ ] Base hash; all new private declarations listed.
- [ ] The sanctioned `capture_run` root called out and root-verified —
      or "unused".
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints.
- [ ] Diff touches only `Build/Loop.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (`briefs/ch2-epoch1-batchA.md`
§pitfalls), plus:
- `Cfg.ofWords` pins `inputPos = 1` and **all** heads at the origin —
  your rewinds are part of each segment, not free.
- `initCfg_ofWords` makes the machine's genuine start the empty-words
  seam; use it, don't re-derive it.
- `stateWord` puts the round word on tape 0 by a `(i : ℕ) = 0` test —
  match on the same test.
- The body's round hypothesis holds only on `Inv`-admissible words; your
  induction threads `hInv0`/`hInvStep` before every `hround` use.
- `hround`'s time witness is existential with `0 < t`; the accepting
  case may include an already-halted tail — the actual halt occurs no
  later (round-3 item 4's note).
- The fuel word never grows: fixed-width decrements retain high zeros;
  do not shrink the counter representation mid-run.
- `capture_run`'s guard is strict liveness before `t`; the halting
  endpoint itself is allowed and carries the final emission.
