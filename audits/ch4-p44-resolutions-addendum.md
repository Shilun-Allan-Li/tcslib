# Chapter 4, phase P4.4 — resolutions addendum: B7 route changes (statement mini-phase P4.4b)

**Status: OPEN for the P4.4b statement gate (2026-10-11; user-approved restructure).** This
addendum supplements `audits/ch4-p44-resolutions.md`. It changes no P4.4 statement. Two proof
routes change, the sketch prose of two declarations is corrected, and seven new sorried
statements are added for gating.

## Why

Plan §4e listed cluster B7 as "unblocked via the received `LogProg` layer". The pre-issue
review of B7 found this false for `comp`, `mem_LOGSPACE_of_logspaceReducible` (by its binding
route) and `multLang_mem_LOGSPACE`. The received layer has two deterministic gaps:

- **G1, no oracle-served virtual input.** A call's virtual input is read physically: the whole
  host input, or its leading run of `1`s, followed by register words (`Machines/Program.lean`,
  `Mode`). No call can serve a decider's input symbols through further calls. The P0 reception
  record already says so: `audits/ch34-p0-findings.md` note 10, and its line 184, "general
  implicit composition remain[s] real work".
- **G2, no random access to a general input.** The input instructions of `LogProg.ARM`
  presuppose `⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩` (`Machines/ARM.lean:72–82`).

## Route change 1 — `Complexity.mem_LOGSPACE_of_logspaceReducible` (T3)

- **Was:** the sketch, as amended by resolutions minors 1–2.
  - `χ_C` is implicitly logspace computable;
  - `χ_C ∘ f` is too, by `comp`;
  - specialize its bit query at index `0`.
- **Problem:** `χ_C`'s bit language is `{pairEncode x [] | x ∈ C}`. Deciding it runs `C`'s
  decider on the undoubled first component of the host, which is itself an instance of G1. So
  the route needs the engine twice, and `comp` as well.
- **Now:** `obtain ⟨f, hf, hB⟩ := h`, then `Set.ext hB`, then
  `Complexity.mem_LOGSPACE_preimage hf hC`. The engine runs once: the oracle-input simulator
  `Complexity.LogProg.OIS` of `Logspace/PreimageHost.lean`, which is [AB09, Fig. 4.3]'s
  construction.
- **Finding 2's circularity rule is kept.** The engine cites nothing from `Reductions`.

## Route change 2 — `Complexity.ImplicitlyLogspaceComputable.comp` (T1)

- **Was:** run `g`'s query machine on a virtual input served by `f`'s queries "via the
  received call protocol". G1 and G2 block this.
- **Now:**
  - Both query languages of `g ∘ f` are preimages of `g`'s along `Complexity.compQ f`
    (`⟨x, bits i⟩ ↦ ⟨f x, bits i⟩`, malformed queries ↦ `[]`). This is
    `Complexity.mem_indexLang_compQ_iff`, proved.
  - Hence both are in `L` by `mem_LOGSPACE_preimage` together with
    `Complexity.ImplicitlyLogspaceComputable.compQ`.
  - The composite bound is question 2's `D (C + 1)^d (|x| + 1)^{cd}`.
  - This is the same Fig. 4.3 simulation, factored once through the engine.
- **Where question 2's ledger now lives.** Note 3 is carried verbatim into `compQ`'s
  machine:
  - malformed-query rejection;
  - index-length and overflow handling before a value is stored;
  - the paired layout;
  - the length boundary test.
- **How that machine queries `f`.** Its host is `⟨⟨x, bits i⟩, bits p⟩`, so it reaches `f` at
  `⟨x, bits j⟩` through the twice-lifted languages `{z | dropIdx (dropIdx z) ∈ ·}`.

## Unchanged

- All five B7 statements; the routes of `trans` (T2) and of
  `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` (T5).
- `multLang_mem_LOGSPACE`'s route (audit question 8). Only its input reading is new: an ARM
  reads the input through `whole`-mode calls to `Complexity.inputBitLang` and
  `Complexity.inputLenLang`.
- T5 needs no nondeterministic construction.

## New statements for the P4.4b gate (seven sorried)

| Statement | File | Role |
|---|---|---|
| `Complexity.LogProg.readIn_run` | `Logspace/InputAccess.lean` | program fragment: read input bit `i` (index in binary on a register) into the control state; registers restored; space independent of `i` |
| `Complexity.implicitlyLogspaceComputable_id` (N1) | `Logspace/InputAccess.lean` | input random access in `L`; stated as the corollary of `readIn_run` |
| `Complexity.LogProg.OIS.run` | `Logspace/PreimageHost.lean` | the simulator's run contract against any truthful oracle |
| `Complexity.LogProg.OIS.compile_decides` | `Logspace/PreimageHost.lean` | its space contract, compiled against a two-decider bank |
| `Complexity.mem_LOGSPACE_preimage` (N2) | `Logspace/PreimageHost.lean` | logspace preimages; stated as the corollary of `compile_decides` |
| `Complexity.implicitlyLogspaceComputable_dropIdx` (N3) | `Logspace/QueryReshape.lean` | index dropping |
| `Complexity.ImplicitlyLogspaceComputable.compQ` (N4) | `Logspace/QueryReshape.lean` | `comp`'s query reshaping |

**Definitions:**
- `LogProg.RdPh` and `LogProg.readTr` (the fragment's transition table, from received actions
  only);
- the `LogProg.OIS` program: `Ph`, `nextPh`, `liftAct`, `tr`, `call`, `prog`, `start`, `lo`,
  `hi`;
- `inputBitLang`, `inputLenLang`, `dropIdx`, `compQ`.

**Proved helpers:** `pairEncode_ne_nil`, `indicator_indexLang_pairEncode`,
`LogProg.vword_whole₁`, `dropIdx_pairEncode`, `dropIdx_length_le`, `compQ_pairEncode`,
`mem_indexLang_compQ_iff`, `compQ_length_le`. Two corollaries are proved modulo N1:
`inputBitLang_mem` and `inputLenLang_mem`.

**Pre-ship probe:** `audits/evidence/b7/B7StatementsProbe.lean.txt` (output `.out`). It has
0 errors. It exercises the fragment and the simulator on concrete instances, and it derives T2,
T3, T5 and `comp` from the contracts.

## Sketch-prose corrections (decision D5; statements unchanged)

- **`comp`** (`Reductions`): the claim that the received layer "is built for exactly this
  shape" is replaced by the gap statement and the route above.
- **`multLang_mem_LOGSPACE`** (`Mult`):
  - the claim that `Machines/Parse2`/`ParseCmp` read `⟨u, ⟨v, w⟩⟩` is replaced by the input
    access route;
  - "accept at the simultaneous end" becomes question 8's acceptance condition: all columns
    through `|a| + |b|`, missing result bits read as `0`, no remaining carry;
  - `arm_decides` becomes `arm_decides_poly`.

## Questions for the gate

1. **`readIn_run`.** Are the head range `[-1, |bits (|x| + 1)|]` and the frame clause right?
   The frame clause says only the counter's tape and the two heads change, and that the
   output and the other registers are untouched.
2. **`OIS.run`.**
   - Are the oracle laws needed only on genuine queries, for length at `i ≤ |v|` and for bit at
     `i < |v|`?
   - Is the work-register range `[-S, S]` right, with `S` the space up to `t` rather than up
     to the first halt?
3. **`OIS.nextPh`.** Does the clamped-move table match `Turing.moveInputPos` at both
   boundaries, including `v = []`?
4. **`OIS.compile_decides`.** Should the hypothesis `B` (over `i ≤ |v|`, all `j`) be
   replaced by monotone space functions?
5. **N1's form.** N1 is stated as `ImplicitlyLogspaceComputable id`, not as the two
   memberships. Is that acceptable?
6. **T3's sketch.** It still describes the superseded `χ_C` route. Correct it now, or leave a
   flagged appendix at the fill?
7. **Namespaces.** Campaign files add to `Complexity.LogProg`; this is policy §1's
   area-local root. Is that acceptable?
