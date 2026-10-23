#!/usr/bin/env python3
"""Draft maintainer landing edits (docstrings only), every replacement asserted unique.

usage: landing_edits.py <head CodeSimulator.lean> <out file> <out diff> [--with-labels]
  L1  module header: the stale "Status update ... partial" bullet -> the current status
  L2  exists_polyCanonizer's docstring: the "(spec, fill pending ...)" tag and the seven
      "Fill appendix" paragraphs -> one "Implementation." paragraph (continuation 5's
      escalation recorded as resolved by the fresh-anchor adapter)
  L3  exists_canonGrammarStage's docstring: an "Implementation." paragraph (the route taken)
  L4  (--with-labels) the new privates' docstrings: campaign labels ("checkpoint N") removed,
      and canonStageRoundSpec's stale claim about the generic link corrected
"""
import difflib, sys

src, out, dif = sys.argv[1:4]
labels = '--with-labels' in sys.argv
t = open(src, encoding='utf-8').read()
orig = t


def rep(old, new):
    global t
    n = t.count(old)
    assert n == 1, (n, old[:80])
    t = t.replace(old, new)


# L1 -------------------------------------------------------------------------------------
a = t.index('* **Status update (fills-8, 2026-10-13; H2-M, 2026-10-14): partial.** The two')
b = t.index('  nested-input startup, canonizer installation and joint ledger.\n') + len(
    '  nested-input startup, canonizer installation and joint ledger.\n')
assert t.count('* **Status update (fills-8') == 1
L1 = """* **Status.** The canonizer `Turing.MachineFormat.exists_polyCanonizer` is proved, with
  no admission. A validator (`exists_canonDecider`) runs the two-port parse front end
  (`exists_canonParseFront`: header validity, canonicality and the binary length guard) and
  the grammar stage (`exists_canonGrammarStage`) on one bank and emits one verdict bit; the
  strip machine (`exists_canonStripTM`) or the constant fallback follows. The grammar stage
  checks the unary initial state against the header (the bounded unary reader
  `exists_canonUnaryTM`), runs two nested public counter loops, over `n + 1` states and
  `3^(k+1)` records each, on the fresh-anchor record round (`canonReturnAdapter` around the
  record validator `exists_canonRecordTM`), and tests the all-`true` suffix; its time is
  quadratic in the input length and independent of the header's value.
  The uniform simulator `Turing.MachineFormat.exists_uniformSimulator` is still admitted.
  Proved for it so far: the complete generic step block `Turing.StepBlock.roundTM` of
  `Build/StepBlock`, one finite machine per work-tape count `k` whose control is independent
  of the coded state count, with its exact time bound and head envelope
  (`Turing.StepBlock.roundTM_effect`); and the binary deadline clock around it, hosted on the
  virtual input, with its one-bit verdict (`h1HostedVerdict_accepts`), the clock being the
  public loop `Turing.StepBlock.hostedLoopTM_run` of `Build/StepBlockLoop`. Open: the
  simulator's nested-input startup, canonizer installation and joint ledger.
"""
t = t[:a] + L1 + t[b:]

# L2 -------------------------------------------------------------------------------------
rep('/-- **A polynomial-time canonizer** (spec, fill pending — batch B5a): one finite\n',
    '/-- **A polynomial-time canonizer**: one finite\n')
a = t.index('\n\n**Fill appendix (B5a partial).** The positive grammar bound')
end_marker = 'therefore remains pending on the complete canonizer. The headline glue is unchanged. -/'
b = t.index(end_marker) + len(end_marker)
assert t.count(end_marker) == 1 and t.count('**Fill appendix (B5a partial).**') == 1
L2 = """

**Implementation.** Validation and emission are separate phases. A validator
(`exists_canonDecider`) decides whether `F.scan` succeeds, in polynomial time and with a
single verdict bit, by the two-port parse front end (header validity and canonicality, and the
positive guard `max F.guard ((4k + 5) · 3^(k+1))` checked in binary against the successor of
the header) followed by the grammar stage (`exists_canonGrammarStage`). On acceptance the strip
machine (`exists_canonStripTM`) erases the input's maximal trailing `true` suffix, which leaves
the decoded machine's serialization (`canonStrip_of_scan`); on rejection the constant
`F.serialize F.fallback` is emitted; `Turing.FinTM.computesFunInTime_cond` composes the three.
The record validator's entry and success states coincide, so every record round is wrapped by
a fresh-anchor return adapter (`canonReturnAdapter`) before it becomes a public counter loop's
body. -/"""
t = t[:a] + L2 + t[b:]

# L3 -------------------------------------------------------------------------------------
rep("""right input blank. Every record consumes at least `4k + 5` cells and every round fails fast
on input exhaustion, so at most `|x| + 1` rounds run, each charged `O(|x| + |bits|)`. -/
private lemma exists_canonGrammarStage""",
    """right input blank. Every record consumes at least `4k + 5` cells and every round fails fast
on input exhaustion, so at most `|x| + 1` rounds run, each charged `O(|x| + |bits|)`.

**Implementation.** A four-phase host joins the stage front, the table block (embedded by the
forwarding transformer and wrapped by the release adapter), the suffix test and a parking
phase. The front copies the header to the outer counter, pads the copy with a spare `false`
and increments it, so that the outer counter holds `n + 1` without overflow, and then runs the
bounded unary reader on the header.
The table block is an outer public counter loop over `n + 1` inner blocks; an inner block
writes a fresh inner counter of `3^(k+1)` and runs an inner public counter loop of record
rounds. Each loop's body is a first-return round (the fresh-anchor adapter), and the loop
contracts are composed from the repetition orbit (`canonRepeat_orbit`) and the public done and
escape contracts. Every completed inner block consumes input, so at most `|x| + 1` outer rounds
run whatever the value of `n`. -/
private lemma exists_canonGrammarStage""")

# L4 -------------------------------------------------------------------------------------
if labels:
    rep("/-- **The record round's loop specification** (checkpoint 1). The adapter-wrapped record\n",
        "/-- **The record round's loop specification.** The adapter-wrapped record\n")
    rep("success preserves the bank and moves the native head to the skipped suffix. This is the\n"
        "`spec` argument of the generic counter-loop link, discharged once. -/\n",
        "success preserves the bank and moves the native head to the skipped suffix. The inner\n"
        "counter loop of the grammar stage iterates this round. -/\n")
    rep("/-- **The inner block's loop specification** (checkpoint 2). The write-then-loop seam —\n"
        "`writeConstTM` writing the inner counter word for `3 ^ (k + 1)` rounds, then checkpoint 1's\n"
        "record loop — wrapped",
        "/-- **The inner block's loop specification.** The write-then-loop seam —\n"
        "`writeConstTM` writing the inner counter word for `3 ^ (k + 1)` rounds, then the record\n"
        "round's counter loop — wrapped")
    rep("/-- **The table block** (checkpoint 3): the outer counter loop over checkpoint 2's inner\n"
        "block, wrapped",
        "/-- **The table block**: the outer counter loop over the inner\n"
        "block, wrapped")
    rep("most `|x| + 1` rounds ever run, each charged checkpoint 2's linear budget, and the counter\n",
        "most `|x| + 1` rounds ever run, each charged the inner block's linear budget, and the counter\n")
    rep("/-- **The stage front** (checkpoint 4): the counter preparation and the initial-state range\n",
        "/-- **The stage front**: the counter preparation and the initial-state range\n")

open(out, 'w', encoding='utf-8').write(t)
A, B = orig.split('\n'), t.split('\n')
d = difflib.unified_diff(A, B, 'a/TCSlib/Complexity/TuringMachine/CodeSimulator.lean',
                         'b/TCSlib/Complexity/TuringMachine/CodeSimulator.lean', lineterm='', n=1)
open(dif, 'w', encoding='utf-8').write('\n'.join(d) + '\n')
wide = [(i + 1, len(l)) for i, l in enumerate(B) if len(l) > 100]
print(f'lines {len(A)} -> {len(B)}; lines over 100 chars: {wide}')
