import sys
p = sys.argv[1]
s = open(p, encoding='utf-8').read()
def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, (n, old[:70])
    s = s.replace(old, new)

# F9/F10/F11: the issue-time list
rep("""the recommendations. Issue-time items: @ANCESTOR@, the dispatch table's SHA-256 column, the
prerequisites' merge state (Q-B1 and Q-U1 below), and each item's budget if the queue changes. -->""",
"""the recommendations. Issue-time items: @ANCESTOR@, the SHA-256 column, the prerequisites' merge
state (Q-B1 and Q-U1 below), the ⟨Q-M2⟩ ruling, each item's budget if the queue changes, each
draft moved to `briefs/` without its comment with its inputs staged, and every item's banner
(number, this file's name, budget). Re-run every item's pre-ship at the shared base if any Lean
change lands first: under Q-B1 (A) the harvest PR re-points C1's owned file (C1's blob, lines,
counts, order list and screen population); #156's head (its gate-69 fix) also edits B5a's owned
file and `Build/StepBlock` (C1's screen population) and `Build/Seam` (G4's). G4's own items are
in its comment, plus three it does not list: its order list's count (96, not 95), its lint base
(40 files, not 39) and its out-of-scope placeholder. -->""")

# F10: dropping an item
rep("""    `Turing.StepBlock.forwardLoopCfg` and `Turing.rulerHostCfg`⟩. **An item whose prerequisite is
    not in the shared base is removed from the queue at issue**, and the queue renumbered;""",
"""    `Turing.StepBlock.forwardLoopCfg` and `Turing.rulerHostCfg`⟩. **An item whose prerequisite is
    not in the shared base is not issued:** this cover is issued without it (every mention
    removed, the queue and the remaining banners renumbered). No other item's base, order list or
    cache roots change;""")

# F8: the cover cannot carry its own hash
rep("""- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders, and its SHA-256 must be the one below:

  | Brief | SHA-256 (dispatch copy) |
  |---|---|
  | this cover | ⟨…⟩ |
  | `c1-fill-replaycanon.md` | ⟨…⟩ |""",
"""- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders. This cover's SHA-256 must be the one the dispatch message gives, and
  each item brief's the one below:

  | Brief | SHA-256 (dispatch copy) |
  |---|---|
  | `c1-fill-replaycanon.md` | ⟨…⟩ |""")

# Q-M2: the recommended rule, still marked for the ruling
rep("""(54 files; 87 minutes a run on the drafting host, against C1's 13 and U2's 10): ⟨Q-M2: whether
B5a's budget ends when its after run starts⟩. Never switch branches while a screen runs.""",
"""(54 files; 87 minutes a run on the drafting host, against C1's 13 and U2's 10). ⟨Q-M2, as
recommended:⟩ **B5a's budget counts up to the start of its after run.** Write its last checkpoint
zip first; start the after run at the latest when the budget ends, and write `REPORT.md` while it
runs; create the next item's branch only after the run has ended and B5a's zip is written. Never
switch branches while a screen runs.""")

open(p, 'w', encoding='utf-8').write(s)
print('cover ok')
