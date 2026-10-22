"""Apply the reviewer's proposed landing edits to the repaired draft (not repairs: the repaired
draft already elaborates). usage: python3 -I landing.py REPAIRED.lean OUT.lean"""
import sys

EDITS = [
    # L1: public-facing text. The second sentence is a scope justification for the report, not
    # library text; "at a blank" is the input's right end marker.
    ("L1", "iw_body docstring",
     """/-- The one-cell copy body returns to `false` after copying a symbol and escapes to `true`
at a blank. No catalog row provides this cyclic native-input copy with an end-marker escape. -/""",
     """/-- The one-step copy body on one work tape. In state `false`, on an input symbol it writes the
symbol, moves the tape head and the input head right and stays in `false`; at the input's right
end it moves to `true` without writing or moving. -/"""),
    # L2: public-facing text ("leaf" is not defined for a generic machine).
    ("L2", "iw_one docstring",
     "/-- One live step of a leaf is its selected action, expressed through the model's equations. -/",
     "/-- One step from a live state applies that state's transition at the scanned symbols. -/"),
    # L3: public-facing text: "public" describes the project's API rule, not the mathematics.
    ("L3a", "iw_orbit proof sketch",
     "**Proof sketch.** Induct on the number of rounds using the public round-orbit equations and",
     "**Proof sketch.** Induct on the number of rounds using the round-orbit equations and"),
    ("L3b", "iw_machine docstring",
     "Every other transition is delegated to the public counter loop. -/",
     "Every other transition is the counter loop's. -/"),
    ("L3c", "iw_join_prefix proof sketch",
     """**Proof sketch.** The transition tables agree off the escape anchor. Apply the public
agreement transport on that set of states. -/""",
     """**Proof sketch.** The transition tables agree off the escape anchor, so the runs agree
until it is first visited (`Turing.MultiTapeTM.runFrom_eq_of_agreeOn`). -/"""),
    # L4: rule 10 hygiene. `decide` evaluates `CounterLoopState`'s derived `DecidableEq`
    # instance (another file's definition); `simp` closes the goal by constructor disjointness.
    ("L4", "iw_local: constructor disjointness without evaluating the derived instance",
     "        rw [hex]\n        decide\n",
     "        rw [hex]\n        simp\n"),
    # L5: the module's status line (the maintainer's integration edit).
    ("L5", "module docstring: the contract is proved",
     "* `Turing.exists_inputWindowCopyTM` — the window copier's contract (sorried).",
     "* `Turing.exists_inputWindowCopyTM` — the window copier's contract (proved)."),
]

text = open(sys.argv[1], encoding="utf-8").read()
for eid, why, old, new in EDITS:
    n = text.count(old)
    assert n == 1, f"{eid}: expected exactly one occurrence, found {n}"
    text = text.replace(old, new)
    print(f"applied {eid}: {why}")
open(sys.argv[2], "w", encoding="utf-8").write(text)
