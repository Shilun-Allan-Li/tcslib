"""landedits.py <WindowClock.lean> : the maintainer's landing edits (every replacement asserted unique).
A1: the module's Status paragraph; A2: the Main results entry; B (optional, cosmetic): three double blank lines."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
E = [
 ('A1', """**Status.** The bridges are proved. `Turing.exists_configWindowRunnerTM` is sorried with its
proof sketch; private lemmas toward it (the clock arithmetic at the actual record, the one-cell
move, a field's constant copy and the clock's clear) are proved.
""", """**Status.** Everything here is proved: the bridges, and `Turing.exists_configWindowRunnerTM`,
whose clock writer, phase host and clear are private to this module.
"""),
 ('A2', """* `Turing.exists_configWindowRunnerTM` — the windowed runner with its configuration-count
  clock (sorried).
""", """* `Turing.exists_configWindowRunnerTM` — the windowed runner with its configuration-count
  clock (proved).
"""),
 ('B1', """  omega


/-- The clock tape of a writer configuration is the constant patch. -/""",
  """  omega

/-- The clock tape of a writer configuration is the constant patch. -/"""),
 ('B2', """  exact hseg


/-- **The copy of a field onto the clock**""", """  exact hseg

/-- **The copy of a field onto the clock**"""),
 ('B3', """  rfl


/-- **The windowed runner**, as a host segment""", """  rfl

/-- **The windowed runner**, as a host segment"""),
]
for tag, a, b in E:
    n = s.count(a)
    assert n == 1, (tag, n)
    s = s.replace(a, b)
    print(tag, 'applied')
open(p, 'w', encoding='utf-8').write(s)
