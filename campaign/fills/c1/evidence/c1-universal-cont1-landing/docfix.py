"""docfix.py <NTimeHierarchy.lean>: gate 68's minors 1 and 2 (docstrings only)."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(a, b):
    global s
    assert s.count(a) == 1, a[:60]; s = s.replace(a, b)
rep("""`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup
hypothesis. The setup built below
is a seam chain over `K + kC + 1` tapes — the core's `K`, the embedded header composite's `kC`,
and the capture/counter tape last — whose phases are the embedded header pass, the code buffer's
rewind and clear, a guided erase of the extractor scratch bank, the expansion of the captured
budget word into the unary block, the block rewind, the counter clear, and the input rewind.
The pieces here are the two leaf machines with their framed runs, the seam-step composer, the
header composite's exact first halt, and two small word facts. -/""",
"""`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup
hypothesis. The setup built below is a seam chain over `K + kC + 1` tapes — the core's `K`, the
embedded header composite's `kC`, and the capture/counter tape last — whose phases are the
embedded header pass, the code buffer's rewind and clear, a guided erase of the extractor scratch
bank, the expansion of the captured budget word into the unary block, the block rewind, the
counter clear, and the input rewind (`Turing.inputRewindTM`, imported). The pieces here are the
guided bank-erase leaf with its framed run, the seam-step composer, the header composite's exact
first halt, and two small word facts. -/""")
rep("""step right into the live park. The guide's head travels with the bank but its word is kept;
every other tape, every other head, the input head and the output are untouched. -/""",
"""step right into the live park. The guide's head travels with the bank, and when the guide is not
one of the selected tapes its word is kept; every other tape, every other head, the input head and
the output are untouched. -/""")
rep("""/-- **The guided bank erase, framed.** Start with every bank tape and the guide holding a
length-`L` buffered word with its head at `L`. The erase parks""",
"""/-- **The guided bank erase, framed.** Take a guide outside the selected bank, and start with
every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks""")
rep("""every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks at exactly `L + 2` and not
earlier, with the bank blank, the bank and guide heads at the origin, the guide's word and
everything else unchanged.
""",
    """every bank tape and the guide holding a length-`L` buffered word with its head at `L`. The erase
parks at exactly `L + 2` and not earlier, with the bank blank, the bank and guide heads at the
origin, the guide's word and everything else unchanged.
""")
bad = [(i, len(l)) for i, l in enumerate(s.split('\n'), 1) if len(l) > 100]
assert not bad, bad
open(p, 'w', encoding='utf-8').write(s); print('ok')
