import sys
src, out = sys.argv[1], sys.argv[2]
t = open(src, encoding='utf-8').read()
old1 = """A counter-driven copy of a bounded window of the native input onto a work tape (user decision 5
of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)). The universal NDTM cannot
copy its whole input `x`, since its time bound has no `|x|` term; it copies the window
`x.take t` instead, and the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that
the window is enough for `t` simulated steps. The in-place suffix device stays with the
universal machine U-1, whose `universal` has no deadline to truncate by.
"""
new1 = """A counter-driven copy of a bounded window of the native input onto a work tape, for the
nondeterministic time hierarchy [AB09, Theorem 3.2]. The universal NDTM cannot copy its whole
input `x`, since its time bound has no `|x|` term; it copies the window `x.take t` instead, and
the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that the window is enough for
`t` simulated steps. The in-place suffix device belongs instead to the universal machine of
`Turing.universal`, which has no deadline to truncate by.
"""
old2 = "  Cambridge University Press, 2009. (§1.2: the read-only input tape.)\n"
new2 = "  Cambridge University Press, 2009. (§1.2: the read-only input tape; Theorem 3.2.)\n"
for o, n in ((old1, new1), (old2, new2)):
    assert t.count(o) == 1, 'anchor not found exactly once: ' + o[:40]
    t = t.replace(o, n)
open(out, 'w', encoding='utf-8').write(t)
print('wrote', out)
