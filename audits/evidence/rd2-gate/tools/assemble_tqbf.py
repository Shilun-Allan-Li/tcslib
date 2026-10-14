"""Assemble the proposed TQBF.lean from the campaign-tip file and the RD-2 blocks.
Every edit is asserted to match exactly once (memory rule: assert every scripted edit)."""
import sys, pathlib
src, blocks, dst = map(pathlib.Path, sys.argv[1:4])
t = src.read_text(encoding='utf-8')
def rd(name): return (blocks / name).read_text(encoding='utf-8')

def rep(old, new):
    global t
    n = t.count(old)
    assert n == 1, (n, old[:80])
    t = t.replace(old, new)

# 1. imports
rep("import TCSlib.Complexity.TuringMachine.Build.CfgRecord\n",
    "import TCSlib.Complexity.TuringMachine.Build.CfgRecord\n"
    "import TCSlib.Complexity.FormulaKit.Gate\n"
    "import TCSlib.Complexity.FormulaKit.Emit\n")

# 2. module docstring, design bullet
start = "* **Claim 4.4(2) at polynomial size, over a packaged quotient codec.** The\n"
end = "  (the phase-P4.4 `PATH` encoding remains the candidate).\n"
i = t.index(start); j = t.index(end) + len(end)
assert t.count(start) == 1 and t.count(end) == 1 and i < j
t = t[:i] + rd("moddoc_design.part") + t[j:]

# 3. module docstring, main definitions / results / references
start = "## Main definitions\n\n* `Complexity.PSPACEHard`"
end = "  STOC 1973. (Cited through [AB09]; no external text required.)\n-/\n"
i = t.index(start); j = t.index(end) + len(end)
assert t.count(start) == 1 and t.count(end) == 1 and i < j
t = t[:i] + rd("moddoc_main.part") + t[j:]

# 4. definitions block before the B4a fill appendix
anchor = "/-! ### Fill appendix: finite marker tracks for the quotient codec\n"
rep(anchor, rd("defs.part") + "\n" + anchor)

# 5. retirement status on the old statement's docstring
rep("/-- **Claim 4.4(2), packaged quotient form** (proved — phase\n"
    "P4.3 round 2; see the module docstring's declared deviations): for every\n",
    "/-- **Claim 4.4(2), packaged quotient form** (proved — phase\n"
    "P4.3 round 2; **retired at the RD-2a re-fill**, design §16b item 2: superseded by the\n"
    "`Complexity.ConfigCodec` theorems below, and used by no proof; see the module docstring's\n"
    "declared deviations): for every\n")

# 6. theorems block before the TQBF language
anchor = "/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded\n"
rep(anchor, rd("thms.part") + "\n" + anchor)

# 7. TQBF_PSPACEHard docstring
start = "/-- **`TQBF` is `PSPACE`-hard** ([AB09, Theorem 4.13, hardness half]; spec,\n"
end = "`Complexity.QBF.decode_encode`. -/\ntheorem TQBF_PSPACEHard : PSPACEHard TQBF := by\n"
i = t.index(start); j = t.index(end) + len(end)
assert t.count(start) == 1 and t.count(end) == 1 and i < j
t = t[:i] + rd("hard_doc.part") + "theorem TQBF_PSPACEHard : PSPACEHard TQBF := by\n" + t[j:]

dst.write_text(t, encoding='utf-8')
print("ok", len(t.split('\n')), "lines")
