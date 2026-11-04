"""Generate the seal test's two files from the owned module.

Usage: python3 -I gen_seal.py <owned.lean> <walk.out> <outdir>
Writes <outdir>/QySealed.lean (the owned module with every other-file TCSlib definition the
elaborated-constant walk reaches, plus the brief's list, made `local irreducible` from the
fill's first private on, and the four `@[simp]` TCSlib definitions erased) and
<outdir>/QySealControls.lean (one `rfl` control per sealed definition, unsealed then sealed),
and <outdir>/sealed-names.txt.
"""
import re
import sys

owned, walk, outdir = sys.argv[1:4]
src = open(owned).read().split("\n")

BRIEF = """Complexity.TimeConstructible Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime
Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.initCfg Turing.Cfg.ofWords Turing.stateWord
Turing.clockCfg Turing.wordPatch Turing.counterLoopCfg Turing.expandTM Turing.copyMapTM
Turing.seamCompTM Turing.embedEmitTM Turing.embedSilentTM Turing.pairEncode Turing.seamReleaseTM
Turing.phaseHostTM Turing.Cfg.mapState Turing.Cfg.Stopped Turing.embedEmitCfg Turing.embedSilentCfg
Turing.FinTM.bufferTape Turing.scanTM Turing.inputFoldTM Turing.writeAdvTM Turing.clearTM
Turing.rewindTM Turing.dbl Turing.counterValue""".split()
SIMP = ["Turing.Action.apply", "Turing.Cfg.init", "Turing.MultiTapeTM.initCfg",
        "Turing.NDTM.initCfg"]

walked = []
for line in open(walk):
    m = re.match(r"^def (\S+) \[", line)
    if m:
        walked.append(m.group(1))
names = []
for n in BRIEF + SIMP + walked:
    if n not in names:
        names.append(n)
open(f"{outdir}/sealed-names.txt", "w").write("\n".join(names) + "\n")


def attr_lines(prefix, items, width=100):
    out, cur = [], prefix
    for it in items:
        if len(cur) + 1 + len(it) > width:
            out.append(cur)
            cur = "  " + it
        else:
            cur = cur + " " + it if cur.strip() else "  " + it
    out.append(cur)
    return out


seal = (["section QySeal", ""] + attr_lines("attribute [local irreducible]", names) +
        attr_lines("attribute [-simp]", SIMP) + [""])

# insertion: the first docstring after the landed `qy_query_of_main`
i0 = next(i for i, l in enumerate(src) if l.startswith("private theorem qy_query_of_main"))
i1 = next(i for i in range(i0 + 1, len(src)) if src[i].startswith("/--"))
assert src[-1] == "" and src[-2] == "end Turing.NTimeDiag", src[-3:]
sealed = src[:i1] + seal + src[i1:-2] + ["end QySeal", ""] + src[-2:]
open(f"{outdir}/QySealed.lean", "w").write("\n".join(sealed))

imports = [l for l in src if l.startswith("import ")]
ctl = ["/-", "Seal controls (scratch; not library code): for each sealed TCSlib definition `c`, the goal",
       "`c = <its defining value>` closed by `rfl`. Expected: every control in `Unsealed` closes (an",
       f"info line each), and every control in `Sealed` fails (exactly {len(names)} errors, one per control).",
       "-/"] + imports + ["", "set_option maxHeartbeats 0", "",
       "open Lean Meta Elab Command Term in",
       "/-- `#qy_control c`: elaborate `rfl` against `c = <the value of c>` at default transparency. -/",
       "elab \"#qy_control \" id:ident : command => liftTermElabM do",
       "  let c ← realizeGlobalConstNoOverload id",
       "  let ci ← getConstInfo c",
       "  let some v := ci.value? | throwError \"{c} has no value\"",
       "  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar",
       "  let ty ← mkEq (mkConst c us) (v.instantiateLevelParams ci.levelParams us)",
       "  let _ ← withoutErrToSorry <| elabTermEnsuringType (← `(rfl)) ty",
       "  synthesizeSyntheticMVarsNoPostponing",
       "  logInfo m!\"control {c}: closes by rfl\"", "",
       "section Unsealed", ""] + [f"#qy_control {n}" for n in names] + ["", "end Unsealed", "",
       "section Sealed", ""] + attr_lines("attribute [local irreducible]", names) + [""] + \
      [f"#qy_control {n}" for n in names] + ["", "end Sealed", ""]
open(f"{outdir}/QySealControls.lean", "w").write("\n".join(ctl))
print(f"sealed {len(names)} names; insertion before line {i1 + 1}")
