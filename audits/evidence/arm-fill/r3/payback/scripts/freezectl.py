"""Controls of the freeze check and of the name screen: each must FAIL (read-only on the base).

Usage: python3 -I -B freezectl.py <base export> <L> <packages worktree>

Each freeze control is one asserted mutation of a scratch copy of a landed file, run through
freeze.py, which must exit 1 and name the mutation:
  C1 a D1 restatement that is not the rewrite (`coreSum_eq_of_cfgWord_eq`, Word: `s` -> `s + 1`
     in one hypothesis);
  C2 a public statement outside D1 (`orc_bit`, Codec/Run: `false` -> `true`);
  C3 an unauthorized public removal (`configBound_mono`, Bridge);
  C4 an unauthorized promotion (`length_lbStep`, TQBFHardParams);
  C5 an unauthorized proof change (`mem_initLang`, Langs);
  C6 an unauthorized docstring change in CircuitComplexity (`eval_tseitinGates_values`);
  C7 an unauthorized addition (a private lemma in Formulas/QBF);
  C8 a listed deletion not made (Bridge's `mem_of_acceptsWithin` restored from the base);
  C9 an import change (Engine imports `TCSlib.Programs.Util.List`).
The name controls (names.py --extra): a new public name that clashes with an existing one, and
a file that still uses a deleted copy; names.py must exit 1 with exactly one CLASH and one
STALE use.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402

TMP = os.path.join(lib.L, "work", "tmp-scan")
NAMES_CTL = """namespace Turing.NDTM

/-- Name-screen control (not landed): a clash with the promoted `take_succ_action`. -/
theorem take_succ_action : True := trivial

end Turing.NDTM

namespace Complexity.Codec

/-- Name-screen control (not landed): a use of a deleted copy. -/
theorem stale_use : True := by
  have := @inWin_runWith_take
  trivial

end Complexity.Codec
"""


def main():
    base, L, WT = sys.argv[1:4]
    W = os.path.join(L, "work", "freeze-ctl")
    os.makedirs(W, exist_ok=True)
    tree = os.path.join(L, "tree")
    t = {k: lib.rd(os.path.join(tree, E.FILES[k][0])) for k in E.FILES}
    b = {k: lib.rd(os.path.join(base, E.FILES[k][0])) for k in E.FILES}
    br = lib.decl_text(b["Bridge"], "mem_of_acceptsWithin", TMP)
    muts = {
        "C1": ("Word", lib.sub(t["Word"], "(hC : Cfg.InWindow s C) (hD : Cfg.InWindow s D) (h : "
               "cfgWord s C = cfgWord s D)", "(hC : Cfg.InWindow (s + 1) C) (hD : Cfg.InWindow s D) "
               "(h : cfgWord s C = cfgWord s D)", 1, "C1"),
               "statement changed Complexity.Codec.coreSum_eq_of_cfgWord_eq"),
        "C2": ("Run", lib.sub(t["Run"], "orc jBit (pairEncode y (Nat.bits a)) = y.getD a false",
               "orc jBit (pairEncode y (Nat.bits a)) = y.getD a true", 1, "C2"),
               "statement changed Complexity.Codec.orc_bit"),
        "C3": ("Bridge", lib.delete_decl(t["Bridge"], "configBound_mono", TMP),
               "removed ['Complexity.Codec.configBound_mono']"),
        "C4": ("TQBFHardParams", lib.sub(t["TQBFHardParams"], "private theorem length_lbStep",
               "theorem length_lbStep", 1, "C4"), "visibility ['Complexity.TQBFHard.length_lbStep']"),
        "C5": ("Langs", lib.sub(t["Langs"], "      cfgCode s (N.tm.initCfg x) = c := by\n  constructor\n"
               "  · rintro ⟨x', c', s', h, hC⟩", "      cfgCode s (N.tm.initCfg x) = c := by\n"
               "  constructor\n  · rintro ⟨x', c', s', h, hC'⟩\n    have hC := hC'", 1, "C5"),
               "body changed Complexity.Codec.mem_initLang"),
        "C6": ("DAGCircuitSat", lib.sub(t["DAGCircuitSat"], "/-- The vertex values on input `x` "
               "satisfy every gate clause", "/-- **Tseitin.** The vertex values on input `x` satisfy"
               " every gate clause", 1, "C6"),
               "docstrings changed ['BoolCircuit.DAGCircuit.eval_tseitinGates_values']"),
        "C7": ("QBF", lib.sub(t["QBF"], "\nend QBF\n\nend Complexity\n",
               "\n/-- Control. -/\nprivate theorem paybackControl : True := trivial\n\nend QBF\n\n"
               "end Complexity\n", 1, "C7"), "added ['Complexity.QBF.paybackControl']"),
        "C8": ("Bridge", lib.sub(t["Bridge"], "/-- **The code-level step relation**",
               br + "\n\n/-- **The code-level step relation**", 1, "C8"),
               "not removed ['Complexity.Codec.mem_of_acceptsWithin']"),
        "C9": ("Engine", lib.sub(t["Engine"], "import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops\n",
               "import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops\nimport TCSlib.Programs.Util.List\n",
               1, "C9"), "FAIL (imports"),
    }
    bad = 0
    for c, (k, text, want) in muts.items():
        p = os.path.join(W, f"{c}-{k}.lean")
        lib.wr(p, text)
        r = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "freeze.py"), base, tree,
                            "--override", f"{k}={p}"], capture_output=True, text=True)
        fails = [l for l in r.stdout.split("\n") if "FAIL" in l]
        ok = r.returncode == 1 and any(want in l for l in fails)
        bad += not ok
        print(f"{c} ({k}): exit {r.returncode}; {'FAILS as required' if ok else 'DID NOT FAIL AS REQUIRED'}"
              f": {'; '.join(f[:220] for f in fails if 'RESULT' in f)}")
    ctl = os.path.join(L, "work", "names-ctl.lean")
    lib.wr(ctl, NAMES_CTL)
    r = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "names.py"), base, L, WT, "--extra",
                        ctl], capture_output=True, text=True)
    nc = len(re.findall(r"^  CLASH ", r.stdout, re.M))
    ns = len(re.findall(r"^  STALE ", r.stdout, re.M))
    ok = r.returncode == 1 and nc == 1 and ns == 1
    bad += not ok
    print(f"names control: exit {r.returncode}; CLASH {nc}, STALE {ns}: "
          f"{'FAILS as required' if ok else 'DID NOT FAIL AS REQUIRED'}")
    for l in r.stdout.split("\n"):
        if l.startswith("  CLASH") or l.startswith("  STALE"):
            print("   " + l.strip()[:200])
    n = len(muts) + 1
    print(f"controls: {n}; failing as required: {n - bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
