"""Lean probe files of the dedup payback landing (writes under <L>/work/probes; read-only on the
base export).

Usage: python3 -I -B probes.py <L>

Writes (all elaborated by elab.sh, read-only):
* Ax<key>.lean: the cut of a changed module (work/cut/<key>.cut.lean, byte for byte) followed
  by `#print axioms` of every named declaration of the landed module, public and private (the
  axiom check, and the elaboration of the cut itself: the tail only adds informational
  messages). For the consumer cuts, the cut alone.
* AxBase<key>.lean: the base text of each changed module followed by `#print axioms` of every
  named declaration of the base module (the baselines: warnings, sorries and axioms).
* Base<Module>.lean: the base text of every unchanged module that some cut inlines (their
  warning baselines).
* Negative controls, each must FAIL:
  - NegDirect: the landed `Codec/Checks` alone against the snapshot, without the cut (the
    snapshot's oleans of Word, Valid, Step and Langs predate D1);
  - NegMutant: the Word cut with one hypothesis swapped in `coreSum_eq_of_cfgWord_eq`
    (`hC.2 i z` -> `hD.2 i z` for `h1`, asserted once);
  - NegNoDelta: the Engine cut without InputAccess's delta (`arm_chain` unknown);
* The artifact control: FacadeFullBase and FacadeFullLanded, the facade's 38-module cut of the
  base texts and of the landed texts; both fail with the same errors (the union of imports
  exposes `Complexity.LogProg.Mem` inside `ISCountGenWalk`), which is why the facade is
  elaborated as its own text and its imports through the consumer cuts.
names.json lists the printed names per probe.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402
import cuts  # noqa: E402


def named(text):
    D, _ = lib.declcut.decls(text)
    return [n for n in D if "<anon>" not in n and not n.endswith("'")]


def tail(names):
    return "\n" + "".join(f"#print axioms {n}\n" for n in names)


def main():
    L = sys.argv[1]
    W = os.path.join(L, "work")
    P = os.path.join(W, "probes")
    CUT = os.path.join(W, "cut")
    tree = os.path.join(L, "tree")
    os.makedirs(P, exist_ok=True)
    meta = json.loads(lib.rd(os.path.join(CUT, "cuts.json")))
    names = {}
    inlined_unchanged = set()
    for key, m in meta.items():
        cut = lib.rd(os.path.join(CUT, m["file"]))
        for r in m["regions"]:
            if r["kind"] == "inline" and not r["changed"]:
                inlined_unchanged.add(r["module"])
        if key.startswith("consumer-"):
            lib.wr(os.path.join(P, f"Ax{key}.lean"), cut)
            names[f"Ax{key}"] = []
            continue
        rel = E.FILES[key][0]
        ln = named(lib.rd(os.path.join(tree, rel)))
        lib.wr(os.path.join(P, f"Ax{key}.lean"), cut + tail(ln))
        names[f"Ax{key}"] = ln
        bt = lib.rd(os.path.join(lib.BASE, rel))
        bn = named(bt)
        lib.wr(os.path.join(P, f"AxBase{key}.lean"), bt + tail(bn))
        names[f"AxBase{key}"] = bn
    for m in sorted(inlined_unchanged):
        lib.wr(os.path.join(P, f"Base{m.split('.', 2)[-1].replace('.', '_')}.lean"),
               lib.rd(os.path.join(lib.BASE, lib.path_of_mod(m))))
    # negative controls
    lib.wr(os.path.join(P, "NegDirect.lean"), lib.rd(os.path.join(tree, E.FILES["Checks"][0])))
    wc = lib.rd(os.path.join(CUT, "Word.cut.lean"))
    lib.wr(os.path.join(P, "NegMutant.lean"), lib.sub(
        wc, "have h1 : C.workTapes i z = none := hC.2 i z (not_le.mp hz)",
        "have h1 : C.workTapes i z = none := hD.2 i z (not_le.mp hz)", 1, "NegMutant"))
    ec = lib.rd(os.path.join(CUT, "Engine.cut.lean"))
    dl = "/-! Delta of `TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`"
    a = ec.index(dl)
    b = ec.index("/-!\n# Abstract-register-machine fragments")
    assert ec.count(dl) == 1 and a < b
    lib.wr(os.path.join(P, "NegNoDelta.lean"), ec[:a] + ec[b:])
    # the artifact control: the facade's full cut, base and landed
    gl = lib.graph(lib.BASE, overlay=tree)
    gb = lib.graph(lib.BASE)
    kbm = {cuts.mod(k): k for k in E.FILES}
    t_l, _ = cuts.build("SpaceComplexity", tree, lib.BASE, gl, kbm)
    t_b, _ = cuts.build("SpaceComplexity", lib.BASE, lib.BASE, gb, {}, own_only=False)
    lib.wr(os.path.join(P, "FacadeFullLanded.lean"), t_l)
    lib.wr(os.path.join(P, "FacadeFullBase.lean"), t_b)
    lib.wr(os.path.join(P, "names.json"), json.dumps(names, indent=1) + "\n")
    print(f"probes written to {P}: {len(os.listdir(P)) - 1} files; base baselines of "
          f"{len(inlined_unchanged)} unchanged inlined modules")


if __name__ == "__main__":
    main()
