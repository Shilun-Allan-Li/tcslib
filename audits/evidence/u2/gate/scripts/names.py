"""Name screen of the U2 unit (read-only; standard library only).

Usage: python3 -I names.py <base root> <landed root>

The new public names: every declaration of the new module, every new declaration of the touched
files, the promoted lemma's new name, and the constructor and fields of `EffectiveCodeK`. Each
name's distinctive last component (or, for nested names, its first distinctive component) is
screened as a whole word over every `.lean` file of the base tree: an occurrence would be a
collision or a reference to a name that did not exist. Exit 1 on any hit.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from decls import parse  # noqa: E402

TM = "TCSlib/Complexity/TuringMachine"
NEW = [f"{TM}/UniversalK.lean"]
TOUCHED = [f"{TM}/Build/StepBlockLoop.lean", f"{TM}/Codes2Tape.lean", f"{TM}/SelfUniversal.lean"]
PROMOTED = {"Turing.Code2TM.serialize_eq_serializeK": "Turing.twoTape_serialize_eq"}
FIELDS = {"Turing.EffectiveCodeK": ["mk", "numStates", "machine", "canonizer", "canonizerTime",
                                    "canonizer_computes"]}
TOKENS = ["EffectiveCodeK", "ofSerialize", "toK", "toK_toFinTM", "toK_machine", "exists_selfStartupTMK", "exists_selfUniversalK",
          "universalK", "forwardLoopCfg", "exists_forwardLoopTM", "serialize_eq_serializeK"]


def main():
    base, landed = sys.argv[1:3]
    names = []
    for rel in NEW:
        names += [d["name"] for d in parse(open(os.path.join(landed, rel)).read())
                  if not d["private"]]
    for rel in TOUCHED:
        b = {d["name"] for d in parse(open(os.path.join(base, rel)).read())}
        names += [d["name"] for d in parse(open(os.path.join(landed, rel)).read())
                  if d["name"] not in b and not d["private"]]
    for s, fs in FIELDS.items():
        assert s in names, s
        names += [f"{s}.{f}" for f in fs]
    print(f"## New public names ({len(names)})")
    for n in names:
        extra = f" (promoted from the private `{PROMOTED[n]}`)" if n in PROMOTED else ""
        print(f"- `{n}`{extra}")
    for n in names:
        comps = n.split(".")[1:]
        assert any(c in TOKENS for c in comps) or comps[-1] in FIELDS.get(
            ".".join(n.split(".")[:-1]), []), f"no screened token covers {n}"
    files = [os.path.join(base, "TCSlib.lean")]
    for d, _, fs in os.walk(os.path.join(base, "TCSlib")):
        files += [os.path.join(d, f) for f in fs if f.endswith(".lean")]
    hits = []
    for f in sorted(files):
        src = open(f, encoding="utf-8").read()
        for t in TOKENS:
            for m in re.finditer(r"(?<![A-Za-z0-9_'])" + re.escape(t) + r"(?![A-Za-z0-9_'])", src):
                hits.append(f"{os.path.relpath(f, base)}:{src.count(chr(10), 0, m.start()) + 1}: {t}")
    print()
    print(f"## Whole-word screen over the base tree ({len(files)} files): tokens {TOKENS}")
    print(f"occurrences: {len(hits)}")
    for h in hits:
        print("  " + h)
    if hits:
        print("NAMES: FAIL")
        sys.exit(1)
    print("NAMES: PASS — no screened component occurs anywhere in the base tree "
          "(`EffectiveCodeK`'s fields are covered by `EffectiveCodeK`)")


if __name__ == "__main__":
    main()
