#!/usr/bin/env python3
"""Statement freeze check for the rabin fill: compare every declaration of the base file with
the head file. Usage: declfreeze.py BASE HEAD."""
import re, sys
TARGETS = set("""oddFactorProb_le blumFactorProb_le blumFactoring_of_factoring polyTimeComputable_oddGenRaw
polyTimeComputable_blumGenRaw rabinSampler_spec rabinCollection_sampleClose polyTimeComputable_rabinFactorRaw
rabinCollection_invProbAt_le rabinCollection_oneWay polyTimeComputable_blumInvRaw blumInv_spec blumSampler_spec
rabinBlumTrapdoor_sampleClose rabinBlumTrapdoor_invProbAt_le rabinBlumTrapdoor_oneWay polyTimeComputable_rabinRootRaw
blumFactorProb_le_invProbAt blumFactoring_of_rabinBlum_oneWay""".split())
KW = r"(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:protected\s+)?(theorem|lemma|def|abbrev|structure|instance|class)\b"
def decls(path):
    lines = open(path).read().split("\n")
    out = []  # (kind, name, doc, block)
    i = 0; doc = None
    starts = []
    for k, l in enumerate(lines):
        if re.match(KW, l) or l.startswith("/--") or l.startswith("/-!") or l.startswith("end ") or l.startswith("namespace "):
            starts.append(k)
    starts.append(len(lines))
    pending_doc = ""
    for a, b in zip(starts, starts[1:]):
        chunk = "\n".join(lines[a:b]).rstrip()
        if lines[a].startswith("/--"):
            # docstring possibly followed directly by the declaration in the same chunk? (no: decl line starts a new chunk)
            pending_doc = chunk; continue
        m = re.match(KW + r"\s*([^\s:({\[]*)", lines[a])
        if not m:
            pending_doc = ""; continue
        kind, name = m.group(1), m.group(2)
        if kind == "instance" and (name == "" or name.startswith("(")): name = "instance@" + lines[a]
        out.append((kind, name, pending_doc, chunk, lines[a].lstrip().startswith("private")))
        pending_doc = ""
    return out
def header(block):
    m = re.search(r":=\s*by\b|:=\s*$|:=\s|\bwhere\b", block, flags=re.M)
    return block[:m.start()].rstrip() if m else block
base = decls(sys.argv[1]); head = decls(sys.argv[2])
hb = {}
for d in head: hb.setdefault(d[1], d)
ok = True; docchg = []; newpriv = []; newpub = []
names_base = set(d[1] for d in base)
for kind, name, doc, block, priv in base:
    if name not in hb:
        print(f"MISSING {name}"); ok = False; continue
    k2, n2, doc2, block2, priv2 = hb[name]
    if kind in ("theorem", "lemma"):
        if header(block) != header(block2):
            print(f"HEADER CHANGED {name}"); ok = False
        elif name not in TARGETS and block != block2:
            print(f"BODY CHANGED (non-target) {name}"); ok = False
    else:
        if block != block2:
            print(f"DEF CHANGED {name}"); ok = False
    if doc != doc2: docchg.append(name)
for kind, name, doc, block, priv in head:
    if name not in names_base:
        (newpriv if priv else newpub).append(name)
print(f"base declarations: {len(base)}; head declarations: {len(head)}")
print(f"new private declarations: {len(newpriv)}; all prefixed rabin_: {all(n.startswith('rabin_') for n in newpriv)}")
print(f"new public declarations: {len(newpub)} {newpub}")
print(f"docstrings changed: {docchg}")
print("targets still containing 'sorry':", [n for k,n,d,b,p in head if n in TARGETS and re.search(r'\bsorry\b', b)])
print("RESULT:", "PASS" if ok and not newpub and all(n.startswith('rabin_') for n in newpriv) else "FAIL")
