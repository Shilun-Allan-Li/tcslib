import subprocess, sys, re
W, rev = sys.argv[1], sys.argv[2]
files = subprocess.run(["git","-C",W,"ls-tree","-r","--name-only",rev,"--","TCSlib"],capture_output=True,text=True).stdout.split()
files=[f for f in files if f.endswith('.lean')]
hits=[]
for f in files:
    src = subprocess.run(["git","-C",W,"show",f"{rev}:{f}"],capture_output=True,text=True).stdout
    lines = src.split('\n')
    for i,l in enumerate(lines):
        m = re.match(r'private (inductive|structure) (\S+)', l)
        if not m: continue
        # scan forward until next top-level declaration/blank-after-deriving
        j=i; der=None
        while j < len(lines) and j < i+80:
            if j>i and re.match(r'(private |protected |noncomputable |@\[|/--|theorem|lemma|def|instance|abbrev|namespace|end|section|open|variable|example|#)', lines[j]):
                break
            d = re.search(r'\bderiving\s+(.*)', lines[j])
            if d: der=d.group(1).strip(); break
            j+=1
        if der: hits.append((f,i+1,m.group(1),m.group(2),der))
for h in hits: print(f"{h[0]}:{h[1]}: private {h[2]} {h[3]} deriving {h[4]}")
print(f"TOTAL private inductive/structure declarations with a deriving clause at {rev}: {len(hits)} in {len(set(h[0] for h in hits))} files")
