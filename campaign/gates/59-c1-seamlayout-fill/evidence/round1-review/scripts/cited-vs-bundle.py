import sys, re, subprocess
W, rev, reviewdir, listfile = sys.argv[1:5]
review = subprocess.run(["git","-C",W,"show",f"{rev}:{reviewdir}/REVIEW.md"],capture_output=True,text=True).stdout
tree = subprocess.run(["git","-C",W,"ls-tree","-r","--name-only",rev,"--",reviewdir],capture_output=True,text=True).stdout.split()
outfiles = [t[len(reviewdir)+1:] for t in tree]
bundle = set(l.strip() for l in open(listfile) if l.strip())
# a file counts as cited if its basename (or basename without ext, or out/NN prefix) appears in REVIEW.md
cited_missing=[]; cited_present=0
for f in outfiles:
    base=f.split('/')[-1]
    stem=base
    for ext in ('.out','.txt','.lean.txt','.json','.diff','.err','.status'):
        pass
    m=re.match(r'(\d+[a-z]?)-',base)
    hit = base in review
    if not hit:
        s=re.sub(r'\.(out|txt|json|diff)$','',base)
        hit = re.search(r'(?<![\w-])'+re.escape(s)+r'(?![\w-])', review) is not None
    if not hit and m:
        hit = re.search(r'out/'+re.escape(m.group(1))+r'(?![\w])', review) is not None
    if hit:
        full=f"{reviewdir}/{f}"
        if full in bundle: cited_present+=1
        else: cited_missing.append(f)
print(f"{reviewdir} at {rev}: {len(outfiles)} files; cited-and-bundled {cited_present}; cited-but-NOT-bundled {len(cited_missing)}")
for f in cited_missing: print("  NOT BUNDLED (cited):", f)
