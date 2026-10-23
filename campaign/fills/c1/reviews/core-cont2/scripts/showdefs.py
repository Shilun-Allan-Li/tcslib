import sys, re, os
# usage: showdefs.py <worktree> <seal set file (name \t module)>: print each definition's source (up to 14 lines)
wt = sys.argv[1]
for l in open(sys.argv[2]):
    name, mod = l.rstrip('\n').split('\t')
    short = name.split('.')[-1]
    path = os.path.join(wt, mod.replace('.', '/') + '.lean')
    L = open(path, encoding='utf-8').read().split('\n')
    hits = [i for i, x in enumerate(L) if re.match(r'^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(def|abbrev)\s+(\S+\.)?' + re.escape(short) + r'(\s|$)', x)]
    print(f'==== {name} ({mod}) lines {[h+1 for h in hits]}')
    for h in hits[:1]:
        for x in L[h:h + 14]:
            print('   ', x)
            if x.strip() == '' : break
