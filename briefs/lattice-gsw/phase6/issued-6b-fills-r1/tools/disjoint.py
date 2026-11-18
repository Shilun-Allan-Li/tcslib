"""disjoint.py <repo> <ourpaths> : owner paths of cleanup Stage 2 (scope.tsv col owner_file, s2a-items.tsv col
owner_file) and the Lean paths changed on cleanup/stage2-s2a (local and origin heads, vs merge-base with the
records base), intersected with our paths (exact) and with our directories (prefix, information)."""
import sys, csv, subprocess
repo, ours = sys.argv[1], [l.strip() for l in open(sys.argv[2]) if l.strip()]
own = set()
for f in ['scope.tsv', 's2a-items.tsv']:
    with open(f'{repo}/briefs/pass-shelat-ch5-8/cleanup-stage2/{f}') as fh:
        for r in csv.DictReader(fh, delimiter='\t'):
            p = (r.get('owner_file') or '').strip()
            if p: own.add(p)
print('stage2 owner paths:', len(own))
base = 'bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d'
for ref in ['cleanup/stage2-s2a', 'origin/cleanup/stage2-s2a']:
    h = subprocess.run(['git','-C',repo,'rev-parse',ref],capture_output=True,text=True).stdout.strip()
    mb = subprocess.run(['git','-C',repo,'merge-base',base,h],capture_output=True,text=True).stdout.strip()
    ch = subprocess.run(['git','-C',repo,'diff','--name-only',mb,h,'--','TCSlib','TCSlib.lean'],capture_output=True,text=True).stdout.split()
    print(f'{ref} {h} merge-base {mb}: {len(ch)} changed TCSlib paths')
    own |= set(ch)
hit = [p for p in ours if p in own]
dirs = sorted({p.rsplit('/',1)[0] for p in ours})
near = sorted(p for p in own if any(p.startswith(d+'/') or p == d+'.lean' for d in dirs))
print('our paths:', len(ours)); print('EXACT HITS:', hit or 'none')
print('stage2 paths in our directories (information):', near or 'none')
