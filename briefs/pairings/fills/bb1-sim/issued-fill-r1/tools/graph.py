"""graph.py (t23 copy of the cs1 staging tool; change: audits/ is read too, and the
audits/*/Checks roots are visited after TCSlib, so the order is the full replay closure)
 <repo> <tree-ish> <outdir>: from git objects only (nothing checked out):
- mods.json: module -> [TCSlib imports in file order], mathlib imports
- order-full.txt: DFS post-order of modules reachable from TCSlib (imports in file order), root last
- SOURCE-full.txt: sha256 of each reachable module source
- sorries.txt: per module (in order) the declarations whose body has a `sorry` token
  (comments and strings stripped), as `<path>: <n>: <names>`, then TOTAL."""
import sys, os, re, json, subprocess, hashlib
repo, rev, outd = sys.argv[1:4]
os.makedirs(outd, exist_ok=True)
ls = subprocess.run(['git','-C',repo,'ls-tree','-r','--full-tree',rev,'--','TCSlib','TCSlib.lean','audits'],
                    capture_output=True,text=True,check=True).stdout.splitlines()
blobs = {}
for l in ls:
    meta, path = l.split('\t',1)
    if path.endswith('.lean'): blobs[path[:-5]] = meta.split()[2]
# batch read
p = subprocess.Popen(['git','-C',repo,'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
src = {}
for m,b in blobs.items():
    p.stdin.write((b+'\n').encode()); p.stdin.flush()
    hdr = p.stdout.readline().split(); n = int(hdr[2])
    data = p.stdout.read(n); p.stdout.read(1)
    src[m] = data
p.stdin.close(); p.wait()
imps, mlimps = {}, {}
for m,d in src.items():
    t = d.decode('utf-8')
    ims = re.findall(r'^import\s+(\S+)', t, re.M)
    imps[m] = [x.replace('.','/') for x in ims if x.startswith('TCSlib') or x.startswith('audits')]
    mlimps[m] = [x for x in ims if not (x.startswith('TCSlib') or x.startswith('audits'))]
order, seen = [], set()
sys.setrecursionlimit(100000)
def dfs(m):
    if m in seen: return
    seen.add(m)
    for x in imps.get(m, []):
        if x in src: dfs(x)
    order.append(m)
dfs('TCSlib')
for r in sorted(m for m in src if m.startswith('audits/') and m.endswith('/Checks')): dfs(r)
open(os.path.join(outd,'order-full.txt'),'w').write('\n'.join(order)+'\n')
with open(os.path.join(outd,'SOURCE-full.txt'),'w') as f:
    for m in order: f.write(hashlib.sha256(src[m]).hexdigest()+'  '+m+'.lean\n')
json.dump({'imports':imps,'mathlib':mlimps,'unreached':sorted(set(src)-seen)}, open(os.path.join(outd,'mods.json'),'w'))
# sorry scan
KW = r'(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class)'
def strip(t):
    t = re.sub(r'/-.*?-/', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), t, flags=re.S)
    t = re.sub(r'--[^\n]*', '', t)
    t = re.sub(r'"(?:\\.|[^"\\])*"', '""', t)
    return t
lines_out, total = [], 0
for m in order:
    t = strip(src[m].decode('utf-8'))
    ns, cur, names = [], None, []
    for l in t.split('\n'):
        mm = re.match(r'^namespace\s+(\S+)', l)
        if mm: ns.append(mm.group(1)); continue
        mm = re.match(r'^end\s+(\S+)\s*$', l)
        if mm and ns and ns[-1]==mm.group(1): ns.pop(); continue
        mm = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'+KW+r'\s+([^\s(:{\[]+)', l)
        if mm:
            nm = mm.group(1)
            cur = nm if nm.startswith('_root_.') else '.'.join(ns[-0:] and [] or [])+nm
            cur = nm
        if re.search(r'\bsorry\b', l) and cur and (not names or names[-1]!=cur):
            names.append(cur)
    if names:
        lines_out.append(f'{m}: {len(names)}: {", ".join(names)}'); total += len(names)
lines_out.append(f'TOTAL {total}')
open(os.path.join(outd,'sorries.txt'),'w').write('\n'.join(lines_out)+'\n')
print(len(order), 'reachable;', len(src)-len(seen), 'unreached;', total, 'sorry decls')
