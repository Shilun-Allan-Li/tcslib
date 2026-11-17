"""dup_inventory.py <repo> <base> <file>... (gsw-6a-fills, new; check 11): every new private helper of the owned files
(name, file, lines of the whole declaration with its docstring), and the helpers whose short name appears in more
than one owned file (the same private fact proved in several files, which privacy forces), with the copied lines
per file and their fraction of that file's fill (head lines minus base lines)."""
import sys, re, subprocess, collections
repo, base = sys.argv[1:3]; files = sys.argv[3:]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev)\s+(\S+)')
CONT = re.compile(r'^(termination_by|decreasing_by)\b')
def show(rev, f): return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True).stdout.decode()
helpers = collections.defaultdict(list); fill = {}
for f in files:
    b = show(base, f); h = show('HEAD', f).split('\n')
    fill[f] = len(h) - len(b.split('\n'))
    bp = {m.group(3) for l in b.split('\n') if (m := DECL.match(l))}
    for i, l in enumerate(h):
        m = DECL.match(l)
        if not m or not (m.group(1) or '').strip().startswith('private') or m.group(3) in bp: continue
        a = i
        if h[i - 1].rstrip().endswith('-/'):
            a = i - 1
            while not h[a].startswith('/--'): a -= 1
        j = i + 1
        while j < len(h) and (not h[j] or h[j][0].isspace() or CONT.match(h[j])): j += 1
        while not h[j - 1].strip(): j -= 1
        helpers[m.group(3).split('.')[-1]].append((f, i + 1, j - a))
print('# all new private helpers: short name, file:line, lines (docstring + declaration)')
for n in sorted(helpers):
    for f, ln, k in helpers[n]: print(f'HELPER\t{n}\t{f}:{ln}\t{k}')
print('# helpers proved in more than one owned file')
per = collections.Counter()
for n in sorted(helpers):
    if len(helpers[n]) > 1:
        print(f'MULTI\t{n}\t' + '; '.join(f'{f.split("/")[-1]}:{ln} ({k} lines)' for f, ln, k in helpers[n]))
        for f, ln, k in helpers[n]: per[f] += k
for f in files:
    print(f'COPIED-LINES\t{f}\t{per[f]}\tof fill {fill[f]}\t{100 * per[f] / max(fill[f], 1):.1f}%')
