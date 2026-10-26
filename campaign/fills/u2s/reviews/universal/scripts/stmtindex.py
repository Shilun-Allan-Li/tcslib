"""Index public theorem/lemma statements (docstring stripped, whitespace normalized, up to the
first top-level ':=') of Lean files. Usage: stmtindex.py <repo> <rev> <out.tsv> [<path> ...]
(no paths: every TCSlib/*.lean at <rev>)."""
import re, subprocess, sys
repo, rev, out = sys.argv[1:4]
paths = sys.argv[4:] or [p for p in subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, 'TCSlib'], capture_output=True, text=True, check=True).stdout.split('\n') if p.endswith('.lean')]
D = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec)\s+)*)(theorem|lemma)\s+(\S+)')
NS = re.compile(r'^namespace\s+(\S+)|^end\s+(\S+)')
rows = 0
with open(out, 'w', encoding='utf-8') as fo:
    for p in paths:
        src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{p}'], capture_output=True, text=True).stdout
        # strip comments
        o = []; i = 0; depth = 0
        while i < len(src):
            if src.startswith('/-', i): depth += 1; i += 2; continue
            if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
            if depth:
                if src[i] == '\n': o.append('\n')
                i += 1; continue
            if src.startswith('--', i):
                j = src.find('\n', i); i = len(src) if j < 0 else j; continue
            o.append(src[i]); i += 1
        L = ''.join(o).split('\n')
        stack = []
        for k, l in enumerate(L):
            m = NS.match(l)
            if m:
                if m.group(1): stack += m.group(1).split('.')
                elif m.group(2) and stack:
                    for c in reversed(m.group(2).split('.')):
                        if stack and stack[-1] == c: stack.pop()
                continue
            m = D.match(l)
            if not m: continue
            if 'private' in m.group(1): continue
            buf = []
            for t in range(k, min(k + 60, len(L))):
                buf.append(L[t])
                if ':=' in L[t] or re.search(r'\bwhere\b', L[t]): break
            s = ' '.join(' '.join(buf).split())
            s = s.split(':=')[0]
            name = '.'.join(stack + [m.group(3)])
            fo.write(f'{p}\t{k+1}\t{name}\t{s}\n'); rows += 1
print(rev, len(paths), 'files', rows, 'public statements')
