"""decldiff.py <repo> <rev1> <rev2> <file>...: public declarations added/removed across revs (file set taken together)."""
import sys, subprocess, re
repo, r1, r2 = sys.argv[1:4]; files = sys.argv[4:]
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private |protected |noncomputable |nonrec )*)(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(\S+)')
def names(rev):
    out = {}
    for f in files:
        r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True)
        if r.returncode: continue
        ns = []
        for l in r.stdout.split('\n'):
            m = re.match(r'^namespace\s+(\S+)', l)
            if m: ns.append(m.group(1)); continue
            m = re.match(r'^end\s+(\S+)\s*$', l)
            if m and ns and ns[-1] == m.group(1): ns.pop(); continue
            m = decl.match(l)
            if m and 'private' not in m.group(1):
                n = m.group(3); full = n[7:] if n.startswith('_root_.') else '.'.join(ns + [n])
                out[full] = (f.split('/')[-1], m.group(2))
    return out
a, b = names(r1), names(r2)
add = sorted(set(b) - set(a)); rem = sorted(set(a) - set(b))
print(f'added ({len(add)}):'); [print(f'  {n} [{b[n][1]}, {b[n][0]}]') for n in add]
print(f'removed ({len(rem)}):'); [print(f'  {n} [{a[n][1]}, {a[n][0]}]') for n in rem]
