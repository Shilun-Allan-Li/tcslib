"""LS-1's exhaustive candidate search (gate 89, round 4).

Usage: python3 -I ls1search.py <repo worktree> <rev> <out dir>
Every code line (comments and docstrings skipped) of TCSlib/**/*.lean at <rev> that
(A) touches `logSpace`'s definition: an `unfold`/`delta`/`change`/`show` step, `logSpace` in a
    rewrite or simp list, `logSpace_eq`, `logSpace.eq_*`, or a local alias `:= logSpace`; or
(B) cites a Mathlib upper bound of `Nat.log` by its argument or by a power (`log_le_self`,
    `log_lt_self`, `log_lt_of_lt_pow`, `log_le_of_lt_pow`, `log_lt_iff_lt_pow`,
    `lt_pow_iff_log_lt`, `log_le_of_le_pow`; the regex also catches `pow_log_le_self` and
    `clog_le_iff_le_pow`, which are classified as other facts).
A proof of `logSpace n ≤ n + 1` (or of `Nat.log 2 m + 1 ≤ m + 1`) must cite `logSpace_le_succ`,
unfold `logSpace` (A), or reach it by reduction through a (B) lemma; so (A) and (B) together with
the citations cover every candidate. Writes candidates.tsv and context.txt (each declaration's
hits with three lines before and two after).
"""
import subprocess, re, sys, collections
wt, rev, out = sys.argv[1:4]
def git(*a): return subprocess.run(['git', '-C', wt, *a], capture_output=True, text=True, check=True).stdout
files = [f for f in git('ls-tree', '-r', '--name-only', rev, '--', 'TCSlib').split() if f.endswith('.lean')]
A = re.compile(r'(unfold|delta|change)\s+[^\n]*logSpace|logSpace_eq|logSpace\.eq_|[\[,]\s*(Complexity\.)?logSpace\s*[\],]'
               r'|:=\s*(Complexity\.)?logSpace\b|show\s+Nat\.log 2')
B = re.compile(r'log_le_self|log_lt_self|log_lt_of_lt_pow|log_le_of_lt_pow|log_lt_iff_lt_pow|lt_pow_iff_log_lt'
               r'|log_le_iff_le_pow|log_le_of_le_pow')
DECL = re.compile(r'^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
rows, srcs = [], {}
for f in files:
    src = git('show', f'{rev}:{f}').split('\n'); srcs[f] = src
    decl, depth = '?', 0
    for i, l in enumerate(src, 1):
        inside = depth > 0
        j = 0
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
            j += 1
        if inside or l.lstrip().startswith(('--', '/-')): continue
        m = DECL.match(l)
        if m: decl = m.group(5)
        code = l.split('--')[0]
        for cls, rx in (('A', A), ('B', B)):
            if rx.search(code): rows.append((cls, f, i, decl, l.strip()))
with open(f'{out}/candidates.tsv', 'w') as o:
    o.write(f'# rev {git("rev-parse", rev).strip()}; {len(rows)} lines: A {sum(r[0] == "A" for r in rows)}, '
            f'B {sum(r[0] == "B" for r in rows)}\n')
    o.writelines(f'{c}\t{f}:{i}\t{d}\t{t}\n' for c, f, i, d, t in rows)
groups = collections.OrderedDict()
for c, f, i, d, t in rows: groups.setdefault((f, d), []).append(i)
res = []
for (f, d), ls in groups.items():
    src = srcs[f]; a, b = max(1, min(ls) - 3), min(len(src), max(ls) + 2)
    res.append(f'### {f} · {d} · lines {ls}')
    res += [f'{k:5d} {src[k - 1]}' for k in range(a, b + 1)]
open(f'{out}/context.txt', 'w').write('\n'.join(res) + '\n')
print(len(rows), 'lines', len(groups), 'declarations')
