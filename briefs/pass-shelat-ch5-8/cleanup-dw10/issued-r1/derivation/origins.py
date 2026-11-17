#!/usr/bin/env python3
"""origins.py <repo> <base> <out.tsv>
For every TCSlib/**.lean (and TCSlib.lean) at <base>: walk the first-parent history of <base>
oldest-first; at each first-parent commit C, diff C^1..C (for a merge: everything the merged
branch brought in) with rename detection, and track each path's origin (the first-parent commit
whose diff added it; a rename carries the origin forward) and every first-parent commit that
added, renamed or modified it. Writes path, origin commit, origin label (PR branch or subject),
origin date, and the labels of all touching first-parent commits."""
import subprocess, sys, re
repo, base, out = sys.argv[1:4]
def g(*a):
    return subprocess.run(['git', '-C', repo, *a], check=True, capture_output=True, text=True).stdout
fp = g('rev-list', '--first-parent', '--reverse', '--format=%H%x09%P%x09%cI%x09%s', base).splitlines()
commits = []
for line in fp:
    if line.startswith('commit '):
        continue
    h, parents, date, subj = line.split('\t', 3)
    m = re.match(r'Merge pull request (#\d+) from [^/]+/(\S+)', subj)
    label = f'{m.group(1)} {m.group(2)}' if m else 'direct: ' + subj[:90]
    commits.append((h, parents.split(), date, label))
origin, touch = {}, {}
for h, ps, date, label in commits:
    if not ps:
        diff = g('show', '--name-status', '--format=', '-M', h)
    else:
        diff = g('diff', '--name-status', '-M', ps[0], h)
    for row in diff.splitlines():
        f = row.split('\t')
        st = f[0]
        if st.startswith('R'):
            old, new = f[1], f[2]
            if old in origin:
                origin[new] = origin.pop(old); touch[new] = touch.pop(old) + [label + ' (R)']
            else:
                origin[new] = (h, label, date); touch[new] = [label + ' (R-from-unknown)']
        elif st.startswith('C'):
            new = f[2]; origin[new] = (h, label, date); touch[new] = [label + ' (C)']
        elif st == 'A':
            origin[f[1]] = (h, label, date); touch[f[1]] = [label]
        elif st == 'D':
            origin.pop(f[1], None); touch.pop(f[1], None)
        elif st.startswith('M') or st.startswith('T'):
            if f[1] in touch:
                touch[f[1]].append(label + ' (M)')
files = [p for p in g('ls-tree', '-r', '--name-only', base, '--', 'TCSlib', 'TCSlib.lean').splitlines()
         if p.endswith('.lean')]
with open(out, 'w') as fh:
    fh.write('path\torigin_commit\torigin_label\torigin_date\ttouching_first_parent_commits\n')
    for p in sorted(files):
        o = origin.get(p, ('?', '?', '?'))
        fh.write('\t'.join([p, o[0], o[1], o[2], ' | '.join(dict.fromkeys(touch.get(p, [])))]) + '\n')
print(len(commits), 'first-parent commits;', len(files), 'files;', sum(1 for p in files if p not in origin), 'without origin')
