"""series.py <repo> <from> <to> <outdir>: `git format-patch <from>..<to>` into <outdir>, and
<outdir>/COMMITS.tsv: one row per commit (in order) with its hash, author name, email and date,
committer name, email and date (raw `git log` %an %ae %aI %cn %ce %cI) and its signing (`none` when
the commit carries no gpgsig header, else the signature format)."""
import sys, subprocess, os
repo, a, b, out = sys.argv[1:5]
os.makedirs(out, exist_ok=True)
subprocess.run(['git', '-C', repo, 'format-patch', '-q', '--no-signature', f'{a}..{b}', '-o', out], check=True)
fmt = '%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI'
rows = subprocess.run(['git', '-C', repo, 'log', '--reverse', f'--format={fmt}', f'{a}..{b}'],
                      capture_output=True, text=True, check=True).stdout.strip().split('\n')
with open(os.path.join(out, 'COMMITS.tsv'), 'w') as f:
    f.write('hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n')
    for r in rows:
        h = r.split('\t')[0]
        raw = subprocess.run(['git', '-C', repo, 'cat-file', 'commit', h], capture_output=True, text=True).stdout
        sig = 'none'
        for l in raw.split('\n\n')[0].split('\n'):
            if l.startswith('gpgsig'): sig = 'ssh' if 'SSH SIGNATURE' in raw else 'openpgp'
        f.write(r + '\t' + sig + '\n')
print(len(rows), 'commits')
