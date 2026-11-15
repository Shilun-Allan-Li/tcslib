"""Read-only final source/style audit; outputs stay beside this script. No Lean or Lake."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

root = Path(sys.argv[1]).resolve()
out = Path(__file__).resolve().parent
rev = 'd842dc8f681f6b89499129f5b64a50d0e4587935'
base = '107f1e8c218733eac12d6b9bee6fece441271317'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, text=True)
def save(name, obj):
    (out / name).write_text(json.dumps(obj, indent=2) + '\n')
pat = re.compile(r'^(?P<private>private\s+)?(?:(?:noncomputable|unsafe|partial|protected)\s+)*'
                 r'(?P<kind>def|abbrev|theorem|lemma|structure|class|instance)\s+'
                 r'(?P<name>[^\s({:]+)')
files = git('diff', '--name-only', base, rev).splitlines()
records, sources, header_issues = [], [], []
main = ''
helpers = set()
for file in files:
    text = git('show', rev + ':' + file)
    lines = text.splitlines()
    prior = subprocess.run(['git', 'show', base + ':' + file], cwd=root,
                           text=True, capture_output=True)
    oldnames = {m.group('name') for row in prior.stdout.splitlines() if (m := pat.match(row))}
    info = dict(file=file, sha256=hashlib.sha256(text.encode()).hexdigest(),
                lines=len(lines), max_width=max(map(len, lines)),
                working_bytes_match=(root / file).read_text() == text,
                module_references='## References' in text)
    sources.append(info)
    missing = [s for s in ['## Main definitions', '## Main results', '## References']
               if s not in text]
    if missing:
        header_issues.append(dict(file=file, missing=missing))
    if file == 'TCSlib/Cryptography/Composability/SequentialZK.lean':
        main = text
    elif '/SequentialZK/' in file:
        helpers.add(Path(file).stem)
    starts = [(i, m) for i, row in enumerate(lines) if (m := pat.match(row))]
    names = {m.group('name') for _, m in starts}
    for ix, (i, m) in enumerate(starts):
        stop = starts[ix + 1][0] if ix + 1 < len(starts) else len(lines)
        before = '\n'.join(lines[:i])
        docs = list(re.finditer(r'/--[\s\S]*?-/', before))
        doc = ''
        if docs:
            d = docs[-1]
            if not re.sub(r'@\[[\s\S]*?\]', '', before[d.end():]).strip():
                doc = d.group()
        region = '\n'.join(lines[i:stop])
        pm = re.search(r':=\s*by\b', region)
        proof = re.split(r'\n(?=/--|namespace\b|end\b|section\b)',
                         region[pm.end():], maxsplit=1)[0].rstrip() if pm else ''
        records.append(dict(file=file, line=i + 1, name=m.group('name'),
                            kind=m.group('kind'), new=m.group('name') not in oldnames,
                            private=bool(m.group('private')), has_doc=bool(doc), doc=doc,
                            proof_lines=len(proof.splitlines()) if proof else 0,
                            sketch='**Proof sketch' in doc,
                            step_comments=len(re.findall(r'^\s*--', proof, re.M)),
                            literal_readers=[n for n in [m.group('name') + '_eq',
                                                        m.group('name') + '_iff'] if n in names],
                            generated_simps_reader='@[simps ' in before[-200:]))
imports = set(re.findall(r'^import TCSlib\.Cryptography\.Composability\.SequentialZK\.([^\s]+)',
                         main, re.M))
contents = set(re.findall(r'^\* `SequentialZK\.([^`]+)`:', main, re.M))
coverage = dict(helper_files=len(helpers), direct_helper_imports=len(imports),
                contents_entries=len(contents), missing_direct_imports=sorted(helpers - imports),
                extra_direct_imports=sorted(imports - helpers),
                missing_contents=sorted(helpers - contents), module_header_issues=header_issues)
diff = git('diff', '--unified=0', base, rev)
attrs = [row for row in diff.splitlines() if row.startswith('+') and not row.startswith('+++')
         and re.search(r'@\[simp(?:\s|\])|attribute\s+\[simp\]', row)]
summary = dict(revision=rev, base=base, changed_files=len(files),
               size_width_issues=[r for r in sources if r['lines'] > 1000 or r['max_width'] > 100],
               working_source_mismatches=[r['file'] for r in sources if not r['working_bytes_match']],
               new_public_missing_docs=[r for r in records if r['new'] and not r['private']
                                        and r['kind'] != 'instance' and not r['has_doc']],
               new_proof15_without_sketch=[r for r in records if r['new'] and r['proof_lines'] >= 15
                                          and not r['sketch']],
               new_proof25_without_stage_comments=[r for r in records if r['new']
                                                   and r['proof_lines'] >= 25
                                                   and not r['step_comments']],
               added_simp_attributes=attrs,
               new_public_defs_without_reader=[r for r in records if r['new'] and not r['private']
                                                and r['kind'] in ['def', 'abbrev']
                                                and not r['literal_readers']
                                                and not r['generated_simps_reader']],
               facade_and_headers=coverage)
save('source-audit.json', dict(summary=summary, source_files=sources, declarations=records))
new = [r for r in records if r['new']]
(out / 'new-source-declarations.tsv').write_text(
    'relative_source\tline\tkind\tdeclared_spelling\tvisibility\n' + ''.join(
        f"{r['file']}\t{r['line']}\t{r['kind']}\t{r['name']}\t"
        f"{'private' if r['private'] else 'public'}\n" for r in new))
width = {}
for line in (root / 'evidence/logs/final-width.log').read_text().splitlines():
    if (m := re.match(r'([^:]+): lines=(\d+), max_width=(\d+)', line)):
        width[m[1]] = [int(m[2]), int(m[3])]
save('stale-width-records.json', [dict(file=r['file'], prior_final_width_log=width.get(r['file']),
                                    pinned_revision_actual=[r['lines'], r['max_width']])
                                  for r in sources
                                  if width.get(r['file']) != [r['lines'], r['max_width']]])
lint = subprocess.run(['python3', '-I', 'scripts/campaign_style_lint.py',
                       'TCSlib/Cryptography', '--check8b'], cwd=root, text=True, capture_output=True)
(out / 'final-lint.stdout.log').write_text(lint.stdout)
(out / 'final-lint.stderr.log').write_text(lint.stderr)
def diagnostic_set(text):
    return {row for row in text.splitlines() if row.startswith(('FAIL', 'WARN'))}
old = diagnostic_set((root / 'evidence/logs/lint-base.log').read_text())
now = diagnostic_set(lint.stdout)
save('final-lint-diff.json', dict(exit=lint.returncode,
     base_fail=sum(s.startswith('FAIL') for s in old), base_warn=sum(s.startswith('WARN') for s in old),
     final_fail=sum(s.startswith('FAIL') for s in now), final_warn=sum(s.startswith('WARN') for s in now),
     added_lines=sorted(now - old), removed_lines=sorted(old - now)))
sweep = [json.loads(row) for row in (root / 'evidence/logs/sweep-final-01/results.jsonl')
         .read_text().splitlines() if row.strip()]
save('evidence-records-audit.json', dict(reviewed_revision=rev, changed_source_files=len(files),
     helper_files=len(helpers), new_source_written_declarations=len(new), sweep_rows=len(sweep),
     sweep_nonzero_rows=[r for r in sweep if r['exit'] or r['errors']],
     missing_sweep_raw_logs=[r['raw_log'] for r in sweep if not (root / r['raw_log']).is_file()],
     axiom_summary=json.loads((root / 'evidence/logs/final-axiom-summary.json').read_text()),
     six_commit_replay_record='evidence/logs/final-repair-replay.log',
     replay_has_exact_six_commits=(root / 'evidence/logs/final-repair-replay.log')
     .read_text().count('EXACT COMMIT ') == 6,
     signing_column_present='\tsigning\n' in (root / 'evidence/checkpointfinal-repair-patches/COMMITS.tsv')
     .read_text()))
print(json.dumps(summary, indent=2))
print('New source-written declarations:', len(new))
print('Read-only audit complete; no Lean or Lake invoked.')
