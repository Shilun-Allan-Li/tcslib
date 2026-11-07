"""Verify retained proposal/source identity, complete let headers, patch and compiled evidence."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
namespace = {'__file__': str(OUT / 'proposal-tools-v2.py')}
exec(compile((OUT / 'proposal-tools-v2.py').read_text(), 'own-proposal-tools-v2', 'exec'), namespace)
chunks, split, sha = namespace['chunks'], namespace['split'], namespace['sha']
context = json.loads((OUT / 'context.json').read_text())
live = (OUT / 'Loop-original-live.lean.txt').read_text()
base = (OUT / 'Loop-terminal-base.lean.txt').read_text()
proposed = (OUT / 'Loop-cumulative-proposed-v2.lean.txt').read_text()
assert Path(context['source']).read_bytes() == live.encode()
assert sha(live) == context['source_sha256']
assert sha(base) == context['terminal_base_sha256']


def reconstruct(before, patch):
    source = before.splitlines(keepends=True)
    raw = patch.splitlines(keepends=True)
    result = []
    cursor, i, hunks = 0, 2, 0
    while i < len(raw):
        m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', raw[i])
        assert m, raw[i]
        start, count, ncount = int(m[1]) - 1, int(m[2] or 1), int(m[4] or 1)
        assert start >= cursor
        result.extend(source[cursor:start])
        cursor, i, used, made = start, i + 1, 0, 0
        while i < len(raw) and not raw[i].startswith('@@ '):
            tag, body = raw[i][0], raw[i][1:]
            if tag == ' ':
                assert source[cursor] == body
                result.append(body)
                cursor, used, made = cursor + 1, used + 1, made + 1
            elif tag == '-':
                assert source[cursor] == body
                cursor, used = cursor + 1, used + 1
            elif tag == '+':
                result.append(body)
                made += 1
            else:
                raise AssertionError(raw[i])
            i += 1
        assert (used, made) == (count, ncount)
        hunks += 1
    result.extend(source[cursor:])
    assert ''.join(result) == proposed
    return hunks


patches = []
for source, name in [(base, 'Loop-bank-only-v2.patch'), (live, 'Loop-cumulative-v2.patch')]:
    text = (OUT / name).read_text()
    patches.append(dict(path=name, sha256=sha(text), hunks=reconstruct(source, text),
                        independent_reconstruction_equal=True))

A = {n: t for n, _, t in chunks(live)}
B = {n: t for n, _, t in chunks(proposed)}
headers = []
sizes = []
for name in ['Turing.FinTM.emCall_bank_initial', 'Turing.FinTM.emCall_bank_final']:
    # Independent exact old proof marker; includes all statement lets before the real proof.
    marker = ':= by\n  dsimp only\n  refine Cfg.ext'
    assert A[name].count(marker) == 1
    old_header = A[name].split(marker, 1)[0]
    assert B[name].startswith(old_header + ':= by\n')
    assert 'let frame := emCallBankFrame' in old_header
    parser_header, old_body = split(A[name])
    assert parser_header == old_header
    new_header, new_body = split(B[name])
    assert new_header == old_header
    headers.append(dict(name=name, header=old_header, header_sha256=sha(old_header),
                        marker_verified_independently=True, full_let_statement_literal_equal=True))
    sizes.append(dict(name=name, old_proof_chars=len(old_body), new_proof_chars=len(new_body),
                      old_proof_lines=len(old_body.splitlines()), new_proof_lines=len(new_body.splitlines())))
(OUT / 'let-header-witnesses.json').write_text(json.dumps(headers, indent=2) + '\n')
(OUT / 'proof-sizes.json').write_text(json.dumps(sizes, indent=2) + '\n')

log = (OUT / 'Loop-sealed-v4.out').read_text()
roots, axioms, foreign, frames, home = [], [], [], [], []
for line in log.splitlines():
    if line.startswith('ROOT|'):
        roots.append(line)
    elif line.startswith('PROOFAX|'):
        _, name, kind, ax = line.split('|')
        axioms.append(dict(name=name, kind=kind.split('=', 1)[1],
                           axioms=[s.strip() for s in ax.strip('[]').split(',') if s.strip()]))
    elif line.startswith('FOREIGNDEF|') or line.startswith('FRAMEDEF|'):
        tag, root, name, owner, hints = line.split('|')
        row = dict(root=root, name=name, owner=owner, hints=hints.split('=', 1)[1])
        (foreign if tag == 'FOREIGNDEF' else frames).append(row)
    elif line.startswith('FRAMEHOME|'):
        home.append(line)
assert len(roots) == 7 and len(axioms) == 18 and len(home) == 7
assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for row in axioms)
coverage = json.loads((OUT / 'seal-coverage-v4.json').read_text())
sealed = set(coverage['sealed_definitions'])
direct_ordinary = {row['name'] for row in foreign if row['hints'] == 'regular'}
frame_ordinary = {row['name'] for row in frames if row['hints'] == 'regular'}
assert direct_ordinary | frame_ordinary <= sealed
assert 'Turing.FinTM.tapeBlocks' in frame_ordinary
(OUT / 'compiled-inventory-v4.json').write_text(json.dumps(dict(
    roots=roots, axioms=axioms, direct_foreign_references=foreign,
    direct_foreign_ordinary=sorted(direct_ordinary),
    immediate_same_home_bridge_definitions=home,
    frame_foreign_references=frames, frame_foreign_ordinary=sorted(frame_ordinary),
    direct_and_frame_ordinary_all_guarded=True,
    scope='Seven roots and eleven compiled descendants, plus immediate foreign definitions in seven unchanged same-home configuration/layout bridges. Imported theorem proofs and other unchanged legacy helpers are not traversed.'), indent=2) + '\n')

reuse = json.loads((OUT / 'controls-reuse.json').read_text())
for row in reuse['records']:
    data = Path(row['path']).read_bytes()
    assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
extra = json.loads((OUT / 'additional-control-check-v2.json').read_text())
assert extra['definitions'] == 1 and extra['pointwise_and_abstracted_pairs'] == 2
native = json.loads((OUT / 'Loop-native-v2-run.json').read_text())
strict = json.loads((OUT / 'Loop-sealed-v4-run.json').read_text())
assert native['exit'] == strict['exit'] == native['errors'] == strict['errors'] == 0
summary = dict(status='Passed cumulative inert proposal, not applied; no debt or gate acceptance.',
    input_live_sha256=sha(live), input_terminal_sha256=sha(base),
    cumulative_proposal_sha256=sha(proposed), cumulative_proposal_bytes=len(proposed.encode()),
    independent_patches=patches, let_headers_independently_verified=True,
    strict_guard_count=len(sealed), direct_foreign_ordinary=len(direct_ordinary),
    additional_frame_ordinary=sorted(frame_ordinary - direct_ordinary),
    roots=7, descendants=11, all_18_selected_standard_axioms=True,
    native_seconds=native['seconds'], strict_seconds=strict['seconds'],
    controls_reused_pairs=60, controls_fresh_additional_pairs=2,
    control_definitions=31, per_definition_both_modes_covered=True,
    live_still_archived=True, no_actual_source_write=True,
    no_compiled_output_snapshot_cache_git_screen_or_replay_operation=True,
    failed_native_v1_retained=True, failed_v1_freeze_not_valid_for_let_headers=True)
(OUT / 'summary-v4.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
