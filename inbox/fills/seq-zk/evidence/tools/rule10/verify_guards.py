"""Verify complete native-name/install/mask/EOF log coverage against seal rows.

This independent postprocessor accepts any positive batch size. It reports
proof-body diagnostics separately; a complete harness is not a proof pass.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--record', required=True, type=Path)
parser.add_argument('--log', required=True, type=Path)
parser.add_argument('--out', required=True, type=Path)
args = parser.parse_args()
record = json.loads(args.record.read_text())
rows = {r['spelling']: r for r in record['rows']}
if len(rows) != len(record['rows']):
    raise RuntimeError('duplicate request identity')
text = args.log.read_text()
decoder = json.JSONDecoder()
components = {'install': {}, 'eof': {}}
names, installed, starts, masks, ends = {}, {}, {}, {}, {}
for line in text.splitlines():
    if 'G06-COMPONENT label=' in line:
        tail = line.split('G06-COMPONENT label=', 1)[1]
        label, tail = tail.split(' phase=', 1)
        phase, tail = tail.split(' spelling=', 1)
        name, tail = tail.split(' key=', 1)
        nk, length = decoder.raw_decode(tail)
        tail = tail[length:]
        if not tail.startswith(' home_key='):
            raise RuntimeError('missing native home identity')
        hk, length = decoder.raw_decode(tail[len(' home_key='):])
        remainder = tail[len(' home_key=') + length:]
        if phase not in components or remainder not in [' instance=true', ' instance=false']:
            raise RuntimeError('unknown component phase/metadata')
        if name not in rows or name in components[phase]:
            raise RuntimeError('extra/duplicate component identity: ' + name)
        row = rows[name]
        if nk != row['name_components'] or hk != row['home_components'] or remainder.endswith('true') != row['instance']:
            raise RuntimeError('native component metadata differs: ' + name)
        components[phase][name] = label
        names.setdefault(label, set()).add(name)
    if 'G06-NAME label=' in line:
        match = re.search(r'G06-NAME label=(\S+) spelling=(.*?) actual=(.*?) home=(.*?) before=.* installed=Lean.ReducibilityStatus.irreducible$', line)
        if not match:
            raise RuntimeError('malformed installation status')
        label, name, actual, home = match.groups()
        if name not in rows or name in installed or actual != name or home != rows[name]['home']:
            raise RuntimeError('installation name/home differs')
        installed[name] = label
    if 'G06-SEAL label=' in line:
        match = re.search(r'G06-SEAL label=(\S+) requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)$', line)
        if not match:
            raise RuntimeError('malformed seal installation count')
        label, count, active, already, verified = match.groups()
        if label in starts or int(count) != int(verified) or int(active) + int(already) != int(count):
            raise RuntimeError('duplicate/incomplete installation count')
        starts[label] = int(count)
    if 'G06-MASK ' in line:
        match = re.search(r'G06-MASK label=(\S+) phase=(install|eof) requested=(\d+) verified=(\d+)(.*)$', line)
        if not match:
            raise RuntimeError('malformed mask evidence')
        label, phase, count, verified, remainder = match.groups()
        key = (label, phase)
        if key in masks or int(count) != int(verified):
            raise RuntimeError('duplicate/incomplete mask evidence')
        if phase == 'install' and not re.fullmatch(r' removed=\d+ scope_depth=1 scoped_names=\d+ tc_state=preserved', remainder):
            raise RuntimeError('lookup/scope preservation not verified')
        if phase == 'eof' and remainder:
            raise RuntimeError('unexpected EOF mask metadata')
        masks[key] = int(count)
    if 'G06-SEAL-END label=' in line:
        match = re.search(r'G06-SEAL-END label=(\S+) requested=(\d+) verified=(\d+)$', line)
        if not match:
            raise RuntimeError('malformed EOF count')
        label, count, verified = match.groups()
        if label in ends or int(count) != int(verified):
            raise RuntimeError('duplicate/incomplete EOF count')
        ends[label] = int(count)
if any(set(c) != set(rows) for c in components.values()) or set(installed) != set(rows):
    raise RuntimeError('native coverage is not exactly the full request set')
for name in rows:
    if len({components['install'][name], components['eof'][name], installed[name]}) != 1:
        raise RuntimeError('batch identity changed between installation and EOF')
if set(names) != set(starts) or starts != ends:
    raise RuntimeError('installation/EOF batch sets differ')
for label, group in names.items():
    if starts[label] != len(group) or any(masks.get((label, phase)) != len(group) for phase in ['install', 'eof']):
        raise RuntimeError('batch/request/mask counts differ')
if sum(starts.values()) != len(rows):
    raise RuntimeError('batched total differs from full request count')
summary = {'record': str(args.record), 'raw_log': str(args.log), 'request_count': len(rows),
           'record_sha256': hashlib.sha256(args.record.read_bytes()).hexdigest(),
           'raw_log_sha256': hashlib.sha256(args.log.read_bytes()).hexdigest(),
           'native_identity_install_mask_eof_complete': True, 'batch_sizes': starts,
           'proof_error_diagnostics': len(re.findall(r'\.lean:\d+:\d+: error(?:\([^\n)]*\))?:', text))}
args.out.parent.mkdir(parents=True, exist_ok=True)
args.out.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary))
