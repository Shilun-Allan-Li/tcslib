#!/usr/bin/env python3
"""UNRUN temporary M4 report renderer; no Git, Lean, cache, subprocess or gate execution.

Only reads supplied artifacts/current source and writes a fresh /private/tmp directory.
READY requires all M4 originals/helpers plus supplied fresh local evidence. It never
claims the complete final canonical gates, publication, or Phase B target truth.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from string import Template

AREA = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
BASE = '5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
M3_HEAD = '04249b85e80a007dc5845077a18a365d5150e14b'
M3_EXCHANGE = '2a9ccadc2772789ace445490f6df8d231ff1221b'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def cell(value):
    return str(value).replace('|', '\\|').replace('\n', ' ')


def table(rows):
    return '\n'.join('| ' + ' | '.join(cell(x) for x in row) + ' |' for row in rows)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    input_path = Path(args.input).resolve()
    home = input_path.parent
    data = json.loads(input_path.read_text())
    root = Path(data['root']).resolve()
    out = Path(args.out).resolve()
    need(out.is_relative_to(Path('/private/tmp')) and not out.exists(),
         'Use a fresh output directory under /private/tmp; never active evidence/REPORT.md')
    need(data['schema'] == 1 and data['stage'] in {'IN_PROGRESS', 'READY_FOR_M4_PACKAGING'},
         'Invalid report stage/schema')
    ready = data['stage'] == 'READY_FOR_M4_PACKAGING'
    need(re.fullmatch(r'[0-9a-f]{40}', data['source_head']), 'Invalid exact source hash')
    historical_path = home / 'baseline/M3-REPORT.md'
    historical = historical_path.read_bytes()
    need(sha(historical_path) == data['baseline_sha256'], 'Historical M3 bytes changed')
    m3_record = json.loads((home / 'baseline/M3-delivery.json').read_text())
    need(m3_record['published'] and m3_record['exchange_commit'] == M3_EXCHANGE
         and m3_record['source_head'] == M3_HEAD and m3_record['payload_files'] == 6349
         and m3_record['exact_committed_path_set']
         and not m3_record['committed_sha256_mismatches'], 'M3 delivery binding differs')
    plan = json.loads((home / data['declaration_plan']).read_text())
    originals = [r for r in plan if r['kind'] == 'frozen_original']
    helpers = [r for r in plan if r['kind'] == 'theorem_only_helper']
    need(len(originals) == 16 and len(helpers) == 13
         and len({r['name'] for r in plan}) == 29, 'M4 scope changed; explicit review required')
    artifacts = {}

    def artifact(key):
        ref = data['fresh_gates'][key]
        if ref is None:
            need(not ready, 'READY lacks fresh artifact: ' + key)
            return None
        need(isinstance(ref, dict) and set(ref) == {'path', 'sha256'}, 'Bad artifact ref: ' + key)
        path = Path(ref['path'])
        if not path.is_absolute():
            path = root / path
        path = path.resolve()
        need(path.is_file() and sha(path) == ref['sha256'], 'Artifact hash differs: ' + key)
        artifacts[key] = {'path': str(path), 'sha256': sha(path)}
        return path

    def json_artifact(key):
        path = artifact(key)
        return None if path is None else json.loads(path.read_text())

    gate_data = {key: json_artifact(key) for key in [
        'committed_inventory', 'source_inventory', 'static_summary', 'freeze_summary',
        'selected_axiom_summary', 'selected_names', 'selected_owner_names', 'headline_names',
        'warning_summary', 'slot_summary', 'overlap_summary']}
    build_path = artifact('all_owner_build')
    ledger_path = artifact('commits_ledger')
    inventory = gate_data['committed_inventory']
    if inventory is None:
        files = data['source_files_observed']
        source_qualification = ('This is an in-progress worktree observation at the root-supplied '
                                'head context, not a fresh committed-source inventory.')
    else:
        need(inventory['head'] == data['source_head'] and inventory['base'] == BASE,
             'Committed inventory head/base differs')
        need(inventory['mode'] == 'COMMITTED_HEAD', 'Historical/worktree inventory cannot bind READY')
        files = [inventory['owner_sources'][m]['file'] for m in inventory['owners']]
        need(len(files) == len(set(files)), 'Duplicate owner paths')
        for f in files:
            need(sha(root / f) == inventory['source_sha256'][f], 'Current source differs: ' + f)
        source_qualification = ('The supplied committed inventory and captured source hashes '
                                'bind this source snapshot; Git ancestry/diff verification is '
                                'a separate root-owned gate, not performed by this renderer.')
    observed = {'TCSlib/Cryptography/Obfuscation.lean'} | {
        str(p.relative_to(root)) for p in
        (root / 'TCSlib/Cryptography/Obfuscation').rglob('*.lean')}
    need(set(files) == observed, 'Filesystem owner coverage differs from the supplied inventory')
    source_rows, source_texts = [], {}
    for f in files:
        path = root / f
        need(path.is_file() and not path.is_symlink(), 'Owner source not an ordinary file: ' + f)
        text = path.read_text()
        source_texts[f] = text
        lines = text.splitlines()
        source_rows.append({'file': f, 'lines': len(lines),
                            'max_width': max(map(len, lines), default=0), 'sha256': sha(path)})
    need(all(r['lines'] <= 1000 and r['max_width'] <= 100 for r in source_rows),
         'Source size/width limit exceeded')
    steps = []
    for p in sorted((root / 'evidence/steps').glob('*/step.json')):
        if p.parent.name.isdecimal():
            row = json.loads(p.read_text())
            row['number'] = int(p.parent.name)
            row['record'] = str(p.relative_to(root))
            steps.append(row)
    need([r['number'] for r in steps] == list(range(1, len(steps) + 1)), 'Step gap/duplicate')
    for row in plan:
        leaf = row['name'].split('.')[-1]
        matching = [s for s in steps if s['number'] > 134 and s['name'].split('.')[-1] == leaf]
        need(len(matching) <= 1, 'Duplicate saved proof step: ' + row['name'])
        record = matching[0] if matching else None
        row['step'] = record['number'] if record else None
        row['status'] = record['status'] if record else 'PENDING_NO_CHECKED_STEP_BOUND'
        row['step_record'] = record['record'] if record else None
        found = []
        pattern = r'^[ \t]*(?:theorem|lemma)[ \t]+(?:Params\.|Internal\.)?' + re.escape(leaf) + r'\b'
        for f, text in source_texts.items():
            found.extend(f + ':' + str(text[:m.start()].count('\n') + 1)
                         for m in re.finditer(pattern, text, re.M))
        need(len(found) <= 1, 'Ambiguous source theorem anchor: ' + row['name'])
        row['source_anchor'] = found[0] if found else None
    checked = [s for s in steps if s['status'] == 'CHECKED_PASS']
    pending = [s['number'] for s in steps if s['status'] != 'CHECKED_PASS']
    checked_orig = sum(r['status'] == 'CHECKED_PASS' for r in originals)
    checked_help = sum(r['status'] == 'CHECKED_PASS' for r in helpers)
    if ready:
        need(checked_orig == 16 and checked_help == 13 and not pending,
             'M4 still has unchecked original/helper bodies or saved steps')
        need(all(r['source_anchor'] for r in plan), 'Missing final M4 theorem source')
        need(all(c.get('subject') for c in data['source_commits']), 'Exact M4 commit subjects missing')
        need(data['source_commits'][-1]['hash'] == data['source_head'], 'Last source commit is not head')
    for commit in data['source_commits']:
        need(re.fullmatch(r'[0-9a-f]{40}', commit['hash']), 'Invalid commit hash')
        if ledger_path:
            need(commit['hash'] in ledger_path.read_text(), 'Commit absent from exact ledger')
    freeze = gate_data['freeze_summary']
    if freeze:
        need(freeze['status'] == 'FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS'
             and freeze['frozen_headers'] == 670 and not freeze['globally_removed']
             and not freeze['globally_changed_headers'] and not freeze['approved_prose_updates'],
             'Frozen header/prose preservation failed')
        need(freeze['current_owners'] == len(files)
             and set(freeze['current_source_sha256']) == set(files)
             and all(freeze['current_source_sha256'][f] == sha(root / f) for f in files),
             'Freeze source coverage/hashes differ')
    statements = gate_data['source_inventory']
    if statements:
        need(statements['head'] == data['source_head'], 'Source-inventory head differs')
        need(set(statements['source_sha256']) == set(files)
             and all(statements['source_sha256'][f] == sha(root / f) for f in files),
             'Source-inventory coverage/hashes differ')
        if ready:
            need(statements['named_sorry_bodies'] == 16,
                 'READY M4 must retain exactly M5 seven + M6 nine frozen original holes')
            later = {'jls_secure', 'jls_subexpSmall', 'jls_subexpSecure', 'theorem41',
                     'theorem41_subexp', 'exists_sprg_raw', 'exists_sprg_raw_subexp',
                     'Params.realizable_of_targets', 'Params.evalEfficient_of_target',
                     'Params.idSampEfficient_of_targets', 'Params.sdSampEfficient_of_targets',
                     'Params.lpnSamplerEfficient_of_target', 'Params.hasComplexityEff_of_target',
                     'theorem41_of_targets', 'exists_sprg_of_targets', 'exists_sprg_of_targets_subexp'}
            need(set(statements['remaining_named_obligations']) == {AREA + n for n in later},
                 'Remaining obligations differ from the exact frozen M5/M6 scope')
    static = gate_data['static_summary']
    if static:
        need(static['head'] == data['source_head'] and static['owners'] == len(files)
             and static['all_widths_pass'] and not static['new_campaign_fail_warn'],
             'Fresh static head/coverage/style differs')
        need(all(r['rc'] == 0 for n, r in static['checks'].items() if n != 'campaign'),
             'Fresh static check failed')
    build_rows = []
    if build_path:
        latest = {}
        for line in build_path.read_text().splitlines():
            row = json.loads(line)
            if 'module' in row:
                latest[row['module']] = row
        expected = {f[:-5] for f in files}
        need(expected <= set(latest), 'All-owner build lacks expected modules')
        for module in sorted(expected):
            row = latest[module]
            log = build_path.parent / 'mods' / (module.replace('/', '_') + '.log')
            need(row['rc'] == row['errors'] == row['error_forms'] == 0
                 and row['source_sha256'] == sha(root / (module + '.lean'))
                 and row['log_sha256'] == sha(log), 'Fresh owner build failure/stale hash: ' + module)
            need(row['head_at_start'] == data['source_head'], 'Owner build was not at the current head')
            object_path = Path(data['environment_tree']) / (module + '.olean')
            need(object_path.is_file() and row['object_sha256'] == sha(object_path),
                 'Current owner object differs from the checked build: ' + module)
            need(not re.search(r'error[:(]', log.read_text()), 'Independent build error form: ' + module)
            build_rows.append(row)
    warnings = gate_data['warning_summary']
    if warnings:
        need(warnings['head'] == data['source_head'] and not warnings['other_warnings'],
             'Unexpected warning/head mismatch')
        if statements:
            need(warnings['expected_remaining_sorry_warnings'] == statements['named_sorry_bodies'],
                 'Remaining-sorry warning count differs from source holes')
    ax = gate_data['selected_axiom_summary']
    selected, headline_axioms = {}, {}
    if ax:
        need(ax['head'] == data['source_head'], 'Selected-axiom summary head differs')
        names = gate_data['selected_names']
        headline_names = gate_data['headline_names']
        need(isinstance(names, list) and names and len(names) == len(set(names)), 'Bad selected-name list')
        need(isinstance(headline_names, list) and headline_names
             and len(headline_names) == len(set(headline_names)), 'Bad headline-name list')
        selected_owners = gate_data['selected_owner_names']
        need(isinstance(selected_owners, list) and selected_owners
             and len(selected_owners) == len(set(selected_owners))
             and set(selected_owners) <= set(inventory['owners']), 'Selected owner scope differs')
        selected = ax['probes'][data['fresh_gates']['selected_probe']]['axioms']
        headline_axioms = ax['probes'][data['fresh_gates']['headline_probe']]['axioms']
        need(set(selected) == set(names) and set(headline_axioms) == set(headline_names),
             'Selected/headline print key sets differ from supplied exact lists')
        need(all(set(a) <= STANDARD for a in selected.values()), 'Selected theorem retains nonstandard axioms')
        need(all(set(a) <= STANDARD | {'sorryAx'} for a in headline_axioms.values()),
             'Headline has undeclared nonstandard axiom')
        combined_axioms = dict(selected)
        for name, axioms in headline_axioms.items():
            need(name not in combined_axioms or set(combined_axioms[name]) == set(axioms),
                 'Selected/headline axiom prints disagree: ' + name)
            combined_axioms[name] = axioms
        if ready:
            need(all(r['name'] in combined_axioms and set(combined_axioms[r['name']]) <= STANDARD
                     for r in plan), 'M4 original/helper absent from standard-only print scope')
            need(all(n in combined_axioms and set(combined_axioms[n]) <= STANDARD
                     for n in freeze['new_theorems_reported']), 'A cumulative helper is not standard-only')
    slot = gate_data['slot_summary']
    if slot:
        need(slot['status'] == 'PASS_WITH_EXACT_RECORDED_HISTORICAL_VIOLATION'
             and slot['all_tagged_wrapper_acquisitions_serial'] is False
             and slot['max_concurrent_job_wrappers'] == 2
             and slot['post_correction_serial'] is True and not slot['active'],
             'Slot-history exception/suffix qualification differs')
        k = slot['known_overlap_exception']
        need((k['prior_pid'], k['owner_pid'], k['start'], k['end']) ==
             ('93883', '93983', '2026-11-18T15:07:45Z', '2026-11-18T15:07:48Z'),
             'Known historical overlap identity differs')
        extracted = Path(artifacts['slot_summary']['path']).parent / 'slots-io-sprg.log'
        need(sha(extracted) == slot['extracted_log_sha256'], 'Extracted tagged log hash differs')
        tagged = [line for line in Path(slot['source']).read_bytes().splitlines(keepends=True)
                  if len(line.rstrip(b'\r\n').split(b' ', 4)) >= 4
                  and line.rstrip(b'\r\n').split(b' ', 4)[3] == b'tag=io-sprg']
        need(hashlib.sha256(b''.join(tagged)).hexdigest() == slot['extracted_log_sha256'],
             'New io-sprg wrapper events occurred after the supplied fresh slot audit')
    overlap = gate_data['overlap_summary']
    if overlap:
        need(overlap['head'] == data['source_head'], 'Overlap review snapshot head differs')
        admission = {r['name']: r for r in overlap['admission_rows']}
        need(len(admission) == len(overlap['admission_rows'])
             and set(admission) == {r['name'] for r in plan}, 'M4 overlap admission scope differs')
        need(all(r['reviewed'] and r['name_shape_artifacts'] and r['exact_artifacts']
                 and r['apply_artifacts'] and r['scope'] in
                 {'PUBLIC_ONLY_CORE', 'ACTUAL_READER_TARGET_ABSENT'} for r in admission.values()),
             'Incomplete/invalid search scope; a reuse control is not isolated admission')
        for row in admission.values():
            if row['scope'] == 'ACTUAL_READER_TARGET_ABSENT':
                need(row['target_absent_from_bound_imports'], 'Actual reader can match its own target')
            for key in ['name_shape_artifacts', 'exact_artifacts', 'apply_artifacts']:
                for ref in row[key]:
                    f = Path(ref['path'])
                    if not f.is_absolute():
                        f = root / f
                    need(sha(f) == ref['sha256'], 'Overlap provenance hash differs: ' + str(f))
    if ready:
        need(all(gate_data.values()) and build_path and ledger_path,
             'READY requires every supplied fresh gate/reference')
    observations = data.get('observations', {})
    quantity = [
        ('Owned source files', len(files), 'Exact supplied committed inventory' if inventory else
         'Filesystem snapshot only; fresh committed inventory PENDING'),
        ('Explicit source headers', freeze['current_headers'] if freeze else observations.get('headers',
         'PENDING'), 'Fresh freeze census' if freeze else 'Dispatch snapshot; fresh census PENDING'),
        ('Cumulative helpers inserted', len(freeze['new_theorems_reported']) if freeze else
         observations.get('cumulative_helpers_inserted', 'PENDING'),
         'Inserted is not checked; the separate checked-helper row determines proof status'),
        ('Source size/width', f"{sum(r['lines'] for r in source_rows):,} lines; largest "
         f"{max(r['lines'] for r in source_rows)}; width {max(r['max_width'] for r in source_rows)}",
         'Current filesystem byte/line measurement; committed binding separately required'),
        ('Saved proof records', f'{len(steps)} records; {len(checked)} CHECKED_PASS; pending {pending}',
         'Saved step JSON records; inserted/unverified bodies are not passes'),
        ('Completed originals', 114 + checked_orig, f'M3 historical 114 + M4 checked {checked_orig}'),
        ('Checked theorem-only helpers', 20 + checked_help, f'M3 historical 20 + M4 checked {checked_help}'),
        ('Remaining original direct holes', statements['named_sorry_bodies'] if statements else
         observations.get('remaining_original_direct_holes', 'PENDING'),
         'Fresh source inventory' if statements else 'Dispatch snapshot; fresh inventory PENDING'),
        ('Frozen headers/prose and moves', f"670 unchanged; {len(freeze['moves'])} exact moves" if freeze
         else 'PENDING fresh M4 global freeze (dispatch snapshot: 93 moves)',
         artifacts.get('freeze_summary', {}).get('path', 'Fresh check PENDING'))]
    original_rows = [(r['name'].removeprefix(AREA), r['source_anchor'] or 'PENDING owner insertion',
                      (str(r['step']) + ': ' if r['step'] else '') + r['status']) for r in originals]
    helper_rows = [(r['name'].removeprefix(AREA), r['source_anchor'] or 'PENDING proposed owner',
                    (str(r['step']) + ': ' if r['step'] else '') + r['status']) for r in helpers]
    gates = []
    for key in data['fresh_gates']:
        if key in {'selected_probe', 'headline_probe'}:
            continue
        gates.append((key, ('Supplied/hash-checked: ' + artifacts[key]['path']) if key in artifacts
                      else 'PENDING; no fresh pass claimed'))
    if selected:
        gates.append(('Selected axiom scope', f'{len(selected)} exact selected names, standard-only; '
                      'selected scope, not full stored-root census'))
        gates.extend(('Headline ' + n.removeprefix(AREA), ', '.join(a) or '(no axioms)')
                     for n, a in sorted(headline_axioms.items()))
    if slot:
        gates.append(('Tagged wrapper counts', f"{slot['acquisitions']} acquisitions; historical max2/"
                      f"serial=false; post-correction {slot['post_correction']['acquisitions']} "
                      'acquisitions serial=true; active0. Wrapper-snapshot qualification only.'))
    commit_rows = [(c['hash'], c['role'], c.get('subject') or 'PENDING exact subject/COMMITS.tsv')
                   for c in data['source_commits']]
    search_rows = [
        ('Four PRG helpers', 'M4-PRG-name-shape, helper-specs-v3, fresh exact/apply core bindings; '
         'sdCore uses publicMap v2. Most-specific shared realization/coin-prefix reuse is explicit.'),
        ('Six hybrid originals', 'M4-PRG name/shape and endpoint/statistical-hop core probes; '
         'semantic acceptance only, actual joint law, no uniform-index premise.'),
        ('Six encoding originals', 'M4Advice 01–06 mathematical cores; shared canonical encoding and '
         'fixed-width APIs. Owned Basic reuse controls are separate, not public-only admission.'),
        ('PRG hop', 'M4PRG prg_hop_fix_advice_core and four checked helper bodies; advice family '
         'before all realizing adversaries/all κ, finite averaging and existing prefix law.'),
        ('LPN helper01–03', 'Actual-definition probes import earlier LPN/Defs with target absent; '
         'canonical challenge and mandatory realization readers. V1/V2 repairs remain attributed.'),
        ('LPN helper04–09 and hop', ('Checked bodies and fresh provenance bound above. ' if ready else
         'PENDING complete checked bodies and fresh provenance until bound above. ') +
         '04 joint real draw; 05/06 preprocessing; 07/08 sections; 09 advice averaging.'),
        ('lemma42/prop41', ('Checked source/probe records bound above; ' if ready else
         'PENDING actual checked source/probe records until bound above; ') +
         'finite hybrid triangle/telescope reuses public APIs and preserves every-realiser quantifiers.')]
    if overlap:
        search_rows.append(('Fresh exact admission ledger', artifacts['overlap_summary']['path'] +
                            '; exact 29-row scope, artifact hashes checked; outcomes are not proofs'))
    status = (f"All sixteen frozen M4 original bodies and thirteen M4 theorem-only helpers have "
              f"saved CHECKED_PASS records at `{data['source_head']}`. The supplied fresh local "
              'M4 artifacts have been cross-checked. **M4 packaging and publication remain pending.**'
              if ready else f"**M4 is ongoing and is not complete.** Source-head context is "
              f"`{data['source_head']}`. {checked_orig}/16 M4 originals and {checked_help}/13 "
              f"planned M4 helpers have saved CHECKED_PASS records. Pending saved steps: {pending}. "
              'Fresh final M4 local gates, packaging and publication remain pending.')
    pending_lpn = [r['name'].removeprefix(AREA) for r in helpers[7:] if r['status'] != 'CHECKED_PASS']
    remaining = ('M4 local proof work is complete; the sixteen M5/M6 frozen original obligations '
                 'remain (seven raw security/existence and nine target links/assemblies). Full '
                 'fresh final canonical gates remain pending; Phase B targets remain hypotheses.'
                 if ready else 'M4 originals still pending: ' + ', '.join(
                     r['name'].removeprefix(AREA) for r in originals if r['status'] != 'CHECKED_PASS') +
                 '. M5 and M6 remain unfinished. No transitive sorryAx count is inferred by '
                 'subtracting source holes or selected prints.')
    mapping = dict(stage_label='READY for packaging' if ready else 'IN PROGRESS', status_text=status,
                   source_head=data['source_head'], source_qualification=source_qualification,
                   quantity_rows=table(quantity), commit_rows=table(commit_rows),
                   original_rows=table(original_rows), helper_rows=table(helper_rows),
                   lpn_pending_text=('Pending/unverified helper04–09 names: ' + ', '.join(pending_lpn) +
                                     '; these are explicit placeholders, not checked proofs.')
                   if pending_lpn else 'All six helper04–09 bodies have bound CHECKED_PASS records.',
                   search_rows=table(search_rows), gate_rows=table(gates),
                   freeze_text=('Fresh source guard matches all current source hashes. Its '
                                'WORKTREE_CANDIDATE label is retained; committed binding and '
                                'full kernel types remain separate checks.') if freeze else
                   'Fresh M4 freeze binding is PENDING; no current preservation pass is inferred '
                   'from earlier prefix snapshots.', remaining_text=remaining,
                   delivery_text='PENDING packaging/publication; no M4 exchange hash is claimed.',
                   historical_report=historical.decode())
    template_path = home / data['report_template']
    rendered = Template(template_path.read_text()).substitute(mapping)
    need(historical in rendered.encode(), 'Historical M3 bytes were not preserved')
    out.mkdir(parents=True)
    report = out / ('REPORT-M4.READY.md' if ready else 'REPORT-M4.IN_PROGRESS.md')
    report.write_text(rendered)
    (out / 'source-rows.json').write_text(json.dumps(source_rows, indent=2) + '\n')
    (out / 'current-declaration-status.json').write_text(json.dumps(plan, indent=2) + '\n')
    binding = dict(stage=data['stage'], source_head=data['source_head'], report_sha256=sha(report),
                   input_sha256=sha(input_path), template_sha256=sha(template_path),
                   historical_M3_report_sha256=sha(historical_path),
                   M3_delivery_record_sha256=sha(home / 'baseline/M3-delivery.json'),
                   artifact_sha256=artifacts, source_sha256={r['file']: r['sha256'] for r in source_rows},
                   gate_execution='NONE: renderer only cross-checks supplied artifacts',
                   current_report_written=False, Git_Lean_cache_source_mutation=False,
                   M4_publication='PENDING; later external delivery record required')
    (out / 'report-binding.json').write_text(json.dumps(binding, indent=2) + '\n')
    print(data['stage'], str(report), sha(report))


if __name__ == '__main__':
    main()
