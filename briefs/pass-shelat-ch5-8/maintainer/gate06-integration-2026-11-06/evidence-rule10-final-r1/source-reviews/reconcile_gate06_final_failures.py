"""Propose source-identity witnesses for a completed fresh Gate06 seal survey.

Review before running. Reads exact Git base/head, archived final evidence and
historical inventories. Writes only a new directory under ignored repairs.
No Lean, cache, source/evidence/Git mutation, waiver, or pass decision exists.
"""
from pathlib import Path
import argparse, collections, csv, hashlib, importlib.util, io, json, re, subprocess, sys

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
REPAIRS = ROOT / '.lake/ps-maintainer/gate06/repairs'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
E = MAIN / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1'
HIST = MAIN / 'briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r2/r6c'
LEGACY = REPAIRS / 'inherited-full-survey-reproduce.py'
LEGACY_SHA = '9891684101636e151bb05b60e41dfa505ba6bdf662fefaf9e43cc85eb92f687c'
INITIAL = REPAIRS / 'inherited-full-survey-review.json'
INITIAL_SHA = 'a62cef848378623bb19825112c65d067eb574561a51bc8690daa11ae5d171053'
HISTORY_SHA = {'cleanup-b-decls.tsv': '371988e791191772c9c74b6d86879b2b688cba731dbd0f3dc4c5decc3411f6fb',
               'cleanup-b.tsv': '32d88f9f3ff992ba4b46033d8800e199b48fd5f7416a59e1d6aa1dee088cac92'}
RUNNER_SHA = 'ea720bbe6fef9467efef1f8dbeb8c01ca3bb3b66e597a3ed2b3ce512f774f509'
ERROR = re.compile(r'(?m)^([^\n]*?\.lean):(\d+):(\d+): error(?:\(([^\n)]*)\))?:([^\n]*)')

def need(ok, message):
    if not ok: raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw.encode() if isinstance(raw, str) else raw).hexdigest()

def unique(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key: ' + k); out[k] = v
    return out

def read(path):
    obj = json.loads(path.read_bytes(), object_pairs_hook=unique)
    need(isinstance(obj, dict), 'not a JSON object: ' + str(path)); return obj

def git(*args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(ROOT), *args], stderr=subprocess.PIPE)

def load_parser():
    need(LEGACY.is_file() and not LEGACY.is_symlink() and sha(LEGACY.read_bytes()) == LEGACY_SHA, 'legacy parser changed')
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('g06_legacy_parse_only', LEGACY)
    need(spec is not None and spec.loader is not None, 'cannot load reviewed parser')
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod  # Only parse/mask_comments/no_comments are called; never its main/git/frozen refs.

def inputs():
    summary_path = E / 'native-seal-runs/summary.json'
    s, cfg, pins, m, modules, closures = (read(E / n) for n in
        ('native-seal-runs/summary.json', 'native-seal-runs/configuration.json', 'pins.json',
         'seal-manifest.json', 'modules.json', 'closures.json'))
    need(s['kind'] == 'seals' and s['complete'] is True and s['aborted_reason'] is None, 'survey is incomplete/aborted')
    n = len(modules)
    need(n > 0 and s['completed_probes'] == s['expected_probes'] == n and len(s['results']) == n, 'not all final N results')
    need(sha((E / 'native-seal-runs/configuration.json').read_bytes()) == s['configuration_sha256'], 'configuration changed')
    need(sha((E / 'native-seal-runs/driver.source.txt').read_bytes()) == cfg['driver_sha256'] == RUNNER_SHA,
         'not the reviewed fresh runner')
    need(cfg['head'] == s['head'] == pins['head'] and cfg['base'] == s['base'] == pins['base'], 'base/head differ')
    need(cfg['expected_math_modules'] == pins['audited_math_modules'] == n and cfg['modules'] == sorted(modules), 'scope differs')
    for name in ('pins.json', 'modules.json', 'closures.json', 'source-fingerprints.json', 'touched.json', 'seal-manifest.json'):
        need(sha((E / name).read_bytes()) == cfg['inputs'][str(E / name)], 'fresh input changed: ' + name)
    adapter = read(E / 'final-adapter.json')
    need(sha((E / 'final-adapter.json').read_bytes()) == cfg['adapter_sha256'] and
         adapter['seal_manifest_sha256'] == sha((E / 'seal-manifest.json').read_bytes()), 'final adapter binding differs')
    probes = {p['module']: p for p in m['probes']}
    need(len(probes) == len(m['probes']) == n and set(probes) == set(modules) and
         [r['module'] for r in s['results']] == [p['module'] for p in m['probes']], 'duplicate/missing/reordered final module')
    need(sha(INITIAL.read_bytes()) == INITIAL_SHA, 'historical initial review changed')
    return summary_path, s, cfg, pins, probes, modules, closures

def historical_rows():
    rows = []
    for filename, digest in HISTORY_SHA.items():
        raw = (HIST / filename).read_bytes(); need(sha(raw) == digest, 'historical inventory changed: ' + filename)
        for line, text in enumerate(raw.decode().splitlines(), 1):
            f = re.split(r'\t|\\t', text)
            if filename == 'cleanup-b-decls.tsv' and len(f) >= 2:
                path, name = f[:2]
            elif filename == 'cleanup-b.tsv' and len(f) >= 4:
                path, name = f[2], re.sub(r'^(?:theorem|lemma|def|instance|structure|inductive|abbrev|class)\s+', '', f[3])
            else: continue
            if path.startswith('TCSlib/') and path.endswith('.lean'):
                rows.append({'inventory': filename, 'line': line, 'file': path, 'name': name})
    return rows

def direct_imports(parser, source):
    lines = parser.mask_comments(source).splitlines()
    unsupported = [i + 1 for i, line in enumerate(lines) if re.match(r'^\s*import\b', line) and
                   not re.fullmatch(r'import\s+[A-Za-z0-9_\'.]+(?:[ \t]+[A-Za-z0-9_\'.]+)*\s*', line)]
    return [line.strip() for line in lines if line.startswith('import ')], unsupported

def prefix_attributes(parser, source, decl):
    # This is supplementary: complete preceding-code hashes below also expose multiline attributes.
    lines = parser.mask_comments(source).splitlines(); out = []
    for line in reversed(lines[:decl['start'] - 1]):
        if not line.strip(): continue
        if line.lstrip().startswith('@['): out.append(line.strip())
        else: break
    return list(reversed(out))

def preceding_definitions(hd, bd, h, b):
    # A conservative superset of potentially operative same-file definitions; not name resolution.
    def prior(ds, limit):
        out = collections.defaultdict(list)
        for d in ds:
            if d['start'] < limit and d['kind'] not in {'theorem', 'lemma', 'example'}:
                out[d['kind'], d['canonical']].append(d)
        return out
    hp, bp = prior(hd, h['start']), prior(bd, b['start']) if b else {}
    changed = []
    for key in sorted(set(hp) | set(bp)):
        hh, bb = hp.get(key, []), bp.get(key, [])
        if len(hh) == len(bb) == 1 and hh[0]['raw'] == bb[0]['raw']: continue
        changed.append({'kind': key[0], 'canonical': key[1],
            'head_candidates': [{'range': [d['start'], d['end']], 'raw_sha256': sha(d['raw'])} for d in hh],
            'base_candidates': [{'range': [d['start'], d['end']], 'raw_sha256': sha(d['raw'])} for d in bb],
            'review_required': True})
    return changed

def diagnostics(record):
    log, result = Path(record['log']), Path(record['result_path'])
    need(log.resolve().is_relative_to((E / 'native-seal-runs').resolve()) and
         result.resolve().is_relative_to((E / 'native-seal-runs').resolve()), 'nonfinal diagnostic path')
    raw, result_raw = log.read_bytes(), result.read_bytes()
    need(sha(raw) == record['log_sha256'] and sha(result_raw) == record['result_json_sha256'], 'native result/log changed')
    text = raw.decode(); errors = list(ERROR.finditer(text))
    need(read(result) == record['result'], 'embedded native result differs')
    need(len(errors) == len(record['errors']) == record['result']['error_diagnostics'], 'native error count differs')
    for match, error in zip(errors, record['errors']):
        need(match[1].strip() == error['path'], 'native diagnostic path differs')
        need((int(match[2]), int(match[3]), match[4] or None, text.count('\n', 0, match.start()) + 1) ==
             (error['probe_line'], error['probe_column'], error['error_code'], error['log_line']), 'native diagnostic identity differs')
    return record['errors']

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', required=True); ap.add_argument('--head', required=True)
    ap.add_argument('--output-directory', type=Path, required=True); args = ap.parse_args()
    out = args.output_directory.resolve()
    need(out.is_relative_to(REPAIRS.resolve()) and not out.exists(), 'output must be a NEW ignored repairs subdirectory')
    for ref in (args.base, args.head):
        need(re.fullmatch('[0-9a-f]{40}', ref) and git('rev-parse', ref + '^{commit}').decode().strip() == ref, 'not an exact commit')
    summary_path, survey, cfg, pins, probes, modules, closures = inputs()
    need((pins['base'], pins['head']) == (args.base, args.head), 'CLI refs differ from final evidence')
    parser, history, initial = load_parser(), historical_rows(), read(INITIAL)
    files = {ref: set(git('ls-tree', '-r', '--name-only', ref, '--', 'TCSlib', 'TCSlib.lean').decode().splitlines())
             for ref in (args.base, args.head)}
    cache, parsed = {}, {}
    def source(ref, path):
        if (ref, path) not in cache:
            cache[ref, path] = git('show', ref + ':' + path).decode() if path in files[ref] else None
        return cache[ref, path]
    def declarations(ref, path):
        if (ref, path) not in parsed:
            s = source(ref, path); parsed[ref, path] = parser.parse(s) if s is not None else []
        return parsed[ref, path]
    def context_files(module):
        rows = []
        for dep in closures[module]:
            path = dep.replace('.', '/') + '.lean'; b, h = source(args.base, path), source(args.head, path)
            need(h is not None, 'final import closure lacks source: ' + path)
            if b != h:
                rows.append({'file': path, 'base_sha256': sha(b) if b is not None else None, 'head_sha256': sha(h)})
        return rows
    all_rows, unmapped, harness, module_context = [], [], [], {}
    total_errors = 0
    for record in survey['results']:
        module, p = record['module'], probes[record['module']]
        need(record['label'] == p['label'] and record['head_before_and_after'] == args.head, 'native record identity differs')
        if not record['valid_harness']:
            errors, issue = record.get('errors', []), None
            try: errors = diagnostics(record)
            except Exception as ex: issue = type(ex).__name__ + ': ' + str(ex)
            total_errors += len(errors)
            harness.append({'module': module, 'errors': errors, 'classification': record['classification'],
                            'evidence_validation_issue': issue, 'diagnostic_count_verified': issue is None, 'record': record}); continue
        errors = diagnostics(record); total_errors += len(errors)
        need(bool(errors) == record['source_failure'], 'source_failure flag differs')
        need(record['result']['source_sha256'] == record['captured_probe_sha256'] == p['probe_sha256'] and
             record['result']['module'] == p['probe_module'] and record['result']['label'] == p['label'], 'native probe identity differs')
        path = modules[module]; hs = source(args.head, path); bs = source(args.base, path)
        need(p['source'] == path and hs is not None and sha(hs) == p['source_sha256'], 'sealed source is not exact final Git source')
        need(sha(Path(p['probe_path']).read_bytes()) == p['probe_sha256'] and
             Path(p['saved_source']).read_bytes() == Path(p['probe_path']).read_bytes(), 'prepared probe changed')
        inverse = {r['probe_line']: r['source_line'] for r in p['source_to_probe_lines']}
        hd, bd = declarations(args.head, path), declarations(args.base, path)
        grouped = collections.defaultdict(list)
        for error in errors:
            need((ROOT / error['path']).resolve() == Path(p['probe_path']).resolve(), 'error names a dependency/other probe')
            need(inverse.get(error['probe_line']) == error['source_line'], 'source/probe line mapping differs')
            candidates = [d for d in hd if d['start'] <= error['source_line'] <= d['end']]
            if len(candidates) != 1 or candidates[0]['name'] != error['source_name'] or candidates[0]['kind'] != error['kind'] or candidates[0]['start'] != error['declaration_start']:
                unmapped.append({'module': module, 'file': path, 'diagnostic': error, 'candidate_ranges':
                                 [[d['name'], d['start'], d['end']] for d in candidates], 'failure_retained': True}); continue
            grouped[candidates[0]['start']].append(error)
        if not grouped: continue
        imports_h, unsupported_h = direct_imports(parser, hs)
        imports_b, unsupported_b = direct_imports(parser, bs) if bs is not None else ([], [])
        module_context[module] = {'file': path, 'base_file_sha256': sha(bs) if bs is not None else None,
            'head_file_sha256': sha(hs), 'base_imports': imports_b, 'head_imports': imports_h,
            'unsupported_import_lines': {'base': unsupported_b, 'head': unsupported_h},
            'changed_head_import_closure_sources': context_files(module),
            'operative_definition_context_review': 'REQUIRED; no dependency equivalence is inferred from theorem byte identity'}
        for start, es in grouped.items():
            h = next(d for d in hd if d['start'] == start)
            matches = [d for d in bd if (d['kind'], d['canonical']) == (h['kind'], h['canonical'])]
            b = matches[0] if len(matches) == 1 else None
            status = ('NEW_FILE' if bs is None else 'AMBIGUOUS_BASE_DECLARATION' if b is None else
                      'RAW_HEADER_BODY_EQUAL_CONTEXT_REVIEW_REQUIRED' if b['raw'] == h['raw'] else
                      'CODE_EQUAL_RAW_DIFFERENT_REVIEW_REQUIRED' if b['code'] == h['code'] else
                      'WHITESPACE_OR_COMMENT_BOUNDARY_REVIEW_REQUIRED' if b['tokens'] == h['tokens'] else
                      'CHANGED_HEADER_OR_BODY')
            variants = {h['name'].removeprefix('_root_.'), h['canonical']}
            short_unique = sum(d['name'] == h['name'] for d in hd) == 1 and sum(d['name'] == h['name'] for d in bd) <= 1
            exact = [r for r in history if r['file'] == path and r['name'] in variants and
                     (r['name'] == h['canonical'] or short_unique)]
            possible = [r for r in history if r['file'] == path and r not in exact and (r['name'] in variants or any(
                        r['name'].endswith('.' + n) or n.endswith('.' + r['name']) for n in variants))]
            prefix_h = ''.join(hs.splitlines(keepends=True)[:h['start'] - 1])
            prefix_b = ''.join(bs.splitlines(keepends=True)[:b['start'] - 1]) if b else None
            linked = [{'section': section, 'index': index, 'old_classification': r.get('classification'),
                       'link_strength': 'file+canonical' if r.get('canonical') == h['canonical'] else 'file+source-spelling-only'}
                      for section in ('declarations', 'linked_prior_declarations') for index, r in enumerate(initial[section])
                      if r['file'] == path and (r.get('canonical') == h['canonical'] or r['name'] == h['name'])]
            row = {'module': module, 'file': path, 'kind': h['kind'], 'name': h['name'], 'canonical': h['canonical'],
                'classification': status, 'diagnostics': len(es), 'errors': es, 'log': record['log'], 'log_sha256': record['log_sha256'],
                'head_range': [h['start'], h['end']], 'base_range': [b['start'], b['end']] if b else None,
                'head_raw_sha256': sha(h['raw']), 'base_raw_sha256': sha(b['raw']) if b else None,
                'head_code_sha256': sha(h['code']), 'base_code_sha256': sha(b['code']) if b else None,
                'scope_stack_equal': b is not None and b['scope_stack'] == h['scope_stack'],
                'head_scope_stack': h['scope_stack'], 'base_scope_stack': b['scope_stack'] if b else None,
                'binding_context_equal': b is not None and b['context_commands'] == h['context_commands'],
                'head_binding_context': h['context_commands'], 'base_binding_context': b['context_commands'] if b else None,
                'attribute_prefix_equal': b is not None and prefix_attributes(parser, hs, h) == prefix_attributes(parser, bs, b),
                'head_attribute_prefix': prefix_attributes(parser, hs, h),
                'base_attribute_prefix': prefix_attributes(parser, bs, b) if b else None,
                'preceding_definition_changes': preceding_definitions(hd, bd, h, b),
                'head_prefix_code_sha256': sha(parser.no_comments(prefix_h)),
                'base_prefix_code_sha256': sha(parser.no_comments(prefix_b)) if prefix_b is not None else None,
                'preceding_documentation_and_context_sha256': {'head': sha(prefix_h), 'base': sha(prefix_b) if prefix_b is not None else None},
                'historical_exact_rows': exact, 'historical_ambiguous_or_suffix_candidates': possible,
                'inventory_key_status': 'EXACT_KEY_LINK_RECHECK_CONTEXT' if exact else 'NO_EXACT_KEY_LINK_ROOT_MUST_DEDUP',
                'initial_survey_cross_links': linked, 'initial_identity_assumed': False,
                'failure_retained': True, 'waiver': False, 'source_base_native_replay': False,
                'boundary_limit': 'Source-parser candidate boundaries; root must confirm complete header/body and operative definition/doc context.'}
            all_rows.append(row)
    counts = {'modules': len(modules), 'recorded_error_diagnostics': total_errors,
        'candidate_failing_declarations': len(all_rows), 'mapped_source_diagnostics': sum(r['diagnostics'] for r in all_rows),
        'unmapped_source_diagnostics': len(unmapped), 'invalid_harness_records': len(harness),
        'invalid_harness_diagnostics': sum(len(r['errors']) for r in harness),
        'invalid_harness_records_with_unverified_counts': sum(not r['diagnostic_count_verified'] for r in harness),
        'classification_declarations': dict(collections.Counter(r['classification'] for r in all_rows)),
        'classification_diagnostics': dict(collections.Counter({k: sum(r['diagnostics'] for r in all_rows if r['classification'] == k)
                                        for k in {r['classification'] for r in all_rows}})),
        'exact_inventory_linked_candidate_keys': sum(bool(r['historical_exact_rows']) for r in all_rows),
        'candidate_keys_without_exact_inventory_link': sum(not r['historical_exact_rows'] for r in all_rows)}
    need(total_errors == counts['mapped_source_diagnostics'] + counts['unmapped_source_diagnostics'] + counts['invalid_harness_diagnostics'],
         'diagnostics were dropped or counted twice')
    need(counts['mapped_source_diagnostics'] + counts['unmapped_source_diagnostics'] == survey['source_error_diagnostics'] and
         len(harness) == survey['harness_failures'], 'fresh runner diagnostic/harness totals differ')
    report = {'schema': 'gate06-final-failure-witness-proposal/v1', 'status': 'ALL_FAILURES_RETAINED_ROOT_REVIEW_REQUIRED',
        'base': args.base, 'head': args.head, 'summary': str(summary_path), 'summary_sha256': sha(summary_path.read_bytes()),
        'helper_sha256': sha(Path(__file__).read_bytes()), 'parser_sha256': LEGACY_SHA, 'initial_review_sha256': INITIAL_SHA,
        'historical_inventory_sha256': HISTORY_SHA, 'counts': counts, 'declarations': all_rows, 'unmapped': unmapped,
        'invalid_harnesses': harness, 'module_contexts': module_context,
        'limits': ['Candidate source identity is not inheritance acceptance, a waiver, a base seal pass, or merge clearance.',
                   'The source parser is not Lean; ambiguous boundaries and context require root inspection.',
                   'Imported/operative definition and contract-documentation changes need manual source-fidelity review.',
                   'Initial 95/120 witnesses are links only; actual final base/head are re-read.',
                   'No cleanup ledger is changed; new observation keys require review against the frozen 764 inventory.']}
    out.mkdir(parents=True, exist_ok=False)
    (out / 'failure-witnesses.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    buf = io.StringIO(); writer = csv.writer(buf, delimiter='\t'); writer.writerow(['file', 'canonical', 'classification', 'diagnostics', 'base_range', 'head_range', 'inventory_key_status', 'failure_retained'])
    for r in all_rows: writer.writerow([r[k] for k in ('file', 'canonical', 'classification', 'diagnostics', 'base_range', 'head_range', 'inventory_key_status', 'failure_retained')])
    (out / 'failure-witnesses.tsv').write_text(buf.getvalue())
    (out / 'REVIEW-REQUIRED.md').write_text('Every recorded failure remains a failure.\n\n' + json.dumps(counts, indent=2) + '\n\nConfirm candidate declaration boundaries, namespace/bindings, operative definitions, documentation and exact inventory keys before recording any inherited observation. No waivers or pass decisions are produced.\n')
    print(json.dumps({'status': report['status'], 'output': str(out), 'counts': counts}), flush=True)

if __name__ == '__main__':
    main()
