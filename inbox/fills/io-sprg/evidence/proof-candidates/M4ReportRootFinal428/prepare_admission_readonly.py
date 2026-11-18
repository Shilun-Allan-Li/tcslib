#!/usr/bin/env python3
"""Executed staging producer: read existing M4 searches; write TEMP admission only.

Does not invoke searches, Lean, Git, cache, gates, or any subprocess. It never
writes implementation/evidence files. Recorded partial/timeouts are not proofs.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
AREA = 'TCSlib.Cryptography.Obfuscation.StructuredSeed.'
HOME = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ref(path):
    path = Path(path).resolve()
    need(path.is_file(), 'Missing provenance: ' + str(path))
    return {'path': str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            'sha256': sha(path)}


def static_logs(kind, leaf):
    if kind == 'lpn':
        folder = ROOT / 'evidence/overlap/M4-LPN-name-shape'
        return [ref(folder / x) for x in ['index.json', 'name-' + leaf + '.log',
                                          'shape-canonical.log', 'shape-verdict.log', 'shape-average.log']]
    if kind == 'encoding':
        folder = ROOT / 'evidence/proof-candidates/M4AdviceEncoding'
        return [ref(folder / 'static-search-index.json'),
                *[ref(folder / 'searches' / (x + '.log')) for x in
                  ['public-encoding-names', 'encoding-shapes', 'list-public-alternatives',
                   'lwe-family-width', 'encoding-local-width-overlap']]]
    if kind == 'security':
        folder = ROOT / 'evidence/overlap/M4-security-name-shape'
        return [ref(folder / x) for x in ['queries.json', '01.log', '02.log', '03.log']]
    folder = ROOT / 'evidence/overlap/M4-PRG-name-shape'
    return [ref(folder / x) for x in ['index.json', 'name-' + leaf + '.log',
                                      'shape-coupling.log', 'shape-coins.log', 'shape-product.log']]


def pair(goal, actual=False, supplemental=False):
    folder = ROOT / 'evidence/overlap/probes' / goal
    path = folder / 'search.json'
    if not path.exists():
        return None
    record = json.loads(path.read_text())
    need(record['goal'] == goal, 'Search goal mismatch')
    modes = {r['mode']: r for r in record['searches']}
    need(set(modes) == {'exact', 'apply'} and len(record['searches']) == 2, 'Incomplete paired record')
    output = {'goal': goal, 'record': ref(path), 'qualification': record['qualification'],
              'original_reused_api': record.get('reused_api'), 'searches': {},
              'correction': ref(folder / 'reuse-correction.json')
              if (folder / 'reuse-correction.json').exists() else None}
    for mode in ['exact', 'apply']:
        row = modes[mode]
        source, log = folder / (mode + '.lean.txt'), folder / (mode + '.log')
        need(sha(source) == row['run']['source_sha256'] and sha(log) == row['run']['log_sha256'],
             goal + '/' + mode + ' archived source/log SHA differs from actual run record')
        text, stdout = source.read_text(), log.read_text()
        imports = re.findall(r'^import\s+(\S+)\s*$', text, re.M)
        result = {'mode': mode, 'status': row['status'], 'run': row['run'],
                  'source': ref(source), 'log': ref(log), 'direct_imports': imports,
                  'elaboration_errors': row.get('elaboration_errors', row.get('diagnostic_error_headers', [])),
                  'observed_log_flags': {'bounded_heartbeat_timeout': 'maximum number of heartbeats' in stdout,
                     'apply_stopped_for_time': 'stopped because it was running out of time' in stdout,
                     'partial_suggestions': 'Remaining subgoals' in stdout or 'partial proof' in stdout,
                     'exact_no_close': '`exact?` could not close the goal' in stdout}}
        if actual:
            need(imports == ['TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN.Defs',
                             'Lean.Elab.Tactic.LibrarySearch'], 'Actual LPN import scope changed')
            need(row['runtime_target_absence_observed'] is True
                 and row['diagnostic_flags']['runtime_target_absence_marker'] is True
                 and not row['diagnostic_flags']['target_present']
                 and not row['diagnostic_flags']['statement_error']
                 and 'LPN_DEFS_GUARD_OK_10' in stdout, 'LPN runtime absence guard not observed')
            request_path = folder / (mode + '-request.json')
            request = json.loads(request_path.read_text())
            need(sha(request_path) == row['request_sha256'], 'Archived LPN request hash differs')
            original_request = Path(row['request'])
            need(original_request.read_bytes() == request_path.read_bytes(), 'Request copies differ')
            audit_path = original_request.with_name('source-import-audit.json')
            audit = json.loads(audit_path.read_text())
            need(sha(audit_path) == row['source_import_audit_sha256'] == request['source_audit_sha256']
                 and not audit['target_declarations_found'] and not audit['target_leaf_code_occurrences'],
                 'Source import/target-absence binding differs')
            need(record['paired_Defs_olean_hashes_equal'] and record['paired_import_source_bindings_equal'],
                 'Paired LPN import source/object bindings differ')
            result.update(runtime_target_absence_observed=True, runtime_marker='LPN_DEFS_GUARD_OK_10',
                          request=ref(request_path), request_origin=ref(original_request),
                          import_audit=ref(audit_path),
                          completion=ref(original_request.with_name('completion.json')),
                          runtime_guard=ref(original_request.with_name('runtime-import-guard.lean.txt')),
                          recorded_Defs_olean_sha256=request['Defs_olean_sha256'],
                          recorded_import_source_count=len(audit['source_sha256']),
                          recorded_Defs_source_sha256=audit['source_sha256'][str(ROOT /
                              'TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Defs.lean')],
                          import_binding_qualification='Recorded at search time. Audit hash/request and '
                          'actual ten-name runtime marker verified; not a fresh full physical closure '
                          'or object/source coherence/owner/axiom audit.')
        else:
            need(not any(x.startswith('TCSlib.Cryptography.Obfuscation') for x in imports),
                 'Public core unexpectedly imports owned source')
            need(not row.get('elaboration_errors'), 'Public core has invalid syntax/elaboration')
        if not supplemental:
            need(row['status'] not in {'INVALID_ELABORATION', 'IMPORT_GUARD_NOT_OBSERVED'},
                 'Superseded invalid pair cannot satisfy primary admission')
        output['searches'][mode] = result
    return output


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True)
    ap.add_argument('--head', default='c44841d3ba8af56a407d3d30b7c4720617c0d845')
    ap.add_argument('--root-reported-committed', action='store_true')
    args = ap.parse_args()
    out = Path(args.out).resolve()
    need(out.is_relative_to(Path('/private/tmp')) and not out.exists(), 'Use fresh TEMP output')
    plan = json.loads((HOME / 'declaration-plan.json').read_text())
    mapping = {
        'Params.hyb_real_eq_raw': ('M4PRG_hyb_real_eq_raw_core', 'prg'),
        'Params.hyb_random_eq_raw': ('M4PRG_hyb_random_eq_raw_core', 'prg'),
        'Params.hyb_prg_accept_eq_chain_zero': ('M4PRG_hyb_prg_accept_eq_chain_zero_core', 'prg'),
        'Params.hyb_uniform_accept_eq_chain_zero': ('M4PRG_hyb_uniform_accept_eq_chain_zero_core', 'prg'),
        'Params.hyb_real_prg_le': ('M4PRG_hyb_real_prg_le_core', 'prg'),
        'Params.hyb_uniform_random_le': ('M4PRG_hyb_uniform_random_le_core', 'prg'),
        'Params.lpnEnc_injective': ('M4Advice_01_lpnEnc_core', 'encoding'),
        'Params.encLPNAdvice_injective': ('M4Advice_02_encLPNAdvice_core', 'encoding'),
        'Params.encLPNAdvice_length_le': ('M4Advice_03_encLPNAdvice_length_core', 'encoding'),
        'Params.prgEnc_injective': ('M4Advice_04_prgEnc_core', 'encoding'),
        'Params.encPRGAdvice_injective': ('M4Advice_05_encPRGAdvice_core', 'encoding'),
        'Params.encPRGAdvice_length_le': ('M4Advice_06_encPRGAdvice_length_core', 'encoding'),
        'Params.prg_hop': ('M4PRG_prg_hop_fix_advice_core', 'prg'),
        'Params.lpn_hop': ('M4LPNDefs_V1_10-lpn_hop', 'lpn'),
        'lemma42': ('M4Security_lemma42_core', 'security'),
        'prop41': ('M4Security_prop41_core', 'security'),
        'Params.sdCore_publicSeed': ('M4PRG_sdCore_publicSeed_core_v2', 'prg'),
        'Params.prg_verdict_prob': ('M4PRG_prg_verdict_prob_core', 'prg'),
        'Params.prg_nuisance_average': ('M4PRG_prg_nuisance_average_core', 'prg'),
        'Params.prg_chain_accept_average': ('M4PRG_prg_chain_output_reindex_core', 'prg')}
    for i, leaf in enumerate(['lpn_accept_realizes_eq', 'lpn_gap_realizes_eq',
                              'lpn_uniform_challenge_reindex', 'lpn_real_seed_reindex',
                              'lpn_pre_real_update', 'lpn_pre_uniform_update', 'lpn_real_section',
                              'lpn_uniform_section', 'lpn_fix_advice'], 1):
        mapping['Internal.' + leaf] = ('M4LPNDefs_' + ('V2' if i == 1 else 'V1') +
                                       '_' + f'{i:02d}-' + leaf, 'lpn')
    need(set(mapping) == {r['name'].removeprefix(AREA) for r in plan}, '29-name scope differs')
    rows, counts = [], Counter()
    for decl in plan:
        suffix = decl['name'].removeprefix(AREA)
        goal, family = mapping[suffix]
        actual = family == 'lpn'
        paired = pair(goal, actual)
        row = {'name': decl['name'], 'kind': decl['kind'], 'probe_goal': goal,
               'reviewed': paired is not None,
               'scope': 'ACTUAL_READER_TARGET_ABSENT' if actual else 'PUBLIC_ONLY_CORE',
               'scope_detail': ('EXACT_ACTUAL_STATEMENT_WITH_LPN_DEFS_RUNTIME_TEN_TARGET_ABSENCE' if actual
                                else 'PUBLIC_COMPONENT_OR_ABSTRACT_MATHEMATICAL_CORE_NOT_OWN_FULL_STATEMENT'),
               'target_absent_from_bound_imports': bool(paired) if actual else None,
               'name_shape_artifacts': static_logs(family, suffix.split('.')[-1]),
               'exact_artifacts': [], 'apply_artifacts': [],
               'search_record': paired['record'] if paired else None,
               'admission_status': 'RECORDED_SCOPED_PAIR_NOT_PROOF' if paired else 'PENDING_PAIR_RECORD',
               'scope_and_reuse_note': ('Actual root-reviewed exact-statement exception; the ten named '
                'LPN targets were absent in the actual imported Lean environment before each search. '
                'No Transport/Sections/Hop/facade/Security/Targets import. Timeouts/no-hits are not '
                'absence proofs.' if actual else 'Owned imports excluded. This is the recorded public '
                'component/core goal, not a claim that the entire construction-specific theorem was '
                'searched under all own definitions. Closed public suggestions motivate direct reuse; '
                'partial suggestions/timeouts/no-hits are not proofs.')}
        if family == 'encoding':
            row['name_shape_scope_note'] = ('Static index records canonical/fixed-width API names and '
                'mathematical encoding shapes, with earlier own-reader text hits explicitly retained; '
                'the dynamic public core still excludes every owned import.')
        if paired:
            row['paired_evidence'] = paired
            if paired['correction']:
                correction_path = ROOT / paired['correction']['path']
                row['reuse_correction_contents'] = json.loads(correction_path.read_text())
            for mode in ['exact', 'apply']:
                s = paired['searches'][mode]
                row[mode + '_artifacts'] = [paired['record'], s['source'], s['log']]
                if actual:
                    row[mode + '_artifacts'] += [s[k] for k in
                        ['request', 'request_origin', 'import_audit', 'completion', 'runtime_guard']]
                if paired['correction']:
                    row[mode + '_artifacts'].append(paired['correction'])
                counts[s['status']] += 1
        rows.append(row)
    supplementary = []
    for goal in ['M4LPNPublic_V1_01-split-product', 'M4LPNPublic_V1_02-move-matrix',
                 'M4LPNPublic_V1_03-resample-selected']:
        p = pair(goal, supplemental=True)
        supplementary.append({'new_declaration': False, 'counts_toward_29': False,
                              'scope': 'SUPPLEMENTARY_PUBLIC_COMPOSITION_CORE', 'pair': p,
                              'qualification': 'Three mathematical composition controls supporting '
                              'LPN averaging; no new helper names and not substitutes for the ten '
                              'actual LPN exact-statement pairs. Diagnostic outcomes remain as recorded.'})
    superseded = []
    for goal, reason in [('M4PRG_sdCore_publicSeed_core', 'Reserved public binder; use publicMap v2'),
                         ('M4LPNDefs_V1_01-lpn_accept_realizes_eq',
                          'Reserved prefix binder prevents runtime guard; use V2 areaPrefix')]:
        folder = ROOT / 'evidence/overlap/probes' / goal
        record = json.loads((folder / 'search.json').read_text())
        refs = [ref(folder / 'search.json')]
        for s in record['searches']:
            mode = s['mode']
            for f, key in [(folder / (mode + '.lean.txt'), 'source_sha256'),
                           (folder / (mode + '.log'), 'log_sha256')]:
                need(sha(f) == s['run'][key], 'Superseded record binding differs')
                refs.append(ref(f))
        superseded.append({'goal': goal, 'reason': reason, 'eligible_for_admission': False,
                           'artifacts': refs, 'recorded_statuses': [s['status'] for s in record['searches']]})
    pending = [r['name'] for r in rows if not r['reviewed']]
    result = {'schema': 1, 'head': args.head,
              'head_qualification': ('Root reports this source head committed; this producer '
              'performs no independent Git inventory. Individual search source/run bindings retain '
              'their actual earlier scope; no historical probe source/run hashes are relabeled.'
              if args.root_reported_committed else 'Root-supplied current source-head CONTEXT; proof '
              'edits remain uncommitted at capture. Individual search source/run bindings retain '
              'their actual earlier scope. Root must separately bind a final committed review head, '
              'without relabeling historical probe source/run hashes.'),
              'status': 'COMPLETE_SCOPED_SEARCH_RECORDS_NOT_M4_PROOF_COMPLETION' if not pending
                        else 'PENDING_EXPLICIT_DECLARATION_PAIRS',
              'admission_rows': rows, 'primary_declarations': len(rows),
              'primary_pairs_recorded': len(rows) - len(pending), 'pending_declarations': pending,
              'primary_search_status_counts': dict(sorted(counts.items())),
              'supplementary_public_composition_pairs': supplementary,
              'superseded_invalid_pairs': superseded,
              'limits': 'This producer verified existing archive hashes and scoped runtime markers '
              'only. It executed no search/Lean/Git/cache/gate/source action. Reviewed means the '
              'recorded scoped search was statically cross-checked, never proof completion or '
              'global lemma absence. Owner source/build/axioms/670-header freeze/final canonical '
              'closure gates remain independently required.'}
    out.mkdir(parents=True)
    (out / 'overlap-admission.json').write_text(json.dumps(result, indent=2) + '\n')
    lines = ['name\tkind\tscope\tgoal\texact_status\tapply_status\tcorrection\tadmission']
    for r in rows:
        p = r.get('paired_evidence')
        lines.append('\t'.join([r['name'], r['kind'], r['scope'], r['probe_goal'],
                                p['searches']['exact']['status'] if p else 'PENDING',
                                p['searches']['apply']['status'] if p else 'PENDING',
                                p['correction']['path'] if p and p['correction'] else '',
                                r['admission_status']]))
    (out / '29-name-map.tsv').write_text('\n'.join(lines) + '\n')
    (out / 'summary.json').write_text(json.dumps({k: v for k, v in result.items()
         if k not in {'admission_rows', 'supplementary_public_composition_pairs',
                      'superseded_invalid_pairs'}}, indent=2) + '\n')
    print(result['status'], result['primary_pairs_recorded'], '/29; pending', pending)
    print('primary status counts', result['primary_search_status_counts'])


if __name__ == '__main__':
    main()
