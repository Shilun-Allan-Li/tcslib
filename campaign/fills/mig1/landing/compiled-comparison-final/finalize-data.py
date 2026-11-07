"""Additional complete classifications, source delta and citation-set comparison; data only."""
from pathlib import Path
from collections import Counter
import hashlib
import json

OUT = Path(__file__).resolve().parent
LAND = OUT.parent


def write(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n')


sources = json.loads((OUT / 'source-names.json').read_text())
maps = {label: json.loads((OUT / ('map-' + label + '.json')).read_text()) for label in ['base', 'head', 'previous-head']}
source_delta = dict(added={n: row for n, row in sources['head'].items() if n not in sources['base']},
                    removed={n: row for n, row in sources['base'].items() if n not in sources['head']})
write('source-declaration-delta.json', source_delta)


def classify(name, row, label):
    if row['private']: return 'private exact kernel name; identity/semantic moves not inferred'
    if name in sources[label] and not sources[label][name]['private']: return 'authored top-level source export'
    if name.startswith(('Turing.FinTM.instDecidableEqFwdMapState', 'Turing.FinTM.instDecidableEqA2_MapState')):
        return 'generated deriving-instance family'
    if name in {'Turing.solveSplit.eq_def', 'Turing.solveSplitWith.eq_def'}:
        return 'generated foreign-home equation theorem'
    if name == 'Fin.castLEEmb.congr_simp': return 'generated foreign-home congruence theorem'
    if row['internal']: return 'generated internal proof/matcher/equation auxiliary'
    return 'generated/synthesized structure field, reader, recursor or auxiliary; not a written top-level source root'


class_summaries = {}
for label in ['base', 'head']:
    census = maps[label]['census']
    rows = {name: dict(row, classification=classify(name, row, label)) for name, row in census.items()}
    assert all(name in census for name, row in sources[label].items() if not row['private'])
    write('classified-census-' + label + '.json', rows)
    class_summaries[label] = dict(Counter(row['classification'] for row in rows.values()))

edge = lambda row: (row['root'], row['descendant'], row['part'], row['name'], row['owner'], row['kind'])
A = {edge(row) for row in maps['previous-head']['cited']}
B = {edge(row) for row in maps['head']['cited']}
citations = dict(previous_count=len(A), final_count=len(B), added=sorted(B - A), removed=sorted(A - B),
                 limitation='Direct TCSlib type/value constant-use sets only. Equality does not prove equal proof bodies; core/Mathlib references are excluded by the native probe.')
write('citations-previous-final-delta.json', citations)

helpers = {}
for name in ['Turing.FinTM.loop_computes_of_startup', 'Turing.FinTM.emCall_bank_embed',
             'Turing.FinTM.emCall_pair_not_mem', 'Turing.FinTM.emCall_triple_not_mem',
             'Turing.FinTM.catalogRewind', 'Turing.FinTM.bufferReplay_run']:
    helpers[name] = {label: [n for n in maps[label]['census'] if n == name or n.endswith('.' + name)]
                     for label in ['base', 'head']}
write('selected-private-helper-presence.json', helpers)

population_path = LAND / 'review-final-source-final/screen-population-proposed.txt'
population = set(population_path.read_text().splitlines())
citations_owners = {row['owner'] for row in maps['head']['cited']}
missing = sorted({owner.replace('.', '/') + '.lean' for owner in citations_owners} - population)
assert not missing
write('cited-owner-population-crosscheck.json', dict(cited_TCSlib_owners=len(citations_owners),
    proposed_population_count=len(population), missing_paths=missing,
    proposed_population_path=str(population_path),
    proposed_population_sha256=hashlib.sha256(population_path.read_bytes()).hexdigest(),
    limit='Read-only coverage of the proposed source QA population; no screen or final bundle population was run/attested here.'))

summary = json.loads((OUT / 'summary.json').read_text())
summary['complete_census_classification'] = class_summaries
summary['source_declaration_delta'] = dict(added=len(source_delta['added']),
    added_private=sum(row['private'] for row in source_delta['added'].values()),
    removed=len(source_delta['removed']), removed_private=sum(row['private'] for row in source_delta['removed'].values()))
summary['previous_to_final']['cited_sets_equal'] = not citations['added'] and not citations['removed']
summary['generated_shared_owner_change_formula_checked'] = True
summary['native_work_here'] = 'Exactly two separately authorized small actual function/equation metadata probes, both managed PASS. No new full census/replay/control/source run.'
write('summary.json', summary)
print(json.dumps(dict(source_delta=summary['source_declaration_delta'],
                      cited_previous_final_equal=summary['previous_to_final']['cited_sets_equal'],
                      complete_classification=class_summaries), indent=2))
