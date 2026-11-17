"""Assign Stage 2 items to proposed jobs, write scope.tsv and the summary tables."""
import json, sys, collections, csv, re

S, OUT = sys.argv[1], sys.argv[2]
items = json.load(open(f'{OUT}/items.json'))

# J0 homes: promotions and every reader whose users sit in another job's files
J0_FILES = {
    'TCSlib/Cryptography/Games/Probability.lean', 'TCSlib/Cryptography/Games/Machines.lean',
    'TCSlib/Cryptography/Games/Tapes.lean', 'TCSlib/Cryptography/Games/Efficiency.lean',
    'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean',
    'TCSlib/Complexity/TuringMachine/Encoding.lean', 'TCSlib/Complexity/Randomized/Repetition.lean',
}
J0_READERS = {  # cross-job readers (home file -> users in another job)
    'Complexity.polyTimeComputable_iterateFind_elim', 'Turing.CodeTM.toFinTM_tm',
    'TCSlib.Cryptography.Ensemble.distAdv_uniform', 'TCSlib.Cryptography.Ensemble.indist_iff',
    'TCSlib.Cryptography.Ensemble.samplable_iff', 'TCSlib.Cryptography.EnsembleLemmas.swapAux_apply',
    'TCSlib.Cryptography.fisherYates_def', 'TCSlib.Cryptography.permFromCoins_def',
    'TCSlib.Cryptography.owpGenNot_apply', 'TCSlib.Cryptography.owpGen_apply', 'TCSlib.Cryptography.owpPair_apply',
}


def job_of(it):
    f = it['owner_file'].split(' ')[0]
    if it['kind'] == 'add reader' and (it['declaration'] in J0_READERS or it['declaration'].startswith('Turing.pairDecode')):
        return 'J0'
    if f in J0_FILES:
        return 'J0'
    if it['id'] in ('S2-DL-01', 'S2-DL-02'):  # DL-55: the verbatim move and T1's re-point in one change
        return 'J0'
    if it['id'].startswith('S2-BK') and it['kind'] == 'delete':
        return 'J8'  # alias removal after every DL-35 site has moved
    p = f.replace('TCSlib/', '')
    if p.startswith('Complexity/') or p.startswith('Cryptography/Randomness/Derandomization'):
        return 'J1'
    if re.match(r'Cryptography/(Asymptotic|Candidates|HardcoreBit|NumberTheory|Foundations|Encoding|Hashing)/', p) or p.startswith('InformationTheory/'):
        return 'J2'
    if re.match(r'Cryptography/(Pseudorandom|Randomness)', p):
        return 'J3'
    if re.match(r'Cryptography/(Encryption|Authentication|AdvancedEncryption|Pairing)', p):
        return 'J4'
    if re.match(r'Cryptography/(SecureComputation|Composability)', p):
        return 'J5'
    if re.match(r'Cryptography/ZeroKnowledge/GraphIsomorphism', p):
        return 'J6'
    if re.match(r'Cryptography/ZeroKnowledge/', p):
        return 'J7'
    return '??'


REMAP = {'J0': 'J0', 'J1': 'J1', 'J2': 'J2', 'J3': 'J3', 'J5': 'J3', 'J4': 'J4', 'J6': 'J5', 'J7': 'J6', 'J8': 'J7'}
for it in items:
    it['job'] = REMAP[job_of(it)]
    if it['id'] == 'S2-DL-28':
        it['kind'] = 'doc nit'
    OV = {
        'S2-RP-004': dict(statement_change='removal of 3 public lemmas (unused since DW-5)', freeze_ref='cleanup-stages Stage 2 + DW10-Q9',
                          notes='host_dispatch, host_branch, host_halt: resolves the 3 STATEMENT rows NEW:9..11'),
        'S2-RP-103': dict(statement_change='move (verbatim, REMOVED/ADDED pair) to Games/Machines.lean', freeze_ref='CS1-Q3',
                          notes='J4 owns Games/Machines.lean for this move (after J0 merges)'),
        'S2-RP-051': dict(notes="delete private getD_ofFn' (:614); re-point public yaoBobTables_yaoMsg (:620) proof-only"),
        'S2-RP-055': dict(notes='delete private map_range_getD_ofFn (:202); re-point garbledValues_getD (:374) proof-only'),
        'S2-RP-040': dict(statement_change='no (private, unused)', freeze_ref='DL-46 frozen-file exception'),
        'S2-DL-01': dict(statement_change='move (verbatim, REMOVED/ADDED pair; same full name)', freeze_ref='DL-55 (G44-01)'),
    }
    if it['id'] in OV:
        it.update(OV[it['id']])

# dependencies at job level
JOBDEP = {'J0': '-', 'J1': 'J0', 'J2': 'J0', 'J3': 'J0 (DL-59 Tapes generalisation)', 'J4': 'J0 (DL-43/DL-55/DL-56/DL-57/DL-59 homes)',
          'J5': 'J0; W6-GI and W6-GIZK first inside the job', 'J6': 'J0; W6-ColProofs and W6-ColSim first inside the job',
          'J7': 'J2, J4, J6 merged (all fourteen DL-35 sites moved)'}
for it in items:
    if it['depends_on'] == '-':
        it['depends_on'] = JOBDEP[it['job']] if it['job'] != 'J0' else '-'
    elif it['job'] != 'J0' and 'J0' not in it['depends_on']:
        it['depends_on'] = it['depends_on'] + '; job ' + JOBDEP[it['job']]

cols = ['id', 'source', 'owner_file', 'tip_line', 'declaration', 'kind', 'statement_change', 'freeze_ref', 'depends_on',
        'est_lines', 'job', 'target', 'notes']
with open(f'{OUT}/scope.tsv', 'w', newline='') as fh:
    w = csv.writer(fh, delimiter='\t', lineterminator='\n')
    w.writerow(cols)
    for it in items:
        w.writerow([str(it[c]).replace('\t', ' ').replace('\n', ' ') for c in cols])

# summaries
J = collections.defaultdict(lambda: dict(items=0, lines=0, files=set(), kinds=collections.Counter(), stmt=0))
for it in items:
    j = J[it['job']]
    j['items'] += 1; j['lines'] += int(it['est_lines']); j['kinds'][it['kind']] += 1
    j['files'].add(it['owner_file'].split(' ')[0])
    if it['statement_change'] not in ('no', 'no (new declaration)', 'no (additive)') and not it['statement_change'].startswith('no '):
        j['stmt'] += 1
for k in sorted(J):
    v = J[k]
    print(k, v['items'], v['lines'], len(v['files']), v['stmt'], dict(v['kinds']))
allf = {it['owner_file'].split(' ')[0] for it in items}
print('files', len(allf), 'items', len(items), 'lines', sum(int(i['est_lines']) for i in items))
# file-disjointness across jobs (J0 and J8 are sequential, excluded)
fj = collections.defaultdict(set)
for it in items:
    fj[it['owner_file'].split(' ')[0]].add(it['job'])
print('shared files:', {f: j for f, j in fj.items() if len(j - {'J0', 'J7'}) > 1})
print('J0/J7 overlap files:', sorted(f for f, j in fj.items() if len(j) > 1))
json.dump({k: dict(items=v['items'], lines=v['lines'], files=sorted(v['files']), stmt=v['stmt'], kinds=dict(v['kinds'])) for k, v in J.items()},
          open(f'{OUT}/jobs.json', 'w'), indent=1)
kinds = collections.Counter(it['kind'] for it in items)
print(kinds)
