"""finalize.py <repo> <base> <work> <pkg>: writes owners.txt, list-only.txt, closures.txt and
SOURCE-SHA256SUMS into <pkg> from derive.py's output (<work>/out) and the static index (<work>/idx)."""
import sys, os, csv, hashlib, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanindex as L
repo, base, work, pkg = sys.argv[1:5]
out = f'{work}/out'
rd = lambda f: list(csv.DictReader(open(f'{out}/{f}'), delimiter='\t'))
owners, facades, listonly, considered = (rd('owners.body.tsv'), rd('facades.body.tsv'),
                                        rd('list-only.body.tsv'), rd('considered-excluded.body.tsv'))
order = [l.strip() for l in open(f'{out}/order.txt') if l.strip()]
imps = {}
for l in open(f'{work}/idx/imports.tsv'):
    m, _, rest = l.rstrip('\n').partition('\t'); imps[m] = rest.split()


def agent(p):
    a = p.split('/')
    if a[1] != 'Cryptography':
        return 'lead'
    if a[2].replace('.lean', '') in ('SecureComputation', 'ZeroKnowledge'):
        return 'sub-A'
    if a[2].replace('.lean', '') in ('Encryption', 'Authentication', 'Games', 'Hashing', 'Randomness',
                                      'Implications', 'Pseudorandom'):
        return 'sub-B'
    return 'lead'


def closure(m):
    acc, st = set(), [m]
    while st:
        x = st.pop()
        for y in imps.get(x, []):
            if y in imps and y not in acc:
                acc.add(y); st.append(y)
    return acc


cnt = collections.Counter((r['tier'], agent(r['path'])) for r in owners)
per_agent = collections.Counter(agent(r['path']) for r in owners)
lines_agent = collections.Counter()
for r in owners:
    lines_agent[agent(r['path'])] += L.git(repo, 'show', f'{base}:{r["path"]}').count('\n')
for r in listonly:
    lines_agent['handed off'] += L.git(repo, 'show', f'{base}:{r["path"]}').count('\n')
t1 = sum(1 for r in owners if r['tier'] == 'T1'); t2 = len(owners) - t1
est_o = sum(int(r['est_seal_requests_A']) for r in owners)
est_l = sum(int(r['est_seal_requests_A']) for r in listonly)
cols = ['path', 'tier', 'agent', 'pos_order', 'pos_full_order', 'decls', 'defs', 'est_seal_requests_A',
        'ledger_items_at_base', 'derivation']


def row(r, ag=True, who='lead'):
    return '\t'.join([r['path'], r['tier'], agent(r['path']) if ag else who, r['pos_order'], r['pos_full_order'],
                      r['decls'], r['defs'], r['est_seal_requests_A'], r['ledger_rows_at_base'], r['derivation']])


HDR = f"""# DW-10 owner set: every Pass–shelat-owned Lean file at the issue base
# Base {base} (records tip at staging; its Lean equals a6d01b1bd1a92e2ac0be9999689467fea7e4e77b, the merge of #341).
# COUNTS: {len(owners)} owners to seal ({t1} T1 created by the campaign, {t2} T2 adopted by it); {len(facades)} facades
#   (no declaration: listed, not sealed); {len(considered)} files considered and excluded (end of this file).
#   The {len(listonly)} files outside the campaign that hold recorded items are in list-only.txt: they are HANDED OFF to the
#   Complexity-library maintainers (Seyoon, DW-10 Q1, 2026-11-17) and not sealed or scanned by this job. Of the 1,453
#   TCSlib .lean files at the base, 1,419 are reachable from TCSlib.lean; every owner is reachable.
#   Suggested split (owners): lead {per_agent['lead']} ({lines_agent['lead']} lines); sub-A {per_agent['sub-A']}
#   ({lines_agent['sub-A']} lines); sub-B {per_agent['sub-B']} ({lines_agent['sub-B']} lines). Lean runs one process at a time for all agents, so the split divides probe generation,
#   attribution and reconciliation, not Lean time.
#   Estimated seal requests (variant A, static lower bound: the `def`s in each file's TCSlib import closure):
#   owners {est_o:,} (the handed-off files would add {est_l:,}; not run here). The recorded seals run 1.65-2.0 times the static count (matchers and generated
#   definitions): IterateFind 595 vs 300, ModuleHost 241 vs 146, IterateFindHost 251 vs 150, Yao 3,046 vs 1,847,
#   Uniform 135 vs 79, CodeSimulator 1,232 vs 657. Use the collector's counts, not these.
# DERIVATION (static, from git objects at the base and the campaign records; the tools are in derivation/):
#   1. Origin. derivation/origins.py walks the base's first-parent history (940 commits) with rename detection and
#      records, for every .lean file at the base, the first-parent commit that created it (a merge counts with all it
#      brought in) and every first-parent commit that changed it (derivation/origins.tsv).
#   2. T1, created by the campaign: the creating commit is a merged PR whose branch names pass-shelat (the plans'
#      workstreams, the fills, landings, promotions and moves #185 to #341), except #186 (integrate/main: main's
#      Arora–Barak and library content) and #280 (lwe-sis integration: the lattice campaign); or the direct commit
#      "Pass-shelat ch. 2-4: asymptotic cryptography layer" of 2026-10-28 (the ch. 2–4 statement and fill layer, plan
#      section *Architecture*); or P0's #183 (InformationTheory/Entropy and Extractors, merged to main by D-1 and arrived
#      through #186; ch. 5–8 plan decision log, 2026-11-04).
#   3. T2, adopted by the campaign: created by the Garg concrete layer (garg-ch1-3, which the ch. 2–4 plan builds on)
#      or by the BGW/InformationTheory commit of 2026-09-30, and changed by at least one Pass–shelat PR (#183 to #341;
#      for example #210's equation readers, #248's cleanup, #195, the moves). Main's Shamir files are excluded: P0 only
#      added docstring citations to them through #183 on main (D-1, "cited in place").
#   4. Facades: T1/T2 files with no declaration (import-only); listed, not sealed.
#   5. Cross-checks. The ch. 2–4 plan's *Architecture* table names 49 TCSlib paths: 41 are T1, 7 no longer exist (moved
#      by #256-#269 into T1 files under Encryption/ and Pseudorandom/), 1 is excluded (ComputationalModels.lean, the
#      model registry, below). Cleanup Stage 1's 19 CHANGED homes (its closures.txt) are all T1 or T2 (two are T1
#      facades). The #248 ledger's owners: every ledger row and provider pair maps to an owner or a handed-off file, or
#      to no declaration at the base (ledger-*.tsv, base_match); #248's primary-owner list (101 paths) gives 73 T1,
#      10 T2, 4 handed off, 3 excluded below, 11 no longer existing.
#   6. Excluded: GSW (#333, #338, #339), pairings and IBE (#331), the lattice LWE/SIS layer (#280), Arora–Barak
#      (#3, #186 and their predecessors), Ladner and every other library file. The 21 files outside the campaign that
#      hold recorded items are handed off (list-only.txt): their items enter the inventory as HANDED-OFF, from the
#      records only.
# The static declaration counts and positions are approximate; the elaborated environment (the job's collector) is
# authoritative, and the job records any difference.
"""
with open(f'{pkg}/owners.txt', 'w') as f:
    f.write(HDR)
    f.write('\t'.join(cols) + '\n')
    for r in owners:
        f.write(row(r) + '\n')
    f.write(f'# FACADES ({len(facades)}): no declaration; not sealed, no control, no scan\n')
    for r in facades:
        f.write(row(r) + '\n')
    f.write(f'# CONSIDERED AND EXCLUDED ({len(considered)}): outside the campaign, changed by a Pass–shelat PR or named as a\n'
            '# #248 primary owner, with no reconciled item at the base. Not sealed; a new failure here is not looked for.\n')
    for r in considered:
        f.write(row(r, ag=False, who='-') + '\n')
with open(f'{pkg}/list-only.txt', 'w') as f:
    f.write(f"""# DW-10 handed-off files: outside the Pass–shelat campaign, holding recorded seal items. Base {base}.
# Seyoon, 2026-11-17 (DW-10 Q1): "Arora–Barak material that needs fixing: send me a pasteable prompt I can give to a
#   different chat. You are responsible for any seals from cryptography content." So this job does NOT seal, scan or
#   control these files. Their recorded items (#248 rows, the provider pairs whose failing proof is here, SY-F07 for
#   Uniform, C-F02 for CodeSimulator) enter inventory.tsv with status HANDED-OFF, reconciled from the records only.
#   The handoff to the Complexity-library chat is the records folder ../handoff-complexity/ (not part of this pack).
# COUNT: {len(listonly)} files ({lines_agent['handed off']} lines). They stay in order.txt: the owners import them.
""")
    f.write('\t'.join(cols) + '\n')
    for r in listonly:
        f.write(row(r, ag=False, who='-') + '\n')
pos = {m: i + 1 for i, m in enumerate(order)}
with open(f'{pkg}/closures.txt', 'w') as f:
    f.write(f'# Closures at the base {base}: tag<TAB>position in order.txt<TAB>position in the full {1419}-module import order'
            '<TAB>module<TAB>TCSlib modules in its import closure<TAB>estimated seal requests (A, static).\n'
            f'# OWNER: the {len(owners)} owners (owners.txt), sealed. HANDED: the {len(listonly)} handed-off files (list-only.txt), not\n'
            f'# sealed; they are listed because the owners import them. order.txt ({len(order)} modules) is the upstream\n'
            '# closure of the owners, in the depth-first post-order of the modules reachable from TCSlib.lean\n'
            '# (imports in file order); the root TCSlib is not in it. Facades are not targets and are in order.txt only if\n'
            '# a target imports them.\n')
    for tag, rs in (('OWNER', owners), ('HANDED', listonly)):
        for r in rs:
            m = r['path'][:-5]
            f.write(f"{tag}\t{pos[m]}\t{r['pos_full_order']}\t{m}\t{len(closure(m.replace('/', '.')))}\t"
                    f"{r['est_seal_requests_A']}\n")
src = L.blobs(repo, base, [m + '.lean' for m in order])
with open(f'{pkg}/SOURCE-SHA256SUMS', 'w') as f:
    for m in order:
        f.write(hashlib.sha256(src[m + '.lean'].encode('utf-8')).hexdigest() + '  ' + m + '.lean\n')
print('owners', len(owners), 'T1', t1, 'T2', t2, 'facades', len(facades), 'list', len(listonly), 'considered',
      len(considered), 'order', len(order), dict(per_agent), dict(lines_agent), est_o, est_l)

# scope of every input item (Seyoon, DW-10 Q1): OWNER, HANDED-OFF (in a list-only file) or NO-DECLARATION
handed_paths = {r['path'] for r in listonly}
owner_paths = {r['path'] for r in owners}
import shutil
for fn in ('ledger-historical.tsv', 'ledger-current.tsv', 'provider-pairs.tsv', 'named-findings.tsv'):
    src_rows = open(f'{out}/{fn}').read().rstrip('\n').split('\n')
    hdr = src_rows[0].split('\t'); bi = hdr.index('base_path')
    cnt = collections.Counter()
    with open(f'{pkg}/{fn}', 'w') as f:
        f.write(src_rows[0] + '\tscope\n')
        for l in src_rows[1:]:
            ps = [p for p in l.split('\t')[bi].split(';') if p]
            sc = ('NO-DECLARATION' if not ps else 'HANDED-OFF' if ps[0] in handed_paths
                  else 'OWNER' if ps[0] in owner_paths else 'OTHER:' + ps[0])
            cnt[sc] += 1
            f.write(l + '\t' + sc + '\n')
    print(fn, dict(cnt))
