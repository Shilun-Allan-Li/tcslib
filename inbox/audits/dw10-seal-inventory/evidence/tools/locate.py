# locate.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW, the item-location half of the owner check (brief, Checks
# step 2: "each input item's declaration located (the base_path of the input tables confirmed or corrected)"; Reconciliation:
# HANDED-OFF items, "if the collector shows the declaration elsewhere than base_path, say so"). Phase `probe` writes a Lean
# probe importing every owner (hence the handed-off files) that prints, for every distinct item declaration name of the four
# input tables, LOCATE {query, name, home}: the constant itself, or every constant whose private-stripped name equals it, or
# (when none) every TCSlib constant whose name ends with `.<query>`. Phase `parse` writes locate.tsv: one row per input item
# (table, id, query, base_path, located homes, verdict confirmed / corrected / ambiguous / not-found).
# Attempt 2 (2026-11-17): attempt 1 queried private item names verbatim and missed them (32 not-found); now the
# private prefix is stripped from queries (UQ). Attempt 1's log is kept as locate/attempt1/.
# Usage: python3 -I locate.py probe <pack> <batches.tsv> <out.lean> | parse <pack> <log> <out.tsv>
import sys, json, csv, re
UQ = lambda q: re.sub(r'^_private\.[^ ]*?\.0\.', '', q) if q.startswith('_private.') else q  # attempt 2: private item names are queried by their user name
def tsv(p): return list(csv.DictReader((l for l in open(p, encoding='utf-8') if not l.startswith('#')), delimiter='\t'))
def items(pack):
    out = []
    for r in tsv(pack + '/ledger-historical.tsv'): out.append(('historical', 'H:' + r['row'], r['canonical'], r['base_path'], r['scope']))
    for r in tsv(pack + '/ledger-current.tsv'): out.append(('current', r['id'], r['declaration'], r['base_path'], r['scope']))
    for r in tsv(pack + '/provider-pairs.tsv'): out.append(('pairs', r['set'] + ':' + r['id'], r['declaration'], r['base_path'], r['scope']))
    for i, r in enumerate(tsv(pack + '/named-findings.tsv')): out.append(('named', f"{r['finding']}#{i}", r['declaration'], r['base_path'], r['scope']))
    return out
if sys.argv[1] == 'probe':
    pack, bt, outp = sys.argv[2:5]
    mods = [l.split('\t')[1] for l in open(bt).read().split('\n')[1:] if l]
    qs = sorted({UQ(x[2]) for x in items(pack) if x[2]})
    src = ['import Lean'] + [f'import {m}' for m in mods] + ['', 'set_option maxHeartbeats 0', 'open Lean Elab Command', '',
           'def qPayload : String := ' + json.dumps('\n'.join(qs), ensure_ascii=False), '', 'run_cmd do', '  let env ← getEnv',
           '  let names := env.header.moduleNames', '  let mut byUser : Std.HashMap String (Array Name) := {}',
           '  let mut byLast : Std.HashMap String (Array Name) := {}',
           '  for (n, _) in env.constants.toList do',
           '    let some mi := env.getModuleIdxFor? n | continue',
           '    unless (`TCSlib).isPrefixOf names[mi.toNat]! do continue',
           '    let u := ((privateToUserName? n).getD n).toString',
           '    byUser := byUser.insert u ((byUser[u]?.getD #[]).push n)',
           '    let parts := u.splitOn "."', '    for k in [1:parts.length] do',
           '      let suf := ".".intercalate (parts.drop k)',
           '      byLast := byLast.insert suf ((byLast[suf]?.getD #[]).push n)',
           '  for q in qPayload.splitOn "\\n" do',
           '    let hits := (byUser[q]?.getD #[])', '    let hits := if hits.isEmpty then (byLast[q]?.getD #[]) else hits',
           '    if hits.isEmpty then IO.println ("LOCATE " ++ (Json.mkObj [("query", toJson q), ("name", Json.null), ("home", Json.null)]).compress)',
           '    for n in hits do',
           '      let home := (env.getModuleIdxFor? n).map fun i => names[i.toNat]!.toString',
           '      IO.println ("LOCATE " ++ (Json.mkObj [("query", toJson q), ("name", toJson n.toString), ("home", toJson home)]).compress)',
           '  IO.println "LOCATE-DONE"', '']
    open(outp, 'w', encoding='utf-8').write('\n'.join(src)); print('queries', len(qs), 'modules', len(mods))
else:
    pack, log, outp = sys.argv[2:5]; L = {}
    for l in open(log, encoding='utf-8'):
        if l.startswith('LOCATE '):
            r = json.loads(l[7:]); L.setdefault(r['query'], [])
            if r['home']: L[r['query']].append(r['home'].replace('.', '/') + '.lean')
    with open(outp, 'w') as f:
        f.write('table\tid\tquery\tbase_path\tscope\tlocated\tverdict\n')
        for t, i, q, bp, sc in items(pack):
            homes = sorted(set(L.get(UQ(q), [])))
            v = 'not-found' if not homes else ('confirmed' if bp in homes or any(h in bp.split(';') for h in homes) else ('ambiguous' if len(homes) > 1 else 'corrected'))
            f.write('\t'.join([t, i, q, bp, sc, ';'.join(homes) or '-', v]) + '\n')
    import collections
    print(collections.Counter(l.split('\t')[6].strip() for l in open(outp).read().split('\n')[1:] if l))
