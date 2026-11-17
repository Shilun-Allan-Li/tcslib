# readers.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW, the reader search behind the classification (brief:
# "say whether a published reader already exists there"). Phase `probe`: writes a Lean probe that imports the given
# modules and prints, for every TCSlib theorem whose user name is <P>_<suffix> (the last name component split at an
# underscore) for a definition P of the given provider list, and whose type mentions P: READER {provider, reader, home}.
# Phase `parse`: READER records -> readers.json (provider -> [reader, home], ranked: _eq, _def, _apply, _iff, _eq_def,
# then the other <P>_* names by length).
# The provider list is every TCSlib definition of the five collectors' CAT records (not only the providers seen in the
# seals), so the index is complete for any read the classification meets.
# Attempt 2: a reader's name may lower-case the first letter of the definition's last component (PolyTimeComputable ->
# polyTimeComputable_iff, Lean's naming convention for theorems about a Prop-valued definition); both spellings map to the
# definition. Attempt 1 (exact spelling only) is kept as readers/attempt1/.
# Attempt 3: also prints STRUCT {provider, fields} for every provider whose result type (after the binders) is a structure,
# so that the field equations <P>_<field> (policy.md §1: a structure-valued definition is read through its field equations)
# count as published readers. Attempt 2's log is kept as readers/attempt2/.
# Usage: python3 -I readers.py probe <providers.txt> <out.lean> <module>... | parse <log> <out.json>
import sys, json
if sys.argv[1] == 'probe':
    prov = [l.strip() for l in open(sys.argv[2]) if l.strip()]; out = sys.argv[3]; mods = sys.argv[4:]
    src = ['import Lean'] + [f'import {m}' for m in mods] + ['', 'set_option maxHeartbeats 0', 'open Lean Elab Command', '',
           'def provPayload : String := ' + json.dumps('\n'.join(prov), ensure_ascii=False), '',
           'run_cmd do',
           '  let env ← getEnv',
           '  let names := env.header.moduleNames',
           '  let mut ps : Std.HashMap Name Name := {}',
           '  for s in provPayload.splitOn "\\n" do',
           '    let n := s.toName',
           '    ps := ps.insert n n',
           '    if let .str pre l := n then',
           '      let lc := Name.str pre (l.decapitalize)',
           '      unless ps.contains lc do ps := ps.insert lc n',
           '  let mut n := 0',
           '  for (t, ci) in env.constants.toList do',
           '    unless ci matches .thmInfo _ do continue',
           '    let some mi := env.getModuleIdxFor? t | continue',
           '    let home := names[mi.toNat]!',
           '    unless (`TCSlib).isPrefixOf home do continue',
           '    let u := (privateToUserName? t).getD t',
           '    let .str pre last := u | continue',
           '    let parts := last.splitOn "_"',
           '    let used := ci.type.getUsedConstants',
           '    for i in [1:parts.length] do',
           '      let p := Name.str pre ("_".intercalate (parts.take i))',
           '      if let some q := ps[p]? then',
           '       if used.contains q then',
           '        IO.println ("READER " ++ (Json.mkObj [("provider", toJson q.toString), ("reader", toJson t.toString), ("home", toJson home.toString), ("private", toJson (isPrivateName t))]).compress)',
           '        n := n + 1',
           '  for (q, _) in ps.toList do',
           '    let some ci := env.find? q | continue',
           '    let some sn := ci.type.getForallBody.getAppFn.constName? | continue',
           '    if isStructure env sn then',
           '      IO.println ("STRUCT " ++ (Json.mkObj [("provider", toJson q.toString), ("structure", toJson sn.toString), ("fields", toJson ((getStructureFields env sn).map (·.toString)))]).compress)',
           '  IO.println s!"READER-DONE {n}"', '']
    open(out, 'w', encoding='utf-8').write('\n'.join(src))
    print('providers', len(prov), 'modules', len(mods))
else:
    log, outp = sys.argv[2:4]; R = {}
    SUF = ['_eq', '_def', '_apply', '_iff', '_eq_def']
    for l in open(log, encoding='utf-8'):
        if l.startswith('READER '):
            r = json.loads(l[7:])
            if r['private']: continue
            R.setdefault(r['provider'], []).append([r['reader'], r['home']])
    def rank(p, t):
        for k, s in enumerate(SUF):
            if t == p + s: return (0, k, t)
        return (1, len(t), t)
    for p in R: R[p] = sorted({tuple(x) for x in R[p]}, key=lambda x: rank(p, x[0]))
    S = {}
    for l in open(log, encoding='utf-8'):
        if l.startswith('STRUCT '):
            r = json.loads(l[7:]); S[r['provider']] = r['fields']
    json.dump(R, open(outp, 'w'), indent=1); json.dump(S, open(outp.replace('.json', '-structs.json'), 'w'), indent=1)
    print('structure-valued providers', len(S))
    print('providers with readers', len(R))
