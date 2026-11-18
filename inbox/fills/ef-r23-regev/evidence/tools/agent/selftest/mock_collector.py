"""mock_collector.py <out.log> (tools-agent, fill ef-r23-regev): writes a clearly MOCK collector log (the NmCollect
record format: CLOSURE / CAT / ROOT / CAT-COUNT / MODULE lines) for the series-1+2 owners, so that the Python half of
rule10_regev.sh (mkseals_ab/mkseals_coe/mkctl_regev, DRY=1 runner) can be exercised without Lean. The closures and
catalog are INVENTED (a handful of definitions); nothing here is evidence about the library."""
import sys, json
def comps(n): return [["str", s] for s in n.split('.')]
def ident(n): return {"display": n, "components": comps(n)}
MA = 'TCSlib.Cryptography.Encoding.ModularArithmetic'; SA = 'TCSlib.Cryptography.Encryption.Symmetric.Regev.Asymptotic'
SR = 'TCSlib.Cryptography.Encryption.Symmetric.Regev'
MOD = 'TCSlib.Cryptography.Encoding.Modular'; PE = 'TCSlib.Complexity.PolyExpr'; FD = 'TCSlib.InformationTheory.FinDist'
defs = [(MA + '.' + n, MA) for n in ['addMod', 'vecAddStep', 'vecAddModWords', 'subsetSumStep', 'subsetSumModWords', 'modContext']]
defs += [(SR + '.' + n, SA) for n in ['shiftAdvice', 'shiftPre', 'shiftAdviceBound']]
defs += [(MOD + '.encodeVector', MOD), ('Complexity.PolyExpr.eval', PE), (FD.replace('InformationTheory.FinDist', 'InformationTheory') + '.FinDist.instCoeFunForallReal', FD)]
clo = {MA: [MOD, PE, FD], 'TCSlib.Cryptography.Encoding': [MA, MOD, PE, FD], SA: [MA, MOD, PE, FD], SR: [MA, SA, MOD, PE, FD]}
with open(sys.argv[1], 'w') as f:
    f.write('MOCK collector log -- invented records, not Lean output\n')
    for m, c in clo.items(): f.write('CLOSURE ' + json.dumps({"module": m, "closure": sorted(c)}, separators=(',', ':')) + '\n')
    for n, h in defs:
        f.write('CAT ' + json.dumps({"name": ident(n), "home": ident(h), "kind": "def", "status": "semireducible",
                                     "instance": n.endswith('instCoeFunForallReal'), "matcher": False, "abbrev": False}) + '\n')
    f.write('ROOT ' + json.dumps({"module": SA, "name": ident(SR + '.shiftPre'), "kind": "def", "type_refs": [],
                                  "value_refs": [ident(MA + '.vecAddModWords')]}) + '\n')
    f.write(f'CAT-COUNT {len(defs)}\n')
    for m in clo: f.write(f'MODULE {m}: stored {1 if m == SA else 0}\n')
