"""seal.py <worktree> <outdir>: write one sealed probe per new module: its source with
`attribute [local irreducible] <foreign TCSlib definitions it may read>` after the options."""
import sys, os
wt, out = sys.argv[1:]
C='TCSlib.Cryptography.'
base = ['TCSlib.Cryptography.Games.ProbComp.sample','TCSlib.Cryptography.Games.advantage',
  'TCSlib.Cryptography.Games.accept','TCSlib.Cryptography.Negligible','TCSlib.Cryptography.uprob',
  'Complexity.NUPPT.distinguisherL','Complexity.NUPPT.runAt','Turing.pairEncode',
  'TCSlib.Cryptography.Games.simulate','Complexity.NUPPT.toComp']
grp = [C+'Pairing.BilinearGen.desc',C+'Pairing.BilinearGen.inst',C+'Pairing.BilinearGen.OrderAtLeastExcept']
asm = [C+'Pairing.tupleStr',C+'Pairing.bdhStr',C+'Pairing.BilinearGen.dbdhGame',C+'Pairing.BilinearGen.dbdhAdv',
  C+'Pairing.BilinearGen.DBDHAssumption',C+'Pairing.BilinearGen.bdhGame',C+'Pairing.BilinearGen.BDHAssumption']
pk = [C+'Composability.FixedLengthScheme.decAnswer',C+'Composability.FixedLengthScheme.splitHalf',
  C+'Games.zeroBits',C+'Games.bitCodec',C+'padFin',C+'bitsToNat']
defs = [C+'AdvancedEncryption.IdentityBased.IBEScheme.'+n for n in ['honestRun','Correct','inLens','outLens','sidImpl','sidCodec','sidGame','SIDSecure','oracleImpl']]
bb = [C+'AdvancedEncryption.IdentityBased.'+n for n in ['bb1Scheme','BB1.F','BB1.setup','BB1.keyGen','BB1.encrypt','BB1.decrypt','BB1.idToZ','BB1.decodeT',
  'bb1SimParams','bb1SimKey','bb1SimInit','bb1SimKeyQ','bb1SimCt','bb1SimChal','bb1SimImpl','bb1SimGame']]
mods = {
 'Pairing/Group': ['TCSlib.Cryptography.uprob','Complexity.NUPPT.runAt'],
 'Pairing/Assumptions': base+grp,
 'Pairing/Operations': grp+['TCSlib.Cryptography.NumberTheory.listToNat','Turing.pairEncode'],
 'KeyExchange/Joux': base+grp+asm,
 'AdvancedEncryption/IdentityBased/Defs': base+pk,
 'AdvancedEncryption/IdentityBased/BonehBoyen': base+pk+grp+defs,
 'AdvancedEncryption/IdentityBased/BonehBoyenSecurity': base+pk+grp+asm+defs+bb,
}
os.makedirs(out, exist_ok=True)
for m, names in mods.items():
    src = open(os.path.join(wt,'TCSlib/Cryptography',m+'.lean')).read()
    anchor = 'set_option autoImplicit false\n'
    assert anchor in src
    seal = ''.join('attribute [local irreducible] ' + n + '\n' for n in names)
    open(os.path.join(out, m.replace('/','_')+'.lean'),'w').write(src.replace(anchor, anchor+seal,1))
    print(m, len(names))
