#!/usr/bin/env bash
cd /workspace/tcslib-fill
timeout 250 /workspace/bin/probe.sh /workspace/tcslib-fill/Probe/ForeignDefs.lean > /tmp/foreign.out 2>&1
cp /tmp/foreign.out /workspace/rabin-evidence/seal/foreign-defs-by-decl.txt
python3 - <<'PY'
import re
targets="oddFactorProb_le blumFactorProb_le blumFactoring_of_factoring polyTimeComputable_oddGenRaw polyTimeComputable_blumGenRaw rabinSampler_spec rabinCollection_sampleClose polyTimeComputable_rabinFactorRaw rabinCollection_invProbAt_le rabinCollection_oneWay polyTimeComputable_blumInvRaw blumInv_spec blumSampler_spec rabinBlumTrapdoor_sampleClose rabinBlumTrapdoor_invProbAt_le rabinBlumTrapdoor_oneWay polyTimeComputable_rabinRootRaw blumFactorProb_le_invProbAt blumFactoring_of_rabinBlum_oneWay".split()
txt=open('/tmp/foreign.out').read()
entries=re.findall(r"^(\S+)\t\[(.*?)\]", txt, flags=re.M|re.S)
new=set(); base=set()
for n,lst in entries:
    names=[x.strip() for x in lst.replace("\n"," ").split(",") if x.strip()]
    isnew = ("rabin_" in n) or any(n.endswith("Candidates."+t) or ("Candidates."+t+".") in n for t in targets)
    (new if isnew else base).update(names)
open('/workspace/rabin-evidence/seal/foreign-defs-new-code.txt','w').write("\n".join(sorted(new))+"\n")
open('/workspace/rabin-evidence/seal/foreign-defs-base-only.txt','w').write("\n".join(sorted(base-new))+"\n")
unseal={
 "Complexity.PolyExpr.eval":"notation (fill notes, item 2)",
 "TCSlib.Cryptography.Candidates.DistinctPrimes":"reducible abbreviation (notation)",
 "Complexity.NUPPT.Coins":"reducible abbreviation (notation)",
 "TCSlib.Cryptography.NumberTheory.Primes":"reducible abbreviation (notation)",
 "Complexity.NUPPT.coins":"structure projection","Complexity.NUPPT.adv":"structure projection","Complexity.NUPPT.advice":"structure projection",
 "TCSlib.Cryptography.Collection.D":"structure projection","TCSlib.Cryptography.Collection.decD":"structure projection",
 "TCSlib.Cryptography.Collection.f":"structure projection","TCSlib.Cryptography.Collection.fintypeD":"structure projection",
 "TCSlib.Cryptography.Collection.gen":"structure projection","TCSlib.Cryptography.Collection.inhabitedD":"structure projection",
 "TCSlib.Cryptography.Collection.sample":"structure projection","TCSlib.Cryptography.PermCollection.toCollection":"structure projection",
 "TCSlib.Cryptography.TrapdoorCollection.toPermCollection":"structure projection",
 "TCSlib.Cryptography.Collection.encD":"structure projection","TCSlib.Cryptography.Collection.eval":"structure projection",
 "TCSlib.Cryptography.PermCollection.perm":"structure projection","TCSlib.Cryptography.TrapdoorCollection.inv":"structure projection",
}
allnames=sorted(new|base)
seal=[n for n in allnames if n not in unseal]
open('/workspace/rabin-evidence/seal/seal-list.txt','w').write("\n".join(seal)+"\n")
open('/workspace/rabin-evidence/seal/not-sealed.txt','w').write("\n".join(f"{k}\t{v}" for k,v in sorted(unseal.items()) if k in allnames)+"\n")
s=open('TCSlib/Cryptography/Candidates/Rabin.lean').read()
anchor="open Complexity Turing NumberTheory Finset\n"
s=s.replace(anchor, anchor+"\n-- RULE-10 SEAL (evidence copy; not part of the delivery source)\nattribute [local irreducible]\n  "+"\n  ".join(seal)+"\n",1)
open('Probe/RabinSealed.lean','w').write(s)
print("sealed", len(seal), "new-code foreign", len(new), "base-only", len(base-new))
PY
cp Probe/RabinSealed.lean /workspace/rabin-evidence/seal/
timeout 280 /workspace/bin/probe.sh /workspace/tcslib-fill/Probe/RabinSealed.lean > /workspace/rabin-evidence/logs/seal-main.log 2>&1
grep "error" /workspace/rabin-evidence/logs/seal-main.log
tail -1 /workspace/rabin-evidence/logs/seal-main.log
