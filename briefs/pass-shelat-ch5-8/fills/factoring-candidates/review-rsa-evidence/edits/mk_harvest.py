# Build the conditional harvest test copy: proposed public lemmas (stub block, proofs moved from the
# rsa_ copies) before the namespace, the rsa_ copies deleted, and every use re-pointed.
# usage: mk_harvest.py SRC OUT_TEST OUT_FILE   (OUT_FILE: the re-pointed RSA.lean without the stub block)
import re,sys
src,out_test,out_file=sys.argv[1],sys.argv[2],sys.argv[3]
s=open(src).read()
KW=r'(?:private |protected |noncomputable |@\[[^\]]*\]\s*)*(?:theorem|lemma|def|abbrev|instance)\b'
def remove_decl(name):
    global s
    L=s.split('\n')
    i=next(k for k,l in enumerate(L) if re.match(KW+r'\s+'+re.escape(name)+r'\b',l))
    d=i
    if L[i-1].rstrip().endswith('-/'):
        d=i-1
        while not L[d].lstrip().startswith('/--'): d-=1
    e=i+1
    while e<len(L) and L[e].strip()!='': e+=1
    # drop the declaration and one following blank line
    del L[d:e+1]
    s='\n'.join(L)
for n in ['rsa_listToNat_one','rsa_listToNat_nil','rsa_findSome?_ite','rsa_find?_range_lt','rsa_comp',
          'rsa_listToNat_ones','rsa_listToNat_mulStr','rsa_ptc_congr','rsa_listToNat_append',
          'rsa_listToNat_zeros_append','rsa_drop_zeros_append','rsa_subStr_self']:
    remove_decl(n)
# the one use of rsa_findSome?_ite becomes the published reading of rejectBlocksL
old='''  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq,
    rsa_findSome?_ite (fun i => val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w)) val]'''
assert s.count(old)==1
s=s.replace(old,'''  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq_find?]''')
ren=[('rsa_listToNat_zeros_append','listToNat_natToList_zero_append'),
     ('rsa_drop_zeros_append','natToList_zero_append_drop'),
     ('rsa_listToNat_append','listToNat_append'),
     ('rsa_listToNat_ones','listToNat_replicate_true'),
     ('rsa_listToNat_one','listToNat_singleton_true'),
     ('rsa_listToNat_nil','listToNat_nil'),
     ('rsa_listToNat_mulStr','listToNat_mulStr'),
     ('rsa_subStr_self','subStr_self'),
     ('rsa_find?_range_lt','IterateFind.find?_range_and_lt'),
     ('rsa_findSome?_ite','rejectBlocksL_eq_find?'),
     ('rsa_ptc_congr','PolyTimeComputable.congr'),
     ('rsa_comp',"PolyTimeComputable.comp'")]
for a,b in ren:
    s=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(a)+r'(?![A-Za-z0-9_?!\'])',b,s)
assert 'rsa_listToNat_one' not in s and 'rsa_comp ' not in s
open(out_file,'w').write(s)
stub=open(sys.argv[0].replace('mk_harvest.py','harvest-stubs.lean')).read()
i=s.index('namespace TCSlib.Cryptography.Candidates\n')
open(out_test,'w').write(s[:i]+stub+'\n'+s[i:])
print('ok')
