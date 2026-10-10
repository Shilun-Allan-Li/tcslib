import os, re, sys, glob, collections
root = sys.argv[1]
def strip(src):
    out=[];i=0;depth=0;n=len(src)
    while i<n:
        if src.startswith('/-',i): depth+=1;i+=2;continue
        if depth and src.startswith('-/',i): depth-=1;i+=2;continue
        if depth: i+=1;continue
        if src.startswith('--',i):
            j=src.find('\n',i); i = n if j<0 else j; continue
        out.append(src[i]);i+=1
    return ''.join(out)
TOK = re.compile(r"[A-Za-z_Ͱ-Ͽ₀-ₜ][A-Za-z0-9_'.Ͱ-Ͽ₀-ₜ!?]*|\d+|\S")
KW = set("def theorem lemma abbrev instance structure private protected noncomputable by have show from fun at with calc exact apply intro intros rw simp simp_all omega cases rcases obtain refine constructor induction match if then else let in using only decide norm_num linarith nlinarith positivity aesop rfl ring field_simp unfold split contradiction exfalso subst congr ext funext specialize use exists left right trivial assumption dsimp change generalize gcongr push_neg by_contra by_cases".split())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def decls(text):
    ms = list(DECL.finditer(text))
    for i,m in enumerate(ms):
        end = ms[i+1].start() if i+1<len(ms) else len(text)
        yield m.group(1), text[m.start():end]
def toks(s, abstract):
    t = TOK.findall(s)
    return [('ID' if abstract and re.match(r"[A-Za-z_]",x) and x not in KW else x) for x in t]
def shingles(t, k): return {tuple(t[i:i+k]) for i in range(max(0,len(t)-k+1))}
surface = ['TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean','TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean',
           'TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean','TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean',
           'TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean','TCSlib/Complexity/ClassNP/PClosure.lean']
pclosure_new = {'mem_P_of_blockAny','mem_P_of_blockMajority','mem_P_of_blockXorAny'}
allfiles = [os.path.relpath(p,root) for p in glob.glob(os.path.join(root,'TCSlib/**/*.lean'),recursive=True)]
EX_K, AB_K = 25, 50
hay_ex, hay_ab = collections.defaultdict(set), collections.defaultdict(set)
for f in allfiles:
    txt = strip(open(os.path.join(root,f),encoding='utf-8').read())
    for name, body in decls(txt):
        for s in shingles(toks(body,False),EX_K): hay_ex[s].add((f,name))
        for s in shingles(toks(body,True),AB_K): hay_ab[s].add((f,name))
print(f"haystack: {len(allfiles)} files")
rows=[]
for f in surface:
    txt = strip(open(os.path.join(root,f),encoding='utf-8').read())
    for name, body in decls(txt):
        if f.endswith('PClosure.lean') and name not in pclosure_new: continue
        for mode,k,hay in (('exact',EX_K,hay_ex),('renamed',AB_K,hay_ab)):
            sh = shingles(toks(body, mode=='renamed'), k)
            if not sh: continue
            hits = collections.Counter()
            for s in sh:
                for (g,n2) in hay.get(s,()):
                    if (g,n2) != (f,name): hits[(g,n2)] += 1
            if hits:
                (g,n2),c = hits.most_common(1)[0]
                rows.append((c/len(sh), mode, f.split('/')[-1], name, len(sh), g, n2))
rows.sort(reverse=True)
screened = sum(1 for f in surface for n,_ in decls(strip(open(os.path.join(root,f)).read())) if not (f.endswith('PClosure.lean') and n not in pclosure_new))
print(f"declarations screened: {screened}")
print("top overlaps (fraction of the declaration's shingles found in ONE other declaration elsewhere):")
for r in [r for r in rows if r[0]>=.5]: print(f"  {r[0]:.0%} [{r[1]}] {r[2]}::{r[3]} ({r[4]} sh) ~ {r[5]}::{r[6]}")
print(f"declarations with >=50% overlap: exact={sum(1 for r in rows if r[1]=='exact' and r[0]>=.5)}, renamed={sum(1 for r in rows if r[1]=='renamed' and r[0]>=.5)}")
