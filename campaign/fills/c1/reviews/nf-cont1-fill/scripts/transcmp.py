# transcmp.py: compare each authorized transcription with its source, comment-stripped, renamed
import re, sys, difflib
S='/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad'
R=S+'/review/nf-cont1-fill'; I=S+'/wt-hk/campaign/fills/c1/inputs'
head=R+'/wt-head/TCSlib/Complexity/ClassNP/NDNormalForm.lean'
def strip(src):
    out=[]; i=0; d=0; n=len(src)
    while i<n:
        if src.startswith('/-',i): d+=1; i+=2; continue
        if d and src.startswith('-/',i): d-=1; i+=2; continue
        if d: i+=1; continue
        if src.startswith('--',i):
            j=src.find('\n',i); i=n if j<0 else j; continue
        out.append(src[i]); i+=1
    return ''.join(out)
DECL=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev|instance|inductive|structure)\s+(\S+)", re.M)
def decl(f, name):
    t=strip(open(f,encoding='utf-8').read()); ms=list(DECL.finditer(t))
    for i,m in enumerate(ms):
        if m.group(1)==name:
            end=ms[i+1].start() if i+1<len(ms) else len(t)
            seg=t[m.start():end]
            seg=re.split(r'\n(?=#print|end |namespace |section |example|open |set_option|attribute)', seg)[0]
            return seg
    raise SystemExit('missing '+name+' in '+f)
ren=[('NfcPh','nf_Ph'),('NfcSt','nf_St'),('nfcStDecEq','nf_stDecEq'),('nfcStFintype','nf_stFintype'),('nfcPark','nf_park'),
     ('nfcM','nf_M'),('nfcAfter','nf_after'),('nfcRed','nf_red'),('nfcV','nf_V'),('nfc_retag','nf_retag'),('nfc_aReturn','nf_aReturn'),
     ('rv_bClear','nf_bClear'),('rv_entry','nf_entry'),('rv_tag','nf_tag'),('rv_inputSymbol_congr','nf_inputSymbol_congr'),('rvPark','nf_park')]
def norm(s):
    for a,b in ren: s=re.sub(r'\b'+a+r'\b',b,s)
    return s
pairs=[(I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','NfcPh','nf_Ph'),(I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','NfcSt','nf_St'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcStDecEq','nf_stDecEq'),(I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcStFintype','nf_stFintype'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcPark','nf_park'),(I+'/c1-fill-nf/NFReviewVProbe.lean.txt','rvPark','nf_park'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcM','nf_M'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcAfter','nf_after'),(I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcRed','nf_red'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfcV','nf_V'),(I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfc_retag','nf_retag'),
 (I+'/c1-fill-nf-cont1/NFContRouteTail.lean.txt','nfc_aReturn','nf_aReturn'),(I+'/c1-fill-nf-cont1/NFContClearTail.lean.txt','rv_bClear','nf_bClear'),
 (I+'/c1-fill-nf/NFReviewProbe.lean.txt','rv_entry','nf_entry'),(I+'/c1-fill-nf/NFReviewVProbe.lean.txt','rv_tag','nf_tag'),
 (I+'/c1-fill-nf/NFReviewProbe.lean.txt','rv_inputSymbol_congr','nf_inputSymbol_congr')]
for f,a,b in pairs:
    src=norm(decl(f,a)); dst=decl(head,b)
    ws=lambda s: ' '.join(s.split())
    eq = ws(src)==ws(dst)
    r=difflib.SequenceMatcher(None, ws(src), ws(dst)).ratio()
    print(f'=== {a} -> {b}: identical modulo renaming and whitespace: {eq}; similarity {r:.2f}; source {len(ws(src))} chars, landed {len(ws(dst))} chars')
    if not eq:
        sl=[l.strip() for l in src.split('\n') if l.strip()]; dl=[l.strip() for l in dst.split('\n') if l.strip()]
        for l in difflib.unified_diff(sl, dl, lineterm='', n=0):
            if l.startswith(('---','+++')): continue
            print('   ', l[:180])
