"""List declarations containing a `sorry` token (comments/strings stripped) in Lean files read from git."""
import re, subprocess, sys
rev = sys.argv[1]; paths = sys.argv[2:]
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque)\s+([^\s:({\[]+)')
def strip(src):
    out=[];i=0;n=len(src);depth=0
    while i<n:
        if src.startswith('/-',i): depth+=1;i+=2;continue
        if depth and src.startswith('-/',i): depth-=1;i+=2;continue
        if depth: out.append('\n' if src[i]=='\n' else ' ');i+=1;continue
        if src.startswith('--',i):
            j=src.find('\n',i); j=n if j<0 else j; out.append(' '*(j-i)); i=j; continue
        if src[i]=='"':
            j=i+1
            while j<n and src[j]!='"':
                j+= 2 if src[j]=='\\' else 1
            out.append(' '*(j+1-i)); i=j+1; continue
        out.append(src[i]); i+=1
    return ''.join(out)
for p in paths:
    src=subprocess.run(['git','show',f'{rev}:{p}'],capture_output=True,text=True,check=True).stdout
    s=strip(src).split('\n'); cur=None; ns=[]
    for ln,line in enumerate(s,1):
        m=re.match(r'^namespace\s+(\S+)',line)
        if m: ns.append(m.group(1))
        m=re.match(r'^end\s+(\S+)',line)
        if m and ns and ns[-1]==m.group(1): ns.pop()
        m=decl.match(line)
        if m: cur=(ln,'.'.join(ns+[m.group(2)]))
        if re.search(r'\bsorry\b',line) and cur:
            print(f'{p}:{cur[0]}\t{cur[1]}')
            cur=(cur[0],cur[1]+'#dup')
