import re,sys
def find_block(src,name,kinds=('theorem','def','lemma','noncomputable def','abbrev','private theorem','private def','private lemma','private noncomputable def')):
    # locate declaration line
    pat=re.compile(r'^(?:@\[[^\]]*\]\s*\n)?(?:%s) %s\b'%('|'.join(re.escape(k) for k in kinds),re.escape(name)),re.M)
    m=pat.search(src)
    if not m: raise KeyError(name)
    t=m.start()
    # include preceding docstring if directly above
    pre=src[:t].rstrip('\n')
    d=t
    if pre.endswith('-/'):
        ds=pre.rfind('/--')
        if ds>=0 and '\n\n' not in pre[ds:]+'' or ds>=0:
            # ensure the docstring belongs (no blank line between)
            between=src[pre.rfind('-/')+2:t]
            if between.strip()=='' and between.count('\n')<=1:
                d=ds
    # end: next line at column 0 starting a new item, after the declaration line
    m2=re.compile(r'\n(?=(/--|/-!|end |section|namespace|theorem |def |lemma |private |noncomputable |@\[|abbrev |variable|open |instance |-- ))').search(src,m.end())
    e=m2.start()+1 if m2 else len(src)
    return d,e
def get(src,name): d,e=find_block(src,name); return src[d:e]
def remove(src,name):
    d,e=find_block(src,name)
    out=src[:d]+src[e:]
    out=re.sub(r'\n{3,}','\n\n',out)
    return out
if __name__=='__main__':
    op,path=sys.argv[1],sys.argv[2]
    s=open(path).read()
    if op=='show':
        for n in sys.argv[3:]: print(get(s,n)); print('-----')
    elif op=='rm':
        for n in sys.argv[3:]: s=remove(s,n)
        open(path,'w').write(s)
