"""(bb1-sim, lead: copied unchanged from bb1-sim-statements, which copied it unchanged from bb1-machine.)
sk15.py <files>: proofs of >= 15 lines (style_lint's measure: from the declaration line to the next
declaration, excluding blanks and the docstring) whose docstring lacks **Proof sketch.**"""
import re,sys
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected |noncomputable |nonrec )*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom)\b")
for f in sys.argv[1:]:
    lines=open(f,encoding='utf-8').read().splitlines()
    starts=[i for i,l in enumerate(lines) if DECL.match(l)]
    for k,i in enumerate(starts):
        end=starts[k+1] if k+1<len(starts) else len(lines)
        # trim trailing docstring of next decl
        j=end
        while j>i and (lines[j-1].strip()=='' or lines[j-1].startswith('/--') or lines[j-1].startswith('omit') or lines[j-1].startswith('/-!')):
            j-=1
        # remove a docstring block preceding next decl
        body=lines[i:end]
        # find docstring before next decl
        t=end-1
        while t>i and lines[t].strip()=='' : t-=1
        if t>i and lines[t].rstrip().endswith('-/'):
            u=t
            while u>i and '/--' not in lines[u] and '/-!' not in lines[u]: u-=1
            end2=u
        else: end2=end
        n=sum(1 for l in lines[i:end2] if l.strip() and not l.strip().startswith('--') and not l.startswith('end ') and not l.startswith('section') and not l.startswith('variable') and not l.startswith('omit'))
        # docstring before i
        d=i-1
        while d>=0 and lines[d].startswith('omit'): d-=1
        doc=''
        if d>=0 and lines[d].rstrip().endswith('-/'):
            u=d
            while u>0 and '/--' not in lines[u]: u-=1
            doc='\n'.join(lines[u:d+1])
        if n>=15 and 'Proof sketch' not in doc and not re.match(r'.*\b(def|structure|abbrev)\b',lines[i].split('(')[0]):
            name=re.sub(r'^.*?(theorem|lemma|def|instance) ','',lines[i]).split()[0]
            print(f'{f.split("/")[-1]}:{i+1}: {name} {n}')
