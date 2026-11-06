import re,sys
W=sys.argv[1]
for spec in sys.argv[2:]:
    f,ln=spec.rsplit(':',1); tag=f.replace('/','_')[:-5]; ln=int(ln)
    log=open(f'{W}/{tag}.S.log').read()
    for m in re.finditer(r':(\d+):(\d+): error:?(.*?)(?=\n\S+\.lean:\d+:\d+:|\Z)', log, re.S):
        l=int(m.group(1))-2
        if l==ln: print(f'{f}:{l}', m.group(3).strip()[:420].replace('\n',' | ')); break
