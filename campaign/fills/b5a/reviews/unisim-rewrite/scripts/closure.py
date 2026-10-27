# closure.py <root> : import graph of TCSlib; prints downstream of CodeSimulator and upstream closure of the two imports
import os,re,sys
root=sys.argv[1]
mods={}
for dp,dn,fn in os.walk(os.path.join(root,'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p=os.path.join(dp,f); m=os.path.relpath(p,root)[:-5].replace('/','.')
            imps=[]
            for l in open(p,encoding='utf-8'):
                mm=re.match(r'^import\s+(\S+)',l)
                if mm: imps.append(mm.group(1))
                elif l.strip() and not l.startswith('import') and not l.startswith('/-') and not l.startswith('--') and not l.startswith(' ') and not l.startswith('Copyright') and not l.startswith('Released') and not l.startswith('Authors') and not l.startswith('-/'):
                    pass
            mods[m]=[i for i in imps if i.startswith('TCSlib')]
def up(m,seen):
    for i in mods.get(m,[]):
        if i not in seen: seen.add(i); up(i,seen)
    return seen
cs='TCSlib.Complexity.TuringMachine.CodeSimulator'
down=sorted(m for m in mods if cs in up(m,set()))
print('downstream of CodeSimulator:',len(down)); [print(' ',d) for d in down]
for imp in ['TCSlib.Complexity.TuringMachine.Nondeterministic','TCSlib.Complexity.TuringMachine.Build.InterpreterStartup']:
    u=up(imp,set()); print(imp,'closure',len(u),'contains CodeSimulator:',cs in u)
base=up(cs,set()); new=up('TCSlib.Complexity.TuringMachine.Nondeterministic',set())|up('TCSlib.Complexity.TuringMachine.Build.InterpreterStartup',set())|{'TCSlib.Complexity.TuringMachine.Nondeterministic','TCSlib.Complexity.TuringMachine.Build.InterpreterStartup'}
print('base closure',len(base),'overlay closure',len(base|new),'added:',sorted((base|new)-base))
for six in ['Build.InputRewind','Build.Rewind','Build.InputWindow','Build.SeamLayout','BufferWords','Nondeterministic']:
    print(six, ('TCSlib.Complexity.TuringMachine.'+six) in (base|new))
