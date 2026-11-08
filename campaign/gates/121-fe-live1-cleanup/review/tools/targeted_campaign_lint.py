from pathlib import Path
import importlib.util,sys,json
sys.dont_write_bytecode=True
root=Path(sys.argv[1]).resolve();files=[x for x in sys.argv[2:]if x!='--check8b'];check8b='--check8b'in sys.argv[2:]
helper=root/'scripts/campaign_style_lint.py'
saved=sys.argv[:];sys.argv=[str(helper)]+(['--check8b']if check8b else [])
spec=importlib.util.spec_from_file_location('campaign_lint_targeted',helper);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);sys.argv=saved
assert m.ROOT==root and m.CHECK8B==check8b
for rel in files:
 p=root/rel;assert p.is_file();m.check_file(p)
 if m.is_facade(p):m.check_facade(p)
width=max((len(p)for _,p,_ in m.findings),default=1)
for level in ['FAIL','WARN','INFO']:
 for lv,p,msg in m.findings:
  if lv==level:print(f'{lv:4}  {p:<{width}}  {msg}')
fail=sum(l=='FAIL'for l,_,_ in m.findings);warn=sum(l=='WARN'for l,_,_ in m.findings)
print(f'\ncampaign_style_lint targeted canonical functions: {fail} FAIL, {warn} WARN over {len(files)} files; check8b={check8b}')
sys.exit(1 if fail else 0)
