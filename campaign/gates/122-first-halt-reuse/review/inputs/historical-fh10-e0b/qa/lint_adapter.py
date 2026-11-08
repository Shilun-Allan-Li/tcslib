from pathlib import Path
import importlib.util,sys,json
sys.dont_write_bytecode=True
kind,root_arg,helper_arg,metadata_arg,*paths=sys.argv[1:];root=Path(root_arg).resolve();helper=Path(helper_arg);files=[root/p for p in paths];sys.argv=[str(helper),*[str(f) for f in files]];spec=importlib.util.spec_from_file_location('actual_canonical_lint',helper);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.ROOT=root
if kind=='style':
 rows=[];actual=module.lint
 def observe(path):
  messages=actual(path);rows.extend({'path':str(path.resolve().relative_to(root)),'message':m} for m in messages);return messages
 module.lint=observe;code=module.main()
elif kind=='campaign':
 module.findings=[];module.CHECK8B=False
 for file in files:module.check_file(file)
 width=max(len(p) for _,p,_ in module.findings);failed=False
 for level in ('FAIL','WARN','INFO'):
  for lv,path,msg in module.findings:
   if lv==level:print(f'{lv:4}  {path:<{width}}  {msg}');failed |= lv=='FAIL'
 print(f"\nstyle_lint: {sum(1 for l,_,_ in module.findings if l=='FAIL')} FAIL, {sum(1 for l,_,_ in module.findings if l=='WARN')} WARN over {len(files)} files")
 code=1 if failed else 0;rows=[{'level':level,'path':path,'message':msg} for level,path,msg in module.findings]
else:raise SystemExit('unknown lint kind')
Path(metadata_arg).write_text(json.dumps({'kind':kind,'ROOT':str(root),'explicit_files':paths,'count_files':len(paths),'default_CHECK8B':False if kind=='campaign' else None,'exit':code,'findings':rows},indent=2)+'\n');raise SystemExit(code)
