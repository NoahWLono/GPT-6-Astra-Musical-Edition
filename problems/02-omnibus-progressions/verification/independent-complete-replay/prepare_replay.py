import pathlib,re,json,hashlib,shutil,subprocess
root=pathlib.Path(__file__).resolve().parent
base=root.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   i=s.find('\n',i)
   if i<0:break
   out.append('\n');i+=1
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
manifest=json.loads((base/'COMPLETE_REBUILD_MANIFEST.json').read_text())
seen=set();order=[];external=set();imports={};banned={};hashes={}
def visit(n):
 if n in seen:return
 p=base/(n+'.lean')
 if not p.exists():external.add(n);return
 seen.add(n);active=strip_comments(p.read_text())
 ds=[]
 for line in active.splitlines():
  if line.strip().startswith('import '):ds+=line.strip()[7:].split()
 imports[n]=ds
 for m in ds:visit(m)
 forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|implemented_by|extern)\b',active)
 if forbidden:banned[n]=forbidden
 hashes[n]=sha(p);order.append(n)
for n in manifest['targets']:visit(n)
assert order==[m['module'] for m in manifest['order']]
assert external==set(manifest['external_imports'])
assert all(hashes[m['module']]==m['source_sha256'] for m in manifest['order'])
assert not banned,banned
src=root/'sources';src.mkdir(exist_ok=False)
for n in order:shutil.copyfile(base/(n+'.lean'),src/(n+'.lean'))
shutil.copyfile(base/'COMPLETE_REBUILD_MANIFEST.json',root/'FROZEN_AUTHOR_MANIFEST.json')
(root/'REBUILD_ORDER.txt').write_text('\n'.join(order)+'\n')
lean=pathlib.Path('/workspace/scratch/caabcb85bd83/toolchains/lean-4.32.2-linux/bin/lean')
mathlib=pathlib.Path('/workspace/scratch/caabcb85bd83/dependencies/mathlib4-v4.32.2')
paths=[mathlib/'.lake/build/lib/lean']+sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))
collisions=[str(p/(n+'.olean')) for p in paths for n in order if (p/(n+'.olean')).exists()]
assert not collisions,collisions
lock={'lean_sha256':sha(lean),'mathlib_head':subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip(),'mathlib_toolchain':(mathlib/'lean-toolchain').read_text().strip(),'mathlib_manifest_sha256':sha(mathlib/'lake-manifest.json'),'mathlib_lake_manifest':json.loads((mathlib/'lake-manifest.json').read_text()),'external_search_paths':[str(p) for p in paths]}
report={'targets':manifest['targets'],'order':order,'external_imports':sorted(external),'local_imports':imports,'source_sha256':hashes,'author_manifest_sha256':sha(base/'COMPLETE_REBUILD_MANIFEST.json'),'banned_active_tokens':banned,'external_project_object_collisions':collisions,'no_project_objects_copied':True}
(root/'DEPENDENCY_LOCK.json').write_text(json.dumps(lock,indent=2)+'\n')
(root/'PREPARATION_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'modules':len(order),'manifest_matched':True,'external_imports':sorted(external),'banned_active_tokens':banned,'copied_project_objects':0}))
