import pathlib, re, json, hashlib, shutil, subprocess
base=pathlib.Path('/workspace/shared/music-research/03-algebraic-tunings')
p=base/'independent-replay'; sources=p/'sources'; objects=p/'objects'
sources.mkdir(exist_ok=True); objects.mkdir(exist_ok=True)
assert not list(objects.iterdir()), 'Fresh objects directory must start empty'
sha=lambda q: hashlib.sha256(q.read_bytes()).hexdigest()
manifest_path=base/'replay-manifest.json'
assert sha(manifest_path)=='1070d311cb04ff5c2641f3a0fd2a5bd3ef42bd7e6b369f92538f80e500747797'
manifest=json.loads(manifest_path.read_text()); listed={r['module']:r for r in manifest['topological_modules']}
def strip_comments(s):
    i=0; depth=0; out=[]
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif s[i:i+2]=='--':
            end=s.find('\n',i); i=len(s) if end<0 else end
        else: out.append(s[i]); i+=1
    assert depth==0
    return ''.join(out)
order=[]; gray=set(); seen=set(); imports={}; externals=set()
def visit(mod):
    if mod in seen:return
    assert mod not in gray, 'Import cycle'
    gray.add(mod); src=base/(mod.replace('.','/')+'.lean'); code=strip_comments(src.read_text())
    deps=[]
    for line in code.splitlines():
        if re.match(r'^\s*import\s',line): deps.extend(line.strip().split()[1:])
    imports[mod]=deps
    for dep in deps:
        if (base/(dep.replace('.','/')+'.lean')).exists():visit(dep)
        else:externals.add(dep)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code),mod
    gray.remove(mod); seen.add(mod); order.append(mod)
visit('GoldenExact')
assert seen==set(listed), (seen-set(listed),set(listed)-seen)
assert len(order)==18
pos={m:i for i,m in enumerate([r['module'] for r in manifest['topological_modules']])}
assert all(pos[d]<pos[m] for m,ds in imports.items() for d in ds if d in pos)
assert (base/'replay-order.txt').read_text().splitlines()==[r['module'] for r in manifest['topological_modules']]
mathlib=pathlib.Path(manifest['mathlib_root']); lean=pathlib.Path(manifest['lean_binary'])
assert sha(lean)==manifest['lean_binary_sha256']
for n in ('lean-toolchain','lake-manifest.json'): assert sha(mathlib/n)==manifest[n+'_sha256']
commit=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
assert commit=='905b95818eb32af7874a58b427f50c1711a5e96c'
assert not subprocess.check_output(['git','-C',str(mathlib),'status','--porcelain','--untracked-files=no'],text=True).strip()
libs=[mathlib/'.lake/build/lib/lean']+sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))
external_records=[]
for mod in sorted(externals):
    found=[lib/(mod.replace('.','/')+'.olean') for lib in libs if (lib/(mod.replace('.','/')+'.olean')).exists()]
    assert len(found)==1,(mod,found)
    external_records.append({'module':mod,'object':str(found[0]),'object_sha256':sha(found[0])})
source_records=[]
old=base/'verified-before-comment-cleanup'
for m in order:
    src=base/(m+'.lean'); r=listed[m]
    assert sha(src)==r['source_sha256'],m
    assert strip_comments(src.read_text())==strip_comments((old/(m+'.lean')).read_text()),m
    shutil.copyfile(src,sources/src.name)
    source_records.append({'module':m,'source_sha256':sha(src),'imports':imports[m]})
report={'target':'AlgebraicTunings.golden_exact_maximum','manifest_sha256':sha(manifest_path),'mathlib_commit':commit,'lean_binary':str(lean),'lean_binary_sha256':sha(lean),'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'source_root':str(sources),'objects_root':str(objects),'lean_path':[str(objects)]+list(map(str,libs)),'modules':source_records,'direct_external_imports':external_records,'source_scan':'No sorry, admit, axiom, or native_decide tokens outside comments in reachable project sources','comment_cleanup':'All noncomment bytes match original verified source snapshots','trust_boundary':'Fresh rebuild of entire reachable project closure, using pinned existing Lean and Mathlib/package objects; Mathlib itself is not rebuilt.'}
(p/'preflight.json').write_text(json.dumps(report,indent=2)+'\n')
shutil.copyfile(manifest_path,p/'author-manifest.json')
print(json.dumps({'module_count':len(order),'order':order,'external_count':len(externals),'manifest_sha256':report['manifest_sha256'],'status':'preflight passed; no compilation started'},indent=2))
