import json,re,hashlib,time,resource
from pathlib import Path
root=Path(__file__).resolve().parent
m=Path('/workspace/scratch/caabcb85bd83/dependencies/mathlib4-v4.32.2')
tool=Path('/workspace/scratch/caabcb85bd83/toolchains/lean-4.32.2-linux')
roots=[root/'sources',m]+sorted((m/'.lake/packages').glob('*'))+[tool/'src/lean',tool/'src/lean/lake']
# The traversal includes implicit Init as well as explicit public/meta imports.
def strip_comments(s):
    out=[];i=0;level=0
    while i<len(s):
        if s[i:i+2]=='/-':level+=1;i+=2
        elif level and s[i:i+2]=='-/':level-=1;i+=2
        elif level:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':
            out.append('"');i+=1
            while i<len(s):
                if s[i]=='\\':out.extend([' ',' ']);i+=2
                elif s[i]=='"':out.append('"');i+=1;break
                else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)
records={};missing=[];visiting=set()
def visit(name):
    if name in records or name in visiting:return
    visiting.add(name)
    p=next((r/(name.replace('.','/')+'.lean') for r in roots if (r/(name.replace('.','/')+'.lean')).is_file()),None)
    if p is None:missing.append(name);visiting.remove(name);return
    b=p.read_bytes();s=strip_comments(b.decode());imports=[]
    for line in s.splitlines():
        mat=re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)\s*',line)
        if mat:imports.append(mat.group(1))
    if not re.search(r'^\s*prelude\s*$',s,re.M) and name!='Init':imports=['Init']+imports
    records[name]={'source_path':str(p),'source_sha256':hashlib.sha256(b).hexdigest(),'imports':imports}
    for imp in imports:visit(imp)
    visiting.remove(name)
for target in ['FullAudit','ParametricAudit','IndependentExactStatement']:visit(target)
report={'roots':['FullAudit','ParametricAudit','IndependentExactStatement'],'source_roots':[str(x) for x in roots],'module_count':len(records),'unresolved_modules':sorted(set(missing)),'scope':'Full recursive source import closure, with implicit Init; external libraries use prebuilt pinned objects and are not freshly compiled in this audit.','modules':records,'script_cpu_seconds':sum(resource.getrusage(resource.RUSAGE_SELF)[:2])}
(root/'full_transitive_import_closure.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:report[k] for k in ['module_count','unresolved_modules','script_cpu_seconds']},indent=2))
