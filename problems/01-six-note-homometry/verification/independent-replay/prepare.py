import json,re,hashlib,shutil
from pathlib import Path
root=Path(__file__).resolve().parent
original=root.parent/'lean'
author=json.loads((original/'frozen_sources.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(original/'frozen_sources.json')=='30b6718a5a092793611c48c936b15d6812442b7dd0d85873a6c890b16b6d4636'
# All sources copied after the author's explicit freeze, with no original objects.
src=root/'sources';src.mkdir(exist_ok=False)
for f,h in author['source_sha256'].items():
    p=original/f
    assert sha(p)==h, f
    shutil.copy2(p,src/f)
shutil.copy2(original/'frozen_sources.json',root/'author_frozen_sources.json')
def strip_comments(s):
    out=[]; i=0; level=0
    while i<len(s):
        if s[i:i+2]=='/-':level+=1;i+=2
        elif level and s[i:i+2]=='-/':level-=1;i+=2
        elif level:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    return ''.join(out)
def imports(p):
    s=strip_comments(p.read_text())
    return re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)',s,re.M)
order=[];direct={};seen=set(); external=set()
def visit(m):
    if m in seen:return
    p=src/(m.replace('.','/')+'.lean')
    if not p.exists():external.add(m);return
    seen.add(m);direct[m]=imports(p)
    for d in direct[m]:visit(d)
    order.append(m)
for m in ['FullAudit','ParametricAudit']:visit(m)
assert set(order)==set(author['build_order']), (set(order)^set(author['build_order']))
scan={m:re.findall(r'\b(?:sorry|admit|axiom|native_decide|implemented_by|unsafe)\b',strip_comments((src/(m+'.lean')).read_text())) for m in order}
assert not any(scan.values()),scan
manifest={'root_modules':['FullAudit','ParametricAudit'],'independently_derived_build_order':order,'direct_imports':direct,'external_direct_imports':sorted(external),'source_sha256':{m+'.lean':sha(src/(m+'.lean')) for m in order},'forbidden_token_scan':scan}
(root/'source_closure.json').write_text(json.dumps(manifest,indent=2))
(root/'REBUILD_ORDER.txt').write_text('\n'.join(order)+'\nIndependentExactStatement\n')
print(json.dumps({'local_modules':len(order),'direct_external_modules':len(external),'independently_derived_order':order},indent=2))
