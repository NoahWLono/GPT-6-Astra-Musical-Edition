from math import gcd
import resource, shutil, json
resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
assert shutil.disk_usage('.').free>4*1024**3

def canon(A,n):
 return min(tuple(sorted((s*x+t)%n for x in A)) for s in (1,-1) for t in range(n))
rows=[]
for s in range(1,21):
 n=8*s; pairs=set();examples={}
 for r in (s,5*s):
  for a in range(1,2*s):
   if a==s: continue
   C={(a+2*s*j)%n for j in range(4)}|{r}
   A=C|{0};B=C|{2*s}
   ca,cb=canon(A,n),canon(B,n)
   assert ca!=cb
   key=tuple(sorted((ca,cb)));pairs.add(key);examples.setdefault(key,(r,a))
 assert len(pairs)==2*(s//2),(s,len(pairs))
 rows.append(dict(n=n,bracelet_pairs=len(pairs),representative_parameters=list(examples.values())))
 print(n,len(pairs),flush=True)
with open('order_four_results.json','w') as f:json.dump(rows,f,indent=2)
