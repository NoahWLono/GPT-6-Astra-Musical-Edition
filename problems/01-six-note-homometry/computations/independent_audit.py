from itertools import combinations
from collections import Counter
from math import gcd
import resource,json,time
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
start=time.process_time(); out=[]
def congruent(A,B,n):
 return any({(s*x+t)%n for x in A}==B for s in (-1,1) for t in range(n))
for n in range(6,25):
 counts=Counter(); total=0
 for d in range(1,n):
  dist0={x:min(x,n-x) for x in range(n)}
  distd={x:min((x-d)%n,(d-x)%n) for x in range(n)}
  for cs in combinations([x for x in range(1,n) if x!=d],5):
   total+=1
   if sorted(dist0[x] for x in cs)!=sorted(distd[x] for x in cs):continue
   C=set(cs);A=C|{0};B=C|{d}
   if congruent(A,B,n):continue
   m=n//gcd(d,n); P=C-{(d-x)%n for x in C}; S=C-P
   assert all((x+d)%n in P for x in P)
   assert {(d-x)%n for x in S}==S
   assert (m,len(P),len(S)) in [(2,2,3),(2,4,1),(3,3,2),(4,4,1)]
   counts[str(m)]+=1
 assert bool(counts)==(n>=12 and (n%3==0 or n%4==0))
 out.append(dict(n=n,checked=total,nontrivial_marked_counts=dict(counts)))
 print(out[-1],flush=True)
json.dump({'cpu_seconds':time.process_time()-start,'results':out},open('independent_audit_results.json','w'),indent=2)
