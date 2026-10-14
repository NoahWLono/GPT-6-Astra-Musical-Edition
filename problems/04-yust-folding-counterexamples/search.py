from itertools import combinations
from collections import Counter,defaultdict
import json,sys,time

def canon(A,mod=None):
 A=sorted(A)
 if mod:
  return min(tuple(sorted(((sgn*a+t)%mod for a in A))) for sgn in [1,-1] for t in range(mod))
 if not A:return ()
 return min(tuple(a-A[0] for a in A),tuple(A[-1]-a for a in A[::-1]))

def deck(A,mod=None):return Counter(canon(A[:i]+A[i+1:],mod) for i in range(len(A)))
def intervals(A,mod=None):
 return Counter(min((b-a)%mod,(a-b)%mod) if mod else b-a for a,b in combinations(A,2))
def related(A,mod=None):
 out=set()
 for a,b in ((a,b) for a in A for b in A if a!=b):
  core=set(A)-{a,b}
  if mod:
   for sgn in [1,-1]:
    for t in range(mod):
     if {(sgn*c+t)%mod for c in core}==core:
      q=(sgn*a+t)%mod
      if q not in set(A)-{a}:out.add(canon(tuple(sorted((set(A)-{a})|{q})),mod))
  elif core:
   t=min(core)+max(core)
   if {t-c for c in core}==core:
    q=t-a
    if q not in set(A)-{a}:out.add(canon(tuple(sorted((set(A)-{a})|{q}))))
 return out

def run(n,limit,mod=None):
 AS=sorted({canon(A,mod) for A in combinations(range(limit+1 if not mod else mod),n)})
 D={A:deck(A,mod) for A in AS}
 I={A:intervals(A,mod) for A in AS}
 R={A:related(A,mod) for A in AS}
 idx=defaultdict(list)
 for A in AS:
  expanded=sorted(D[A].elements())
  for pair in set(combinations(expanded,2)):idx[pair].append(A)
 pairs={tuple(sorted((A,B))) for group in idx.values() for A,B in combinations(group,2)}
 good=[];bad=[]
 for A,B in sorted(pairs):
  overlap=sum((I[A]&I[B]).values())
  if overlap>=n*(n-1)//2-1:
   good.append((A,B))
   if B not in R[A]:
    info={'A':A,'B':B,'shared_deck':list((D[A]&D[B]).elements()),'intervalA':sorted(I[A].elements()),'intervalB':sorted(I[B].elements()),'shared_intervals':overlap,'relatedA':sorted(R[A])}
    bad.append(info)
 print(json.dumps({'n':n,'limit':limit,'mod':mod,'set_classes':len(AS),'pairs_with_two_shared_subsets':len(pairs),'matching_pairs':len(good),'counterexamples_count':len(bad),'counterexamples':bad[:10]}),flush=True)
 return bad
if __name__=='__main__':
 mod=int(sys.argv[1]) if len(sys.argv)>1 else 0
 if mod:
  for n in range(3,mod+1):run(n,mod,mod)
 else:
  for n in range(3,9):run(n,16)
