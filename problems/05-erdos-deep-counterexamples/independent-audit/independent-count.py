from collections import Counter
from itertools import combinations
from math import comb, gcd
import json
claimed = {(4,4,3),(6,3,3),(6,5,3),(6,6,4),(6,6,6),(7,7,3),(9,4,3),(8,7,4),(8,8,5),(10,6,4),(12,4,4),(13,5,3),(13,7,4),(16,5,4),(21,6,4)}
results=[]
for n,gens,lens,K in [(34,(1,6,12),(10,9,5),14),(48,(1,6,18),(20,5,5),21)]:
    parts=[]
    total=Counter()
    for g,k in zip(gens,lens):
        points=[j*g%n for j in range(k)]
        assert len(set(points))==k
        # Use ordinary absolute difference, independent of Lean's two modular residues.
        hist=Counter(min(abs(x-y),n-abs(x-y)) for x,y in combinations(points,2))
        assert sorted(hist.values())==list(range(1,k))
        assert sum(hist.values())==comb(k,2)
        assert all(1<=d<=n//2 for d in hist)
        total.update(hist)
        parts.append(dict(g=g,k=k,order=n//gcd(n,g),points=points,histogram=dict(sorted(hist.items())),strict_half_order=k<=n//gcd(n,g)//2))
    assert sorted(total.values())==list(range(1,K))
    assert sum(total.values())==comb(K,2)
    assert lens not in claimed
    assert gcd(n,*gens)==1
    results.append(dict(n=n,K=K,constituents=parts,complete_histogram=[total[d] for d in range(1,n//2+1)],pair_total=sum(total.values())))
print(json.dumps(results,indent=2))
