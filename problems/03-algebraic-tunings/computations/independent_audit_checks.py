"""Independent integer-only unit-step exhaustive check. Not a nonunit search."""
from math import isqrt
import json, resource
resource.setrlimit(resource.RLIMIT_CPU, (20,20))
resource.setrlimit(resource.RLIMIT_AS, (1024**3,1024**3))

def longest_run(B,m):
    lo=-((m+isqrt(5*m*m))//2)
    hi=(isqrt(5*m*m+4*B)-m)//2
    D=5*m*m-4*B
    if D<=0:return max(0,hi-lo+1)
    r=isqrt(D-1) # N<-B iff |2b+m|<=r
    badlo=max(lo,-((m+r)//2))
    badhi=min(hi,(r-m)//2)
    if badlo>badhi:return max(0,hi-lo+1)
    return max(0,badlo-lo,hi-badhi)

# For m>=B+1, both continuous allowed components have width<1:
# inner width < 2B/(sqrt(5)m)<1; outer width <= B/sqrt(5m²/4-B)<1.
# For m<=0, N(x)>=x², so at most floor(sqrt(B))+1 terms.
checks=[]
for B in range(64,2049):
    M=isqrt((4*B+3)//5)
    conjectured=(isqrt(5*M*M+4*B)-M)//2+(M+isqrt(5*M*M))//2+1
    best=max(longest_run(B,m) for m in range(1,B+1))
    assert best==conjectured,(B,M,best,conjectured)
    assert isqrt(B)+1<best
    if B in [64,65,79,80,100,1000,2048]:
        checks.append({'B':B,'M':M,'length':best,'maximizing_m':[m for m in range(1,B+1) if longest_run(B,m)==best]})
print(json.dumps({'checked_B':'64..2048','scope':'all integer m for normalized unit-step progressions, with analytic tail bounds','samples':checks},indent=2))
