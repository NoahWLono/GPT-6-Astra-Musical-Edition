"""Integer-only checks of the explicit construction. Not a global-search proof."""
from math import isqrt
import json,resource
resource.setrlimit(resource.RLIMIT_CPU,(25,25))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
def positive(m,b):
    # 2*(m*phi+b) = m+2*b + m*sqrt(5)
    A=m+2*b
    if m==0:return A>0
    if m>0:return A>=0 or 5*m*m>A*A
    return A>0 and A*A>5*m*m

def norm(m,b):return b*b+m*b-m*m

def explicit(B):
    M=isqrt((4*B+3)//5)
    lo=-((M+isqrt(5*M*M))//2)
    hi=(isqrt(5*M*M+4*B)-M)//2
    return M,lo,hi,hi-lo+1
checks=[]
for B in range(1,10001):
    m,lo,hi,L=explicit(B)
    assert (5*m*m)//4<=B<(5*(m+1)*(m+1))//4
    assert positive(m,lo) and not positive(m,lo-1)
    assert abs(norm(m,lo))<=B and abs(norm(m,hi))<=B
    assert norm(m,hi+1)>B
    assert (5*m*m)//4<=B # minimum norm bound certifies interior
    if B in (1,5,20,64,100,1000,10000):checks.append(dict(B=B,m=m,b_min=lo,b_max=hi,length=L))
print(json.dumps(dict(checked_B='1..10000',samples=checks),indent=2))
