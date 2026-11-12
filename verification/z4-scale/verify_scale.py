import sys
from pathlib import Path
HERE = str(Path(__file__).resolve().parent)
from fractions import Fraction as Q
from math import comb
import json
T=500; q=768; V=175
Delta=10**6*(T+2)*(9*q+10)
X=2*Delta**2
Km=2**20*X**257
Kh=2**40*(100*(V+1))**10*X**100
Cden=(128*Km)**2
target=min(Q(1,(64*Km)**6),Q(1,(64*Kh)**4))
cap=target.denominator.bit_length()+64

def qualifies(k):
    B=1<<(2*k)
    if B<20*Cden: return False
    ue=3*B//(100*Cden); ze=B//(3*Cden); we=B//(50*Cden*Cden)
    if ze<3: return False
    upper=Q(3,1<<min(ue,cap))/(1-Q(4,1<<min(ze,cap)))+Q(2,1<<min(we,cap))
    if upper<target: return True
    lower=Q(2,1<<we) if we<=cap else Q(0)
    if lower>=target: return False
    raise RuntimeError('indeterminate exact B comparison')

lo=1; hi=2
while not qualifies(hi): lo=hi; hi*=2
while hi-lo>1:
    mid=(lo+hi)//2
    if qualifies(mid): hi=mid
    else: lo=mid
k=hi
assert qualifies(k) and not qualifies(k-1)
B=1<<(2*k)
nQ=(2*T+1)**2*(T*V+1)**2
kappa=2*B*(9*q+nQ+2)
lam=176; M=256
N0=comb((2*lam)**2,M)
Dr=10**6*(kappa+B+(2*lam)**2+q+T+1)

# For x in [1,2], y=(x-1)/(x+1) is in [0,1/3].
# 2 sum_{j=0}^{m-1} y^(2j+1)/(2j+1) underestimates ln x;
# the remainder is at most 2*y^(2m+1)/((2m+1)*(1-y*y)).
def ln_bounds(x,m=100):
    y=(x-1)/(x+1); y2=y*y; term=y; total=Q(0)
    for j in range(m):
        total += term/(2*j+1)
        term *= y2
    low=2*total
    return low,low+2*term/((2*m+1)*(1-y2))
ln2lo,ln2hi=ln_bounds(Q(2))

def log2_bounds(n):
    e=n.bit_length()-1
    shift=max(0,e-80)
    top=n>>shift
    den=1<<(e-shift)
    xlo=Q(top,den)
    xhi=Q(top+1,den) if shift else xlo
    llo,_=ln_bounds(xlo)
    _,lhi=ln_bounds(xhi)
    return Q(e)+llo/ln2hi,Q(e)+lhi/ln2lo

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,c):return a[0]*c,a[1]*c
def const(c):return Q(c),Q(c)
terms={
 'C_over_100':log2_bounds(100*Cden),
 'memory':mul(add(const(6),log2_bounds(Km)),4),
 'history':mul(add(const(6),log2_bounds(Kh)),44),
 'rare':mul(add(add(const(26),mul(add(const(1),mul(log2_bounds(Dr),2)),513)),log2_bounds(N0+1)),16),
 'density':mul(log2_bounds(382205952),33720)
}
rare=terms['rare']
assert all(rare[0]>v[1] for name,v in terms.items() if name!='rare')
a=log2_bounds(10*Cden);b=log2_bounds(21)
rat=(a[0]-b[1],a[1]-b[0])
zlo=(rare[0]-rat[1]-3)/2
zhi=(rare[1]-rat[0]-3)/2
assert zlo.numerator//zlo.denominator==zhi.numerator//zhi.denominator
n0=zhi.numerator//zhi.denominator+1
assert n0>=k+2
assert rat[0]+2*n0+3-Q(1,1<<60)>rare[1]
assert rat[1]+2*(n0-1)+3<rare[0]

def compact(v):
    unit=1<<60
    low=(v[0]*unit).numerator//(v[0]*unit).denominator
    high=-((-v[1]*unit).numerator//(-v[1]*unit).denominator)
    return {'lowerNumerator':str(low),'upperNumerator':str(high),'denominator':str(unit)}
result={'engine':'Python exact Fraction/integer arithmetic with analytic logarithm remainder bounds','k':k,'n0':n0,'kMinimalCertified':True,'n0MinimalCertified':True,'bindingTerm':'rare','inverseThresholdLog2Bounds':{key:compact(v) for key,v in terms.items()},'log2_10Cden_over_21':compact(rat),'noHugeNoiseDenominatorConstructed':True}
Path(HERE,'scale-python.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(json.dumps(result,indent=2))
