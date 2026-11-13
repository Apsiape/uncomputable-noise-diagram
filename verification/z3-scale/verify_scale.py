"""Exact rational-series certificate for the fixed Z3 recipe; no float decisions."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
from fractions import Fraction as Q
import json
sys.set_int_max_str_digits(0)

def add(a,b): return a[0]+b[0],a[1]+b[1]
def mul(a,k):
    return (a[0]*k,a[1]*k) if k>=0 else (a[1]*k,a[0]*k)
def sub(a,b): return add(a,mul(b,-1))
def divpos(a,b):
    assert a[0]>=0 and b[0]>0
    return a[0]/b[1],a[1]/b[0]
def series(p,q):
    z=Q(p,q); zz=z*z; power=z; total=Q(0); M=180
    for j in range(M):
        total+=power/(2*j+1); power*=zz
    tail=2*power/((2*M+1)*(1-zz))
    return 2*total,2*total+tail
L2=series(1,3)
def ln(n):
    e=n.bit_length()-1; scale=1<<300
    if e>300:
        low=n>>(e-300); high=low+(n!=(low<<(e-300)))
    else:
        low=high=n<<(300-e)
    lower=series(low-scale,low+scale)[0]
    upper=series(high-scale,high+scale)[1]
    return add(mul(L2,e),(lower,upper))
L10=ln(10)
def decimal(q,digits=12,upper=False):
    unit=10**digits; numerator=q.numerator*unit; denominator=q.denominator
    value=-((-numerator)//denominator) if upper else numerator//denominator
    return str(value//unit)+'.'+str(value%unit).zfill(digits)
def printed(a): return [decimal(a[0]),decimal(a[1],upper=True)]
def log2span(a): return printed(divpos(a,L2))
def log10span(a): return printed(divpos(a,L10))
D=10**6*502*(9*768+10); X=2*D*D; Km=(1<<20)*X**257
Dc=128*Km; Dc2=Dc*Dc; Dc4=Dc2*Dc2
Lkm=ln(Km); Ldc=ln(Dc)
base=10**30*502**10*769**10; Lbase=ln(base)
delta=Q(1,1<<250)
def full(k,B):
    # ln(B+1) is between ln B and ln B+1/B, exactly.
    lb=mul(L2,2*k); lb=(lb[0],lb[1]+Q(1,B))
    ld=add(Lbase,mul(lb,4))
    return add(mul(L2,20),mul(add(L2,mul(ld,2)),1<<41))
checks=[]; B=1; k=0
while True:
    k+=1; B*=4
    if B<20*Dc2: continue
    Fz=B//(3*Dc2); Fw=B//(50*Dc4); Fu=3*B//(100*Dc2)
    if Fz<=2 or Fw==0: continue
    assert Fu-Fw>=252
    # eta=2^(1-Fw)*(1+theta), 0<ln(1+theta)<2^-250.
    LetaInv=mul(L2,Fw-1); LetaInv=(LetaInv[0]-delta,LetaInv[1])
    Lfull=full(k,B)
    rhs1=mul(add(mul(L2,6),Lkm),6)
    rhs2=mul(add(mul(L2,6),Lfull),4)
    rhs=(max(rhs1[0],rhs2[0]),max(rhs1[1],rhs2[1]))
    margin=sub(LetaInv,rhs)
    if margin[0]>0: checks.append((k,margin)); break
    assert margin[1]<0, 'unresolved interval decision'
    checks=[(k,margin)]
assert k==43429 and checks[-2][0]==k-1
# Every earlier candidate was rejected by exact floors or separated intervals.
terms=[add(ln(100),mul(Ldc,2)),mul(ln(382205952),33720),
       mul(add(mul(L2,6),Lkm),4),mul(add(mul(L2,6),Lfull),44)]
assert all(terms[3][0]>t[1] for t in terms[:3])
Y=add(sub(ln(21),ln(10)),sub(terms[3],mul(Ldc,2)))
quot=divpos(Y,L2)
lo=(quot[0]-3)/2; hi=(quot[1]-3)/2
assert lo.numerator//lo.denominator==hi.numerator//hi.denominator
n0=max(k+2,lo.numerator//lo.denominator+1)
assert n0==33644133613821753975
E=2*n0+3; assert E>=252
current=sub((E*L2[0]-delta,E*L2[1]),Y)
previous=sub(mul(L2,E-2),Y)
assert current[0]>0 and previous[1]<0
rate=add(mul(L2,42),add(ln(17600000000),add(mul(L2,2*k),(Q(0),Q(176363,B)))))
# ln(B+176363) lies in [ln B, ln B+176363/B].
sval=(3*B+4*Dc2-1)//(4*Dc2)
result={'engine':'Python exact Fraction series with explicit remainder',
 'k':k,'n0':str(n0),'binding':'(64K_full)^(-44)',
 'Fw':str(Fw),'s_digits':len(str(sval)),'s_leading':str(sval)[:20],
 'log10_epsilon_reciprocal':log10span(terms[3]),
 'log10_K_full':log10span(Lfull),'log10_c_reciprocal':log10span(rate),
 'c':'1/(2^42*17600000000*(4^43429+176363))',
 'k_previous_margin_log2':log2span(mul(checks[-2][1],-1)),
 'k_margin_log2':log2span(checks[-1][1]),
 'n0_margin_log2':log2span(current),
 'n0_previous_failure_log2':log2span(mul(previous,-1)),
 'all_decisions':'CERTIFIED by exact rational interval separation',
 'earlier_k':'exhaustively rejected by exact floors or separated intervals',
 'eta_tail':'0 < ln(eta*2^(Fw-1)) < 2^-250; no enormous powers constructed'}
text=json.dumps(result,indent=2)+'\n'
with open(os.path.join(HERE,'scale-python.json'),'w',encoding='utf-8') as f:f.write(text)
with open(os.path.join(HERE,'scale-python.out.txt'),'w',encoding='utf-8') as f:f.write(text)
print(text,end='')
