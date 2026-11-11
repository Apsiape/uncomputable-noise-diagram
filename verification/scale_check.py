"""Recompute Section 9 / PARAMETERS with exact integers and Decimal logarithms.
No alphabet or enormous rate denominator is constructed.
Run: python -B scale_check.py (from this directory; writes scale-output.json and scale-output.txt)
"""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
from decimal import Decimal as D, localcontext
from math import comb
import json

def calculate(precision):
    with localcontext() as ctx:
        ctx.prec=precision
        log2=D(2).log10(); log4=2*log2
        T=500; K=16**4; q=5*K; M=3*K; lam=176; V=175
        delta=10**6*(T+2)*(9*q+10)
        kmem=2**20*(2*delta**2)**257
        khist=2**40*(100*(V+1))**10*(2*delta**2)**100
        cden=(128*kmem)**2
        targetden=max((64*kmem)**6,(64*khist)**4)
        # eta >= 2^(1-w). For passing, u>=w+4 and z>=3 imply
        # eta <= 6*2^(-u)+2*2^(-w) < 4*2^(-w).
        # Compare powers without constructing 2 to an enormous exponent.
        def pow2ge(e,n): return e>=n.bit_length() or (e==n.bit_length()-1 and n==(1<<e))
        def test(k):
            B=1<<(2*k)
            if B<20*cden: return False,'B<20/C',None
            z=B//(3*cden)
            if z<=2: return False,'4*z_B>=1',None
            w=B//cden2; u=(3*B)//(100*cden)
            if u>=w+4 and w-2>=targetden.bit_length():
                return True,'eta<4*2^-w<target',(w,u,z)
            if w<(2*targetden).bit_length():
                return False,'eta>=2^(1-w)>=target',(w,u,z)
            raise AssertionError('bounds inconclusive')
        cden2=50*cden*cden
        low=1; high=2
        while not test(high)[0]: low=high; high*=2
        while high-low>1:
            mid=(low+high)//2
            if test(mid)[0]: high=mid
            else: low=mid
        k=high
        ok,cert,parts=test(k);prev=test(k-1)
        assert ok and not prev[0]
        B=1<<(2*k);nA=9*q;nQ=(2*T+1)**2*(T*(160+16-1)+1)**4
        kap=2*B*(nA+nQ+2)
        Nbox=(2*lam)**4
        dr=10**6*(kap+B+Nbox+q+T+1)
        lm=D(kmem).log10();lh=D(khist).log10();lc=-D(cden).log10()
        lr=20*log2+513*(log2+2*D(dr).log10())
        # Stirling's alternating expansion through n^-9.
        # At n>=196608 its next-term remainder < 2e-61 in natural logs.
        pi=D('3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679')
        def lnfact(n):
            n=D(n)
            return (n+D('.5'))*n.ln()-n+(2*pi).ln()/2+1/(12*n)-1/(360*n**3)+1/(1260*n**5)-1/(1680*n**7)+1/(1188*n**9)
        lq=(lnfact(Nbox)-lnfact(M)-lnfact(Nbox-M))/D(10).ln()
        # Positive control: independently known exact small binomial.
        assert comb(40,12)==5586853480
        control=(lnfact(400)-lnfact(120)-lnfact(280))/D(10).ln()
        exact_control=D(comb(400,120)).log10()
        assert abs(control-exact_control)<D('1e-20')
        exponents={
            'C/100':2-lc,
            '(64*K_mem)^-4':4*(6*log2+lm),
            '(64*K_hist)^-44':44*(6*log2+lh),
            '[64*K_rare*(N_0+1)]^-16':16*(6*log2+lr+lq)
        }
        dominant=max(exponents,key=exponents.get);ep=exponents[dominant]
        # N_0+1 changes log10 N_0 by less than 10^(-1e6).
        # Hence the last exponent has error <1e-54.
        crossing=(ep+(D('1.05').log10()+lc))/log4
        n0=max(k+2,int(crossing.to_integral_value(rounding='ROUND_FLOOR')))
        def upperlog(n0):
            # ell=2*4^(n0+1)-1. The omitted log correction is
            # positive and <1e-50 at these n0, verified below.
            return D('1.05').log10()+lc-(n0+1)*log4
        assert n0>100 and upperlog(n0)+ep < -D('.001')
        assert upperlog(n0-1)+ep > D('.001')
        up1=upperlog(n0);lo1=up1-D('1.05').log10()
        # len I1 = C/(10 ell), i.e. upper/21.
        width1=up1-D(21).log10()
        assert up1 < -D(500000000)
        # Helper alphabet alone has 100^B letters.
        # log10(log10(100^B)) = log10(2B).
        doublelog=log2+2*k*log2
        assert doublelog>31539
        return dict(precision=precision,k=k,n0=n0,
            log10_C=str(lc),log10_B=str(2*k*log2),log10_kappa=str(D(kap).log10()),
            log10_Delta_rare=str(D(dr).log10()),log10_K_rare=str(lr),
            log10_N_0=str(lq),epsilon_star_negative_log10=str(ep),
            epsilon_star_terms_negative_log10={s:str(x) for s,x in exponents.items()},
            dominant_term=dominant,
            log10_I1_lower=str(lo1),log10_I1_upper=str(up1),log10_I1_width=str(width1),
            I_n_exact='(2*C/(2*4^(n+n0)-1), 21*C/(10*(2*4^(n+n0)-1)))',
            log10_I_n_shift='subtract (n-1)*log10(4), with correction <1e-50 for each endpoint',
            helper_alphabet_double_log10=str(doublelog),
            B_search_pass_certificate=cert,
            B_search_pass_w=parts[0],B_search_previous=prev[1],B_search_previous_w=prev[2][0],
            positive_control={'comb(40,12)':5586853480,'log_binomial_control_error':str(abs(control-exact_control))},
            error_statement='Reported production logs rounded to 40 decimals have absolute error <1e-39; log N_0 uses Stirling remainder <2e-61, and log(N_0+1)-log(N_0)<10^(-1e6). Integer searches certified by the stated bounds.')
a=calculate(80);b=calculate(100)
assert (a['k'],a['n0'])==(b['k'],b['n0'])
for key in ('log10_C','log10_B','log10_N_0','epsilon_star_negative_log10','log10_I1_upper'):
    assert abs(D(a[key])-D(b[key]))<D('1e-50')
def trim(v):
    if isinstance(v,str):
        try: return format(D(v),'.40f') if len(v)>50 and not any(c.isalpha() and c not in 'eE' for c in v) else v
        except: return v
    if isinstance(v,dict): return {k:trim(x) for k,x in v.items()}
    return v
b=trim(b);b['precision_agreement']='80 and 100 decimal digits agree to absolute error <1e-50.'
(HERE/'scale-output.json').write_text(json.dumps(b,indent=2)+'\n',encoding='utf-8')
text=json.dumps(b,indent=2)+'\nPASS: every window below 10^(-500000000); alphabet > 10^(10^31539).\n'
(HERE/'scale-output.txt').write_text(text,encoding='utf-8')
print(text)

