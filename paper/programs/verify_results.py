"""Exact supplementary identities and fixed object digests for the manuscript."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from cubic_parity import weights, certificate as core_certificate
import json


def main():
    expected = {
        'herald-gates.json': 'a069b637730ec10e48d7402608e929f1e71c8b558164388cdd07047a57eff2cc',
        'binary-terms.tsv': 'd59dd512ce13ddbd6ab180b72634f277fdccc22b53861ff65c0060483aa84c2d',
    }
    for name, digest in expected.items():
        assert sha256((HERE/name).read_bytes()).hexdigest() == digest, name
    certificate = json.loads((HERE/'CIRCUIT-CERTIFICATE.json').read_text())
    assert certificate['verdict'] == 'PASS'
    assert certificate['gate_sha256'] == expected['herald-gates.json']
    assert certificate['terms_sha256'] == expected['binary-terms.tsv']
    assert (F(33,32)**15-1) < 1
    assert 2*10**330 < 1024*2**1088
    assert 33293550733133931 < 2**56
    positive=weights((1,1,1,1))
    negative=weights((-1,1,1,1))
    assert sum(positive)==sum(negative)==2**20
    assert next(i for i,c in enumerate(positive) if c)==5
    assert next(i for i,c in enumerate(negative) if c)==4
    derivative=core_certificate(positive,negative)
    assert min(derivative)>=0 and derivative[13]>0 and derivative[54]>0
    for terminals in product((-1,1),repeat=4):
        parity=terminals[0]*terminals[1]*terminals[2]*terminals[3]
        assert weights(terminals)==(positive if parity==1 else negative)
    # Exact rational composition of the stage-start recipe, at test points
    # on either side of a component and at its endpoints.
    for z in (F(1,5),F(1,3),F(1,2),F(2,3),F(4,5)):
        for j in (1,2,3):
            b,v,u = F(1),F(0),F(0)
            b,v,u = b,b,F(0)
            for q,p in ((3,1),(3,2)):
                u=F(0)
                for _ in range(q):
                    u += z*v
                for _ in range(p):
                    u -= v
                v,u=u,F(0)
            for _ in range(j*j):
                v *= 2
            v += b
            assert (b,v,u) == (1,1+2**(j*j)*(3*z-1)*(3*z-2),0)
    # Coefficient form of the negative-trip factorization, independent of roots.
    for length in (2,3,7,19):
        rho=F(99,100)
        a=[F(1)]+[-(1-rho)*rho**(i-1) for i in range(1,length)]
        out=[F(0)]*(length+1)
        for i,x in enumerate(a):
            out[i] += x
            out[i+1] -= rho*x
        assert out == [F(1),F(-1)]+[F(0)]*(length-2)+[rho**(length-1)*(1-rho)]
    print('PASS: object digests, parity core, stage-start recipe, selector, return factorization, finite-lag estimate')


if __name__ == '__main__':
    main()
