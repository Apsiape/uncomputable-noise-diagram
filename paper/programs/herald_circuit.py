"""Fanout-two circuit computing the two outgoing energies and the calibrated leaf sign."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functools import lru_cache
from collections import Counter
from bond_circuit import Emitter,Wire,Parities,ZERO,ONE,COPY,NOT,XOR,AND,OR
from small_ising import Encoding,horizontal,vertical
import local_machine as lm


def decode_word(e,g,chunk):
    negative,*word=chunk
    rep=word[:g.pivot]+[e.zero]+word[g.pivot:]
    hidden=Parities(e,rep[-20:])
    observed=e.majority(*(hidden.get(g.model.table.head(s,0)) for s in (lm.MASS,lm.B,lm.D)))
    toggle=e.op(XOR,negative,observed)
    return [e.op(XOR,x,toggle) if (g.flip >> i)&1 else x for i,x in enumerate(rep)]


def ge(e,bits,k):
    value=e.one
    for i,x in enumerate(bits):
        value=e.op(AND if (k >> i)&1 else OR,value,x)
    return value


def select(e,c,a,b):
    return e.op(XOR,b,e.op(AND,c,e.op(XOR,a,b)))


@lru_cache(maxsize=1)
def encoding():
    return Encoding()


class Raw(Emitter):
    def __init__(self,n):
        self.ops=[]
        super().__init__(n)

    def emit(self,f,a,b):
        index=len(self.ops)
        self.ops.append((f,a,b))
        self.count=index+1
        return index

    def acquire(self,w):
        return w.end


def inputs(f,a,b):
    if f in (ZERO,ONE):
        return ()
    return (a,) if f in (COPY,NOT) else (a,b)


@lru_cache(maxsize=1)
def network():
    g=encoding()
    e=Raw(3*g.p+8)
    assert e.count==2
    x=[Wire(e.emit(COPY,b.end,b.end),b.value) for b in e.inputs]
    words=[decode_word(e,g,x[i*g.p:(i+1)*g.p]) for i in range(3)]
    east=horizontal(e,g,words[0],words[1])
    north=vertical(e,g,words[0],words[2])
    slot=x[-8:-1]
    cal=x[-1]
    zero=ge(e,slot,64)
    one=ge(e,slot,40)
    two=select(e,ge(e,slot,18),ge(e,slot,25),cal)
    output=select(e,east,select(e,north,two,one),select(e,north,one,zero))
    assert output.end==e.count-1
    # Intern equal Boolean nodes and remove unused arithmetic carry outputs before making copies.
    clean=[]
    remap={}
    intern={}
    for old,(f,a,b) in enumerate(e.ops):
        a,b=remap.get(a,a),remap.get(b,b)
        if f in (XOR,AND,OR) and a>b:
            a,b=b,a
        alias=None
        if f in (XOR,AND,OR) and a==b:
            alias=0 if f==XOR else a
        elif f in (AND,OR,XOR) and a in (0,1):
            if f==AND:
                alias=0 if a==0 else b
            elif f==OR:
                alias=b if a==0 else 1
            elif a==0:
                alias=b
            else:
                f,a,b=NOT,b,b
        if f==NOT and a in (0,1):
            alias=1-a
        elif f==NOT and a>=0 and clean[a][0]==NOT:
            alias=clean[a][1]
        key=f,a,b
        if alias is not None:
            remap[old]=alias
        elif key in intern:
            remap[old]=intern[key]
        else:
            remap[old]=intern[key]=len(clean)
            clean.append(key)
    root=remap[len(e.ops)-1]
    clean.append((COPY,root,root))
    live={len(clean)-1}
    for i in range(len(clean)-1,-1,-1):
        f,a,b=clean[i]
        if f==COPY and a<0:
            live.add(i)
        if i in live:
            live.update(j for j in inputs(f,a,b) if j>=0)
    ordered=[(i,clean[i]) for i in sorted(live)]
    demand=Counter(src for _,(f,a,b) in ordered for src in inputs(f,a,b))
    ops=[]
    current={}
    uses=Counter()
    for old,(f,a,b) in ordered:
        args=[]
        for src in inputs(f,a,b):
            idx=current.get(src,src)
            if uses[idx]==1 and demand[src]>1:
                idx=len(ops)
                ops.append((COPY,current.get(src,src),current.get(src,src)))
                current[src]=idx
            args.append(idx)
            uses[idx]+=1
            demand[src]-=1
        current[old]=len(ops)
        if not args:
            args=[-1,-1]
        elif len(args)==1:
            args.append(args[0])
        ops.append((f,*args))
    consumers={}
    for i,(f,a,b) in enumerate(ops):
        for src in set(inputs(f,a,b)):
            consumers.setdefault(src,[]).append(i)
    assert max(map(len,consumers.values()))<=2
    assert all(len(consumers[-1-i])==1 for i in range(3*g.p+8))
    return ops,consumers


def compile_circuit(patterns=(),wanted=None,consumer=None):
    ops,consumers=network()
    if wanted is not None:
        return ops[wanted]
    if consumer is not None:
        return tuple(consumers.get(consumer,()))
    universe=(1 << len(patterns))-1
    values={-1-i:sum(((x >> i)&1) << k for k,x in enumerate(patterns)) for i in range(3*encoding().p+8)}
    for i,(f,a,b) in enumerate(ops):
        left,right=values.get(a,0),values.get(b,0)
        v={ZERO:0,ONE:universe,COPY:left,NOT:universe^left,XOR:left^right,AND:left&right,OR:left|right}[f]
        values[i]=v
    return len(ops),dict(Counter(f for f,_,_ in ops)),values[len(ops)-1]


@lru_cache(maxsize=1)
def gate_count():
    return len(network()[0])


@lru_cache(maxsize=64)
def gate(i):
    if i<0:
        raise ValueError("negative gate")
    return compile_circuit(wanted=i)


@lru_cache(maxsize=32)
def users(i):
    return compile_circuit(consumer=i)

