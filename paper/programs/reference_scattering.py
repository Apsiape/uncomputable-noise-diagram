"""Independent register assembly and Walsh reference for the binary-wave bond table.

Only Python standard-library modules are used. The verifier
can import reference_terms() without reading any data produced by the model.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from collections import Counter
from itertools import product
import json
from pathlib import Path

# Names are local to this independent description. Register ordinal determines
# distance from the home cell in the seventeen-track unary tape.
REG = "stage todo code num den cut heat length dilute fuel pc x y list skip op tmp".split()
ASSEMBLY = """
:wave
+ dilute
:mass
:choose
fork later begin
:later
+ stage
go choose
:begin
+ num num den den den den
copy stage todo
:next
- todo simulate finish
:simulate
quad num
quad den
copy stage fuel
empty pc
empty x
empty y
:step
copy code list
copy pc skip
:fetch
- list readcell halted
:readcell
+ list
empty op
:peel
half list factor popped
:factor
+ op
go peel
:popped
- skip fetch ready
:ready
- fuel exec done
:exec
half op even odd
:even
half op ix dx
:odd
half op iy dy
:ix
+ x
go advance
:dx
- x take advance
:iy
+ y
go advance
:dy
- y take advance
:advance
+ pc
go step
:take
empty pc
empty op pc
go step
:halted
+ num
:done
+ code
go next
:finish
copy den length
copy den heat
empty heat length
- dilute extra cutmarks
:extra
- stage extend cutmarks
:extend
copy den heat
empty heat length
go extra
:cutmarks
copy length cut
copy length heat
:subtract
- num minus subheat
:minus
- cut subtract invalid
:subheat
- den minusheat shorten
:minusheat
- heat subheat invalid
:shorten
- cut cs invalid
:cs
- heat hs invalid
:hs
- length cleanup invalid
:cleanup
clean
install
:invalid
dead
"""


def assemble():
    code, labels, drains = [], {}, {}
    def inc(reg):
        code.append(("i",REG.index(reg),len(code)+1))
    def drain(reg,dest):
        base = len(code)
        drains[base] = (REG.index(reg), tuple(REG.index(d) for d in dest))
        code.append(("d",REG.index(reg),base+1,base+2+len(dest)))
        for v in dest:
            inc(v)
        code.append(("g",base))
    for line in ASSEMBLY.strip().splitlines():
        if line.startswith(":"):
            labels[line[1:]] = len(code)
            continue
        cmd,*args = line.split()
        if cmd=="+":
            for v in args:
                inc(v)
        elif cmd=="-":
            code.append(("d",REG.index(args[0]),*args[1:]))
        elif cmd in ("go","fork"):
            code.append(("g",*args))
        elif cmd=="empty":
            drain(args[0],args[1:])
        elif cmd=="quad":
            drain(args[0],["tmp"]*4)
            drain("tmp",args)
        elif cmd=="copy":
            src,dst = args
            drain(dst,[])
            drain(src,[dst,"tmp"])
            drain("tmp",[src])
        elif cmd=="half":
            reg,even,odd = args
            base = len(code)
            code.append(("d",REG.index(reg),base+1,base+4))
            code.append(("d",REG.index(reg),base+2,base+8))
            inc("tmp")
            code.append(("g",base))
            for target in (even,odd):
                drain("tmp",[reg])
                code.append(("g",target))
        elif cmd=="clean":
            for v in REG:
                if v not in ("cut","heat","length"):
                    drain(v,[])
        else:
            assert cmd in ("install","dead")
            code.append((cmd,))
    resolved = [tuple([ins[0],*[labels[a] if isinstance(a,str) else a for a in ins[1:]]]) for ins in code]
    assert len(resolved)==235 and labels["wave"]==0 and labels["mass"]==1
    return resolved, labels, drains


PROGRAM, LABELS, DRAINS = assemble()
PHASE = (0,1,2,3,4,5,5,5,8,8,8)
ORIGINAL_TRIPS = [("old",d,g,t) for d,g,t in product((-1,1),(0,1),(0,1))]
ENTRY = ORIGINAL_TRIPS[0]
B,D,W,A = ("terminal",),("direct",),("wave",),("mass",)
STAGE_DIRECT = [("ref",6)]+[("ref",i) for i in range(1,13) if i!=6]
LONG = [("long",d,g) for d,g in product((-1,1),(0,1))]
SHORT = [(tag,d) for d in (-1,1) for tag in ("wait","run")]


def stride(distance,continuation,write):
    step = 1 if distance>0 else -1
    rem = distance-step
    target = ("walk",rem,continuation) if rem else continuation
    return target,step,write


def work(state,mem):
    """Unweighted head actions for either seed and all shared program controls."""
    tag,*par = state
    if state in (W,A) and mem==0:
        yield ("pc",int(state==A)),0,5
    elif tag=="pc" and mem==5:
        op,*arg = PROGRAM[par[0]]
        if op=="g":
            for addr in arg:
                yield ("pc",addr),0,5
        if op in ("i","d"):
            yield stride(arg[0]+1,(op,*arg),5)
        if op=="install":
            yield ("mark",0,0,0),1,8
    elif tag=="walk":
        yield stride(*par,mem)
    elif tag=="origin":
        if mem==5:
            yield ("pc",par[0]),0,5
        else:
            yield state,-1,mem
    elif tag=="i" and mem in (0,1):
        yield stride(17,state,1) if mem else (("origin",par[1]),-1,1)
    elif tag=="d" and mem in (0,1):
        yield stride(17,("scan",par[0],par[1]),1) if mem else (("origin",par[2]),-1,0)
    elif tag=="scan" and mem in (0,1):
        yield stride(17,state,1) if mem else stride(-17,("clear",par[1]),0)
    elif tag=="clear" and mem==1:
        yield ("origin",par[0]),-1,0
    elif tag=="mark" and mem in (0,1):
        col,placed,present = par
        if mem:
            present |= {5:1,6:2,7:4}.get(col,0)
        if col!=16:
            yield ("mark",col+1,placed,present),1,0
        elif not present&4:
            yield ("back",),-1,4
        else:
            create = 3 & ~(placed|present)
            if create!=3:
                yield ("mark",0,placed|create,0),1,(0,2,3)[create]
    elif tag=="back":
        yield (ENTRY,0,8) if mem==8 else (state,-1,mem)
    elif tag=="erase+":
        yield (("erase-",),-1,0) if mem==4 else (state,1,0)
    elif tag=="erase-":
        yield (B,0,0) if mem==8 else (state,-1,0)


def payloads():
    # Discovery order of the original finite state alphabet is part of the
    # numerical mask convention. The eight old trip labels already exist.
    states = ORIGINAL_TRIPS+[B,D,W,A]
    seen = set(states)
    for state in states:
        discoveries = []
        if state in ORIGINAL_TRIPS:
            discoveries.append(("erase+",))
        else:
            for mem in (0,1,2,3,4,5,8):
                discoveries.extend(t for t,_,_ in work(state,mem))
        for target in discoveries:
            if target not in seen:
                states.append(target)
                seen.add(target)
    assert len(states)==5711
    reserved = {11,13}
    allstates = states+STAGE_DIRECT+LONG+SHORT
    ordinals = (k for k in range(8192) if k not in reserved)
    return dict(zip(allstates,ordinals))


def colored_write(raw,ordinary):
    return ordinary+(raw-PHASE[raw]+1)%3 if ordinary in (5,8) else ordinary


def penalty(lane):
    # Each even-position bit of lane & (lane >> 1) masks one adjacent pair.
    return 1-2*((lane & (lane>>1) & 0x1555).bit_count()%2)


STEP_M = (0,0,0,0,1,1,1,1,1,1,0,0,0)
STEP_D = (1,1,1,-1,-1,-1,1,1,1,-1,-1,-1,0)
STEP_W = (1,1,1,1,1,1,0,0,0,0,0,0,0)


def weighted(state,raw):
    mem = PHASE[raw]
    tag = state[0]
    if state==D or tag=="ref":
        tick = 0 if state==D else state[1]
        if mem!=STEP_M[tick]:
            return
        if tick in (0,6):
            yield state,0,mem,1<<(8 if tick==0 else 49)
        target = B if tick==12 else ("ref",tick+1)
        yield target,STEP_D[tick],STEP_W[tick],32
        return
    if tag not in ("old","long","wait","run"):
        for target,move,write in work(state,mem):
            terminal = target==B
            weight = (2 if (raw-8+1)%3==0 else -1) if terminal else 1
            yield target,move,write,weight
        return
    if state in ORIGINAL_TRIPS and state!=ENTRY:
        return
    if mem not in (0,2,3,4,8):
        return
    cost = 12 if mem else 0
    if mem==8 and (state==ENTRY or (tag in ("long","wait") and state[1]==-1)):
        yield ENTRY,0,8,1<<49
        yield ("erase+",),1,8,1
        yield ("long",1,0),1,8,1<<(42-cost)
        yield ("run",1),0,8,-(1<<(34-cost))
    elif tag=="long":
        _,d,bonus = state
        if mem==4:
            d,bonus = -1,1
        elif mem==2:
            bonus = int(d==1)
        yield ("long",d,bonus),d,mem,1<<(42-cost+bonus)
    elif tag=="wait":
        d = -1 if mem==3 else state[1]
        yield ("run",d),0,mem,1<<(34-cost)
    elif tag=="run":
        yield ("wait",state[1]),state[1],mem,1<<(34-cost)


def reference_terms():
    ids = payloads()
    for raw in range(1,11):
        yield raw,0,colored_write(raw,PHASE[raw]),0,1<<50
    for state,number in ids.items():
        incoming = (0,) if state in (D,W,A,B) else (-1,0,1)
        for raw in range(11):
            for target,move,write,weight in weighted(state,raw):
                new = ids[target]
                lane = 1+2*new if move else 0
                center = colored_write(raw,write) | (32+128*new if not move else 0)
                for side in incoming:
                    head = 128*number+(1<<(5+side))+raw
                    yield head,lane if move<0 else 0,center,lane if move>0 else 0,weight*penalty(lane)


def main():
    expected = Counter(reference_terms())
    root = Path(HERE)
    with (root/"binary-terms.tsv").open(encoding="ascii") as f:
        actual = Counter(tuple(map(int,line.split())) for line in f)
    if actual!=expected:
        print("Missing",list((actual-expected).items())[:8])
        print("Extra",list((expected-actual).items())[:8])
        raise ValueError("independent reference and printed table differ")
    report = {"status":"PASS","register_instructions":len(PROGRAM),"shared_payloads":5711,
              "total_payloads":len(payloads()),"scattering_options":sum(expected.values()),
              "absolute_integer_weight":sum(abs(row[-1])*n for row,n in expected.items())}
    (root/"SCATTERING-CHECK.json").write_bytes(json.dumps(report,indent=2).encode()+b"\n")
    print(json.dumps(report))


if __name__=="__main__":
    main()
