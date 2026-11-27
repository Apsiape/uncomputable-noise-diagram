"""Direct incident-edge lookup on the signed degree-three Ising graph."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def shifted(vertex,origin):
    (x,y),*rest=vertex
    return ((origin[0]+x,origin[1]+y),*rest)


def core_indices(role,i,*extra):
    if role=="hub":
        return i,4+2*i,5+2*i
    if role=="child":
        g,=extra
        return 4+2*i+g,12+4*i+2*g,13+4*i+2*g
    if role=="center":
        k,=extra
        return 28+i,12+8*k+i,16+8*k+i
    raise ValueError("invalid parity spin")


def mux_parent(node):
    parent,side=divmod(node,2)
    return [("mux",parent,64*side+1),("mux",parent,64*side+33)]


def avg_parent(leaf,node):
    parent,side=divmod(node,2)
    return [("average",leaf,parent,2*side),("average",leaf,parent,2*side+1)]


def candidates(g,v):
    (cx,cy),kind,*a=v
    origin=(cx,cy)
    if kind in ("spin","invariant","reference"):
        for role,(dx,dy) in enumerate(((0,0),(1,0),(0,1))):
            home=origin if kind=="reference" else (cx-dx,cy-dy)
            bit,rail=((g.p-1-a[0],a[1]) if kind=="invariant" else (0,int(kind=="reference")))
            yield home,("control",role*g.p+bit,rail,0)
        return
    out=[]
    if kind=="master":
        out=[("close",),("master",0)]
    elif kind in ("control","broadcast"):
        if kind=="control":
            i,r,where,k=a
            _,_,stem,height=g.control(i,r)
            prefix=("control",i,r)
        else:
            where,k=a
            _,_,stem,height=g.master()
            prefix=("master",)
        n=1 if where=="stem" else k
        index=k-1 if where=="stem" else stem+n-2
        out.append((*prefix,index))
        if where=="stem" and k<stem:
            out.append((*prefix,k))
        elif n < 1 << height:
            out.extend([(*prefix,stem+2*n-2),(*prefix,stem+2*n-1)])
        elif kind=="control":
            out.extend([("mux",n,34+r),("mux",n,98+r)])
        else:
            leaf,slot=divmod(n-(1 << height),128)
            if slot<18 and g.energy(leaf)==2:
                out.append(("cal",leaf,slot,"plain",0))
            else:
                out.extend(avg_parent(leaf,128+slot))
    elif kind=="mux":
        n,where,*q=a
        if where=="parity":
            block,*core=q
            ids=[32*block+i for i in core_indices(*core)]
        elif where=="arm":
            s,=q
            ids=[64*s,64*s+32,128+s]
        elif where=="join":
            ids=[128,129,130]
        elif where=="out":
            ids=[130]
            out.extend([("close",)] if n==1 else mux_parent(n))
        elif where=="constant":
            j,=q
            ids=[131+i for i in (j-1,j) if 0<=i<2*g.m]
            if j in (0,2*g.m):
                ids.extend([2+int(j!=0),66+int(j!=0)])
        else:
            raise ValueError("invalid mux vertex")
        out.extend(("mux",n,i) for i in ids)
    elif kind=="average":
        leaf,n,where=a
        ids={"sum":(0,2,4),"dummy":(1,3),"out":(4,)}[where]
        out.extend(("average",leaf,n,i) for i in ids)
        if where=="out":
            out.extend(mux_parent((1 << g.m)+leaf) if n==1 else avg_parent(leaf,n))
    elif kind=="cal":
        leaf,slot,loc,j,*rest=a
        prefix=("cal",leaf,slot)
        if loc=="plain":
            out.append((*prefix,"plain",j-1))
            if j<g.ordinary:
                out.append((*prefix,"plain",j))
            else:
                out.extend([(*prefix,"parity",0,0),(*prefix,"parity",0,32)])
        elif loc=="pair":
            where,*q=rest
            if where=="core":
                block,*core=q
                ids=[32*block+i for i in core_indices(*core)]
            elif where=="pad":
                ids=[32*q[0]+2,32*q[0]+3]
            elif where=="join":
                ids=[1,33,64]
            elif where=="out":
                ids=[64]
                if j+1<g.m:
                    out.extend([(*prefix,"parity",j+1,0),(*prefix,"parity",j+1,32)])
                else:
                    out.extend([(*prefix,"average",0,0),(*prefix,"average",0,1)])
            else:
                raise ValueError("invalid calibration pair vertex")
            out.extend((*prefix,"parity",j,i) for i in ids)
        elif loc=="average":
            where,*q=rest
            if where=="input":
                ids=[q[0],2+2*q[0],3+2*q[0]]
            else:
                ids={"sum":(2,4,6),"dummy":(3,5),"out":(6,)}[where]
            out.extend((*prefix,"average",j,i) for i in ids)
            if where=="out":
                if j<6:
                    out.extend([(*prefix,"average",j+1,0),(*prefix,"average",j+1,1)])
                else:
                    out.extend(avg_parent(leaf,128+slot))
        else:
            raise ValueError("invalid calibration vertex")
    else:
        raise ValueError("unknown vertex")
    yield from ((origin,address) for address in out)


def incident(g,vertex):
    target=(tuple(vertex[0]),*vertex[1:])
    result=[]
    for origin,address in candidates(g,target):
        a,b,sign=g.edge(*address)
        a,b=shifted(a,origin),shifted(b,origin)
        if target not in (a,b):
            raise ValueError(("invalid incident edge",target,origin,address))
        result.append(((origin,*address),b if target==a else a,sign))
    return result

