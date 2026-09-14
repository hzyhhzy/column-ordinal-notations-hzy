"""Independent bounded recursive-tuple oracle for the fixed SPD rule only.

No production or research module imports. The production implementation uses
interned iterative arenas; this small oracle uses direct tuples and recursion.
"""
from functools import cmp_to_key
from time import monotonic

START = monotonic()
events = 0
Z = (0,0,None,(),0)
A = (3,0,None,(),0)
B = (4,0,None,(),0)


def tick():
    global events
    events += 1
    if events>10000000 or monotonic()-START>40:
        raise TimeoutError('Tuple reference 40-second / 10m-event bound')


def sign(a,b):
    return (a>b)-(a<b)


class Terms:
    def __init__(self):
        self.keep,self.cache,self.instances = [Z,A,B],{},{}
        self.slots = 0

    def keep_node(self,t):
        tick()
        if len(self.keep)>=50000:
            raise OverflowError('Tuple oracle node bound')
        self.keep.append(t)
        return t

    def atom(self,n):
        return self.keep_node((1,n,None,(),0))

    def node(self,h,args):
        args = tuple(args)
        self.slots += len(args)
        if self.slots>200000:
            raise OverflowError('Tuple oracle argument-slot bound')
        return self.keep_node((2,0,h,args,max(h[4]+1,max((a[4] for a in args),default=0))))

    def compare(self,a,b):
        tick()
        if a is b:
            return 0
        if a[4]!=b[4]:
            return sign(a[4],b[4])
        if a[0]!=2 or b[0]!=2:
            return sign(a[0],b[0]) or sign(a[1],b[1])
        key=id(a),id(b)
        if key in self.cache:
            return self.cache[key]
        if any(self.compare(c,b)>=0 for c in a[3]):
            result=1
        elif any(self.compare(c,a)>=0 for c in b[3]):
            result=-1
        else:
            result=self.compare(a[2],b[2]) or sign(len(a[3]),len(b[3]))
            if not result:
                for x,y in zip(a[3],b[3]):
                    result=self.compare(x,y)
                    if result:
                        break
        if len(self.cache)>=60000:
            raise OverflowError('Tuple oracle comparison-cache bound')
        self.cache[key]=result
        self.cache[id(b),id(a)]=-result
        return result

    def at(self,t,p):
        tick()
        key=id(t),p
        if key in self.instances:
            return self.instances[key]
        if t[0]==3:
            result=self.atom(p)
        elif t[0]==2:
            result=self.node(self.at(t[2],p),(self.at(c,p) for c in t[3]))
        else:
            result=t
        if len(self.instances)>=50000:
            raise OverflowError('Tuple oracle context-cache bound')
        self.instances[key]=result
        return result


class Diagram:
    def __init__(self):
        self.terms,self.heads,self.columns=Terms(),[],[]
        self.rows=0

    def value(self,h,p):
        return self.terms.at(self.heads[h],p)

    def head_key(self,h,k,p):
        return self.terms.compare(self.value(h,p),self.value(k,p)) or sign(h,k)

    def pair(self,h,s,k,t,p):
        return self.head_key(h,k,p) or self.head_key(s,t,p)

    def profile(self,a,b):
        h,p,s,q=a
        k,r,t,v=b
        return (self.terms.compare(self.value(h,p),self.value(k,r)) or sign(h,k)
                or self.terms.compare(self.value(s,p),self.value(t,r)) or sign(s,t)
                or sign(q,v))

    def edge(self,a,b):
        return sign(a[1],b[1]) or self.profile(a,b)

    def append(self,rows):
        tick()
        j=len(self.columns)
        if j>=80:
            raise OverflowError('Tuple oracle 80-column bound')
        maximum={}
        for h,p,s,q in rows:
            tick()
            if not(0<=h<=p<j and 0<=s<=p and (0<=q<=p or q in (j,j+1))):
                raise ValueError('Illegal oracle row')
            maximum[h,p,s]=max(q,maximum.get((h,p,s),-1))
        col=tuple(sorted(((*key,q) for key,q in maximum.items()),
                         key=cmp_to_key(self.edge),reverse=True))
        self.rows+=len(col)
        if self.rows>60000:
            raise OverflowError('Tuple oracle 60000-row bound')
        self.columns.append(col)
        visible=[e for e in col if e[3]!=j+1]
        if not visible:
            self.heads.append(Z)
            return
        hstar=max((e[0] for e in visible),key=cmp_to_key(lambda h,k:
            self.terms.compare(self.heads[h],self.heads[k]) or sign(h,k)))
        args=[]
        for h,p,s,q in sorted(visible,key=lambda e:(e[1],e[2],e[0],e[3]),reverse=True):
            if h==hstar:
                args.extend((self.heads[s],A if q==p else B if q==j else self.terms.atom(q)))
        self.heads.append(self.terms.node(self.heads[hstar],args))

    def control(self):
        return max(self.columns[-1],key=cmp_to_key(lambda a,b:
            self.profile(a,b) or sign(a[1],b[1])))


def read(g):
    d=Diagram()
    for col in g:
        d.append(col)
    return d


def count(d,j):
    result=1
    for p in {e[1] for e in d.columns[j]}:
        h,_,s,q=max((e for e in d.columns[j] if e[1]==p),key=cmp_to_key(d.profile))
        ranked=sorted(range(p+1),key=cmp_to_key(lambda h,k:d.head_key(h,k,p)))
        digit=p+3 if q==j+1 else p+2 if q==j else q+1
        result+=digit+(p+3)*((p+1)*ranked.index(h)+ranked.index(s))
    return result


def moved(row,oldchild,newchild,f):
    h,p,s,q=row
    return f(h),f(p),f(s),newchild+1 if q==oldchild+1 else newchild if q==oldchild else f(q)


def fs(g,n):
    old=read(g)
    if not g:
        return ()
    if n==0 or not old.columns[-1]:
        return tuple(old.columns[:-1])
    chosen=old.control()
    h,cut,_,_=chosen
    x=len(g)-1
    out=read(old.columns[:-1])
    shift=0
    for block in range(n):
        tick()
        f=lambda i:i if i<cut else i+shift
        child=x+shift
        hh,pp,ss,qq=moved(chosen,x,child,f)
        rows=[moved(e,x,child,f) for e in old.columns[-1] if e!=chosen]
        if qq:
            rows.append((hh,pp,ss,child if qq==child+1 else pp if qq==child else qq-1))
        rows.extend((k,pp,t,child+1) for k in range(pp+1) for t in range(pp+1)
                    if out.pair(k,t,hh,ss,pp)<0)
        if block:
            rows.extend(moved(e,cut,child,f) for e in old.columns[cut]
                        if e[3]==cut+1 or e[0]==h)
        out.append(rows)
        uh,ui=out.value(hh,child),child if hh==pp else hh
        us,uj=out.value(ss,child),child if ss==pp else ss
        bridge=[]
        for k in range(child+1):
            for t in range(child+1):
                value=(out.terms.compare(out.value(k,child),uh) or sign(k,ui)
                       or out.terms.compare(out.value(t,child),us) or sign(t,uj))
                if value<0:
                    bridge.append((k,child,t,child+2))
        if bridge:
            out.append(bridge)
        shift+=x-cut+1+bool(bridge)
        f=lambda i:i if i<cut else i+shift
        for j in range(cut,x):
            out.append(moved(e,j,f(j),f) for e in old.columns[j])
    return tuple(out.columns)


def graph_compare(a,b):
    left,right=read(a),read(b)
    for xs,ys in zip(left.columns,right.columns):
        for x,y in zip(xs,ys):
            result=left.edge(x,y)
            if result:
                return result
        if len(xs)!=len(ys):
            return sign(len(xs),len(ys))
    return sign(len(a),len(b))
