#!/usr/bin/env python3
"""Traverse actual Lean NDJSON proof expressions, never cached axiom summaries.

This checks inventory, dependency closure and a name allowlist. It does NOT type
check proof terms. Run nanoda or a fresh Lean kernel replay for type checking.
All expression references are stored in compact arrays to bound Python overhead.
"""
from array import array
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import sys

TARGETS = [
    'CubeSections.maximalSectionVolume',
    'CubeSections.balancedSectionAttains',
    'CubeSections.maximalSectionVolume_eq_iff',
    'CubeSections.maximalSections_main',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
KINDS = ['bvar','sort','const','app','lam','forallE','letE','proj','natVal','strVal','mdata']


class ExportGraph:
    def __init__(self):
        self.names = ['']
        self.levels = [('zero',None)]
        self.kinds = bytearray()
        self.a, self.b, self.c = array('i'), array('i'), array('i')
        self.const_us = {}
        self.literal_values = {}
        self.decls = {}
        self.metadata = None
        self.lines = 0

    def add_decl(self,kind,d,members=()):
        name = d['name']
        if name in self.decls:
            raise ValueError(f'Duplicate declaration: {self.names[name]}')
        roots = [d['type']]
        if kind in ('thm','def','opaque'):
            roots.append(d['value'])
        roots += [r['rhs'] for r in d.get('rules',[])]
        self.decls[name] = {'kind':kind,'roots':roots,'members':tuple(members),
                           'unsafe':d.get('isUnsafe',False) or d.get('safety') == 'unsafe',
                           'partial':d.get('safety') == 'partial',
                           'record':d}

    def load(self,path):
        with path.open() as f:
            for line_number,line in enumerate(f,1):
                self.lines = line_number
                obj = json.loads(line)
                if 'meta' in obj:
                    if line_number != 1 or self.metadata is not None:
                        raise ValueError('Metadata outside the first line')
                    self.metadata = obj['meta']
                elif 'in' in obj:
                    if obj['in'] != len(self.names):
                        raise ValueError('Nondense or duplicate name index')
                    v = obj.get('str',obj.get('num'))
                    pre = self.names[v['pre']]
                    suffix = v.get('str',str(v.get('i')))
                    self.names.append((pre+'.' if pre else '')+suffix)
                elif 'il' in obj:
                    if obj['il'] != len(self.levels):
                        raise ValueError('Nondense or duplicate universe index')
                    keys = set(obj)-{'il'}
                    if len(keys) != 1:
                        raise ValueError('Invalid universe record')
                    k = keys.pop()
                    self.levels.append((k,obj[k]))
                elif 'ie' in obj:
                    i = obj['ie']
                    if i != len(self.kinds):
                        raise ValueError('Nondense or duplicate expression index')
                    keys = set(obj)-{'ie'}
                    if len(keys) != 1:
                        raise ValueError('Invalid expression record')
                    k = keys.pop(); v = obj[k]
                    a=b=c=-1
                    if k in ('bvar','sort'): a=v
                    elif k == 'const':
                        a=v['name']
                        if v['us']: self.const_us[i]=v['us']
                    elif k == 'app': a,b=v['fn'],v['arg']
                    elif k in ('lam','forallE'): a,b,c=v['type'],v['body'],v['name']
                    elif k == 'letE': a,b,c=v['type'],v['value'],v['body']
                    elif k == 'proj': a,b,c=v['typeName'],v['idx'],v['struct']
                    elif k in ('natVal','strVal'): self.literal_values[i]=v
                    elif k == 'mdata': a=v['expr']
                    else: raise ValueError(f'Unknown expression tag {k}')
                    self.kinds.append(KINDS.index(k));self.a.append(a);self.b.append(b);self.c.append(c)
                elif 'inductive' in obj:
                    d=obj['inductive']
                    all_members=[v['name'] for group in ('types','ctors','recs') for v in d[group]]
                    for group,kind in [('types','induct'),('ctors','ctor'),('recs','rec')]:
                        for v in d[group]: self.add_decl(kind,v,all_members)
                else:
                    if len(obj) != 1: raise ValueError('Invalid declaration record')
                    kind,d=next(iter(obj.items()))
                    if kind not in ('axiom','thm','def','opaque','quot'):
                        raise ValueError(f'Unknown declaration tag {kind}')
                    self.add_decl(kind,d)
        if self.metadata is None: raise ValueError('Missing export metadata')
        self.by_name={n:i for i,n in enumerate(self.names)}

    def walk(self,targets):
        pending_names=[self.by_name[t] for t in targets]
        pending_expr=[]
        seen_names=set();seen_expr=bytearray(len(self.kinds))
        axioms=set();bad=[];counts=Counter();nexpr=0
        while pending_names or pending_expr:
            if pending_names:
                n=pending_names.pop()
                if n in seen_names: continue
                seen_names.add(n)
                d=self.decls.get(n)
                if d is None: raise ValueError(f'Missing declaration body: {self.names[n]}')
                counts[d['kind']]+=1
                if d['kind']=='axiom': axioms.add(self.names[n])
                if d['unsafe'] or d['partial']: bad.append(self.names[n])
                pending_expr.extend(d['roots']);pending_names.extend(d['members'])
                continue
            i=pending_expr.pop()
            if not 0<=i<len(seen_expr): raise ValueError(f'Missing expression {i}')
            if seen_expr[i]: continue
            seen_expr[i]=1;nexpr+=1
            k=KINDS[self.kinds[i]];a,b,c=self.a[i],self.b[i],self.c[i]
            if k=='const': pending_names.append(a)
            elif k in ('app','lam','forallE'): pending_expr.extend((a,b))
            elif k=='letE': pending_expr.extend((a,b,c))
            elif k=='proj': pending_names.append(a);pending_expr.append(c)
            elif k=='mdata': pending_expr.append(a)
            elif k=='natVal': pending_names.append(self.by_name['Nat'])
            elif k=='strVal':
                pending_names.extend(self.by_name[n] for n in ['String.ofList','Char.ofNat'])
        return {'targets':targets,'reachable_declarations':len(seen_names),
                'reachable_expressions':nexpr,'declaration_kinds':dict(sorted(counts.items())),
                'axioms':sorted(axioms),'unapproved_axioms':sorted(axioms-ALLOWED),
                'unsafe_or_partial':sorted(bad)}

    def level(self,i):
        k,v=self.levels[i]
        if k=='zero': return '0'
        if k=='param': return self.names[v]
        if k=='succ': return f'({self.level(v)}+1)'
        if k in ('max','imax'): return f'{k}({self.level(v[0])},{self.level(v[1])})'
        raise ValueError(f'Unknown universe tag {k}')

    def pretty(self,i,stack=(),budget=6000):
        if budget<=0: raise ValueError('Type pretty-print budget exhausted')
        k=KINDS[self.kinds[i]];a,b,c=self.a[i],self.b[i],self.c[i]
        def r(j,s=stack): return self.pretty(j,s,budget-1)
        if k=='bvar': return stack[a] if a<len(stack) else f'LOOSE_BVAR_{a}'
        if k=='sort': return 'Prop' if a==0 else f'Sort({self.level(a)})'
        if k=='const':
            us=self.const_us.get(i,[])
            return self.names[a]+('.{'+','.join(self.level(u) for u in us)+'}' if us else '')
        if k=='app': return f'({r(a)} {r(b)})'
        if k in ('lam','forallE'):
            x=f'x{len(stack)}'
            return f'({"fun" if k=="lam" else "forall"} {x} : {r(a)}, {r(b,(x,)+stack)})'
        if k=='letE':
            x=f'x{len(stack)}'
            return f'(let {x} : {r(a)} := {r(b)}; {r(c,(x,)+stack)})'
        if k=='proj': return f'({self.names[a]}.proj{b} {r(c)})'
        if k in ('natVal','strVal'): return json.dumps(self.literal_values[i])
        if k=='mdata': return r(a)
        raise ValueError(k)


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('export',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--target',action='append')
    a=p.parse_args();targets=a.target or TARGETS
    g=ExportGraph();g.load(a.export)
    records=[g.walk([t]) for t in targets]
    union=g.walk(targets)
    for t in targets:
        d=g.decls[g.by_name[t]]
        if d['kind']!='thm' or 'value' not in d['record']:
            raise ValueError(f'Target is not a theorem with a body: {t}')
    axioms={n:{'record':g.decls[g.by_name[n]]['record'],
               'type':g.pretty(g.decls[g.by_name[n]]['roots'][0])}
            for n in union['axioms']}
    detail_names=targets+[n for n in ['CubeSections.UpperBoundStatement','CubeSections.EqualityStatement',
        'CubeSections.AttainmentStatement','CubeSections.MainStatement','CubeSections.cube',
        'CubeSections.sectionMass','CubeSections.sectionVolume','CubeSections.sharpValue',
        'CubeSections.IsBalancedSection','CubeSections.BlockData.plane'] if n in g.by_name and g.by_name[n] in g.decls]
    details={}
    for n in detail_names:
        d=g.decls[g.by_name[n]]
        details[n]={'kind':d['kind'],'record':d['record'],'type':g.pretty(d['roots'][0])}
        if d['kind']=='def': details[n]['definition']=g.pretty(d['roots'][1])
    ok=not union['unapproved_axioms'] and not union['unsafe_or_partial']
    result={'status':'PASS_EXPORTED_BODY_DEPENDENCY_GRAPH' if ok else 'FAILED',
            'not_a_typechecker':True,'metadata':g.metadata,'export_path':str(a.export.resolve()),
            'export_sha256':sha(a.export),'export_bytes':a.export.stat().st_size,
            'line_count':g.lines,'expression_count':len(g.kinds),'declaration_count':len(g.decls),
            'per_target':records,'union':union,'axiom_signatures':axioms,'details':details,
            'note':'Traversal uses actual exported type/value expressions and inductive constructor/recursor rules. No #print axioms or cached axiom summary is an input. Inductive blocks are conservatively included in full. Axiom names are allowed here; their displayed signatures must also be reviewed.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('details','axiom_signatures')},indent=2))
    return 0 if ok else 1


if __name__=='__main__':
    sys.setrecursionlimit(20000)
    raise SystemExit(main())
