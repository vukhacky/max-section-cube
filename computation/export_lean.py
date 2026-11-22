#!/usr/bin/env python3
"""Generate candidate Lean arithmetic proofs from the canonical rational tree data.

Lean proofs use norm_num and structural conjunction; no external success Boolean
is imported. JSON provenance does not occur as a theorem premise.
"""
from __future__ import annotations
import argparse,hashlib,json
from fractions import Fraction as F
from pathlib import Path

HERE=Path(__file__).resolve().parent
import sys, tempfile
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import verify
NORM_DEFS='''Leaf.Accepts, Parameters.Valid, Rectangle.InWindow,
      chargeSum, chargeUpper, curvatureEnvelope, surplus, angularDenominator,
      AngleTest, projectionLower, StripTest, determinantLower, gramLower,
      sine, cosine, radiusUpper, eta'''

def qterm(value):
    n,d=value.split('/')
    return f'({n} / {d} : ℚ)'

def frepr(x):return f'{x.numerator}/{x.denominator}'

def generate(case):
    q,m,l=case['q'],case['m'],case['l'];name=case.get('_namespace',f'Q{q}M{m}L{l}')
    lines=['import CubeSections.Certificates.Coverage'] + [f'import CubeSections.Certificates.Data.{x}' for x in case.get('_imports',[])] + ['',
           '/-! Generated from computation/data/pair_trees.json; all arithmetic is proved in Lean. -/',
           f'namespace CubeSections.Certificates.Data.{name}','',
           'set_option maxRecDepth 8192','set_option maxHeartbeats 4000000','',
           f'def parameters : Parameters := ⟨{q}, {m}, {l}⟩','']
    nextid=0
    def visit(node,box):
        nonlocal nextid
        idx=nextid;nextid+=1
        b=f'box_{idx}';n=f'node_{idx}'
        x,X,y,Y=box
        if node['kind']=='external':
            ref=node['ref']
            lines.append(f'private def {b} : Rectangle := ⟨{", ".join(qterm(t) for t in box)}⟩')
            lines.append(f'private def {n} : Tree := {ref}.tree')
            lines.append(f'private theorem {n}_accepts : {n}.Accepts parameters {b} := {ref}.accepted')
        elif node['kind']=='split':
            z=node['midpoint']
            if node['axis']=='c':
                lc=visit(node['left'],(x,z,y,Y));rc=visit(node['right'],(z,X,y,Y));ctor='splitC';valid='SplitCValid'
            else:
                lc=visit(node['left'],(x,X,y,z));rc=visit(node['right'],(x,X,z,Y));ctor='splitD';valid='SplitDValid'
            lines.append(f'private def {b} : Rectangle := ⟨{", ".join(qterm(t) for t in box)}⟩')
            lines.append(f'private def {n} : Tree := .{ctor} {qterm(z)} {lc} {rc}')
            lines.append(f'private theorem {n}_accepts : {n}.Accepts parameters {b} := by')
            lines.append(f'  change {valid} {b} {qterm(z)} ∧ _ ∧ _')
            lines.append(f'  exact ⟨by norm_num [{valid}, {b}], {lc}_accepts, {rc}_accepts⟩')
        else:
            ctor='.projection' if node['kind']=='projection' else f'(.strip {qterm(node["T"])})'
            lines.append(f'private def {b} : Rectangle := ⟨{", ".join(qterm(t) for t in box)}⟩')
            lines.append(f'private def {n} : Tree := .leaf {ctor}')
            lines.append(f'private theorem {n}_accepts : {n}.Accepts parameters {b} := by')
            lines.append(f'  norm_num [Tree.Accepts, {n}, {b}, parameters, {NORM_DEFS}]')
        lines.append('')
        return n
    r=case['root_box'];rootnode=visit(case['tree'],(*r['c'],*r['d']))
    lines.append(f'def tree : Tree := {rootnode}')
    if case.get('_is_chunk'):
        lines += ['def rootBox : Rectangle := box_0',
                  f'theorem accepted : tree.Accepts parameters rootBox := {rootnode}_accepts','']
    else:
        lines += ['theorem accepted : tree.Accepts parameters (rootRectangle parameters.q) := by',
                  '  have hb : box_0 = rootRectangle parameters.q := by',
                  '    norm_num [box_0, rootRectangle, parameters]',
                  f'  simpa only [tree, ← hb] using {rootnode}_accepts','',
                  'theorem checked : tree.check parameters (rootRectangle parameters.q) = true :=',
                  '  (tree.check_eq_true_iff parameters (rootRectangle parameters.q)).mpr accepted','',
                  '#print axioms accepted','#print axioms checked','']
    lines += [f'end CubeSections.Certificates.Data.{name}','']
    return name,'\n'.join(lines),nextid

def write_modules(data, output, chunk_leaves, selected=None):
    """Emit candidates; the caller must subsequently compile them with Lean."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    written = []
    def leaf_count(tree):
        return 1 if tree['kind'] != 'split' else leaf_count(tree['left']) + leaf_count(tree['right'])
    def emit(case):
        name, text, nodes = generate(case)
        relative = Path(*name.split('.')).with_suffix('.lean')
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding='utf-8')
        written.append({'module': str(relative), 'nodes': nodes,
                        'sha256': hashlib.sha256(text.encode()).hexdigest()})
    selected_cases = [case for case in data['cases'] if selected is None or
                      f'Q{case["q"]}M{case["m"]}L{case["l"]}' == selected]
    verify.require(bool(selected_cases), 'Unknown selected case')
    for case in selected_cases:
        name = f'Q{case["q"]}M{case["m"]}L{case["l"]}'
        if leaf_count(case['tree']) <= chunk_leaves:
            emit(case)
            continue
        imports = []
        def cut(tree, box):
            if leaf_count(tree) <= chunk_leaves:
                subname = f'C{len(imports):03d}'
                imports.append(name + '.' + subname)
                subcase = {**case, 'tree': tree,
                           'root_box': {'c': list(box[:2]), 'd': list(box[2:])},
                           '_namespace': name + '.' + subname, '_is_chunk': True,
                           'counts': {'leaves': leaf_count(tree)}}
                emit(subcase)
                return {'kind': 'external', 'ref': subname}
            x, upper_x, y, upper_y = box
            midpoint = tree['midpoint']
            if tree['axis'] == 'c':
                left, right = (x, midpoint, y, upper_y), (midpoint, upper_x, y, upper_y)
            else:
                left, right = (x, upper_x, y, midpoint), (x, upper_x, midpoint, upper_y)
            return {**tree, 'left': cut(tree['left'], left), 'right': cut(tree['right'], right)}
        root = case['root_box']
        tree = cut(case['tree'], (*root['c'], *root['d']))
        emit({**case, 'tree': tree, '_imports': imports})
    return written


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=HERE / 'data/pair_trees.json')
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--check', action='store_true', help='Regenerate in a temporary directory and compare all emitted Lean bytes')
    action.add_argument('--output', type=Path, help='Write candidates to a new directory outside the tracked Lean source tree')
    parser.add_argument('--lean-dir', type=Path, default=HERE.parent / 'lean')
    parser.add_argument('--case', help='Emit only one namespace, for example Q4M4L4')
    parser.add_argument('--chunk-leaves', type=int, default=64)
    args = parser.parse_args()
    verify.require(args.chunk_leaves > 0, 'chunk-leaves must be positive')
    data = verify.load_json(args.certificate)
    verify.replay(data)
    target = args.lean_dir.resolve() / 'CubeSections/Certificates/Data'
    if args.check:
        with tempfile.TemporaryDirectory(prefix='msc-lean-data-') as temporary:
            emitted = write_modules(data, Path(temporary), args.chunk_leaves, args.case)
            mismatches = [row['module'] for row in emitted
                          if not (target / row['module']).is_file() or
                          (target / row['module']).read_bytes() != (Path(temporary) / row['module']).read_bytes()]
            verify.require(not mismatches, 'Generated Lean data differ: ' + ', '.join(mismatches))
        status = 'BYTE_IDENTICAL_LEAN_DATA_REGENERATION'
    else:
        destination = args.output.resolve()
        verify.require(destination != target and target not in destination.parents,
                       'Write a candidate outside the tracked Lean data tree, review, then copy explicitly')
        verify.require(not destination.exists(), 'Output directory must not already exist')
        emitted = write_modules(data, destination, args.chunk_leaves, args.case)
        status = 'LEAN_CANDIDATES_WRITTEN_NOT_COMPILED'
    print(json.dumps({'status': status, 'modules': len(emitted),
                      'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
                      'module_sha256': {row['module']: row['sha256'] for row in emitted}}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RecursionError) as error:
        print(f'LEAN DATA GENERATION FAILED: {error}', file=sys.stderr)
        raise SystemExit(1)
