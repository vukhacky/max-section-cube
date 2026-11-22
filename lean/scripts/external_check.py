#!/usr/bin/env python3
"""Explicit-target checker orchestration; never invoke a checker with no target.

Run after compilation has finished. Outputs are written to --output-dir;
the source project and pinned dependency caches are read-only inputs.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

from verification import ROOT, environment, check_targets

TOOLS=Path(__file__).resolve().parent
HERE=ROOT/'.lake/verification/external'
EXPORTER=None
NANODA=None
TARGETS=['CubeSections.maximalSectionVolume','CubeSections.balancedSectionAttains',
         'CubeSections.maximalSectionVolume_eq_iff','CubeSections.maximalSections_main']
ALLOW=['propext','Classical.choice','Quot.sound']


def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()


def config(export,output,pretty=(),pretty_path=None):
    cfg={'export_file_path':str(export.resolve()),'use_stdin':False,'num_threads':1,
         'stack_size_bytes':67108864,'permitted_axioms':ALLOW,
         'unpermitted_axiom_hard_error':True,'unsafe_permit_all_axioms':False,
         'nat_extension':True,'string_extension':True,'pp_declars':list(pretty),
         'pp_to_stdout':False,'print_success_message':True}
    if pretty:
        destination=(pretty_path or output.with_suffix('.pretty.txt')).resolve()
        destination.parent.mkdir(parents=True,exist_ok=True)
        # Nanoda 0.4.31 expects an existing pretty-print destination.
        destination.touch(exist_ok=True)
        cfg['pp_output_path']=str(destination)
    output.write_text(json.dumps(cfg,indent=2)+'\n')
    return output


def invoke(command,label,env,timeout=1800,output=None):
    start=time.monotonic();when=datetime.datetime.now(datetime.timezone.utc).isoformat()
    out=output or HERE/(label+'.stdout.log');err=HERE/(label+'.stderr.log')
    with out.open('wb') as of,err.open('wb') as ef:
        try:
            r=subprocess.run([str(x) for x in command],cwd=HERE,env=env,
                             stdout=of,stderr=ef,timeout=timeout)
            code=r.returncode
        except subprocess.TimeoutExpired:
            code=124
    receipt={'label':label,'command':[str(x) for x in command],'exit_code':code,
             'started_utc':when,'seconds':time.monotonic()-start,
             'stdout':str(out),'stderr':str(err),'stdout_sha256':sha(out),'stderr_sha256':sha(err),
             'environment':{k:env.get(k) for k in ('LEAN_PATH','LEAN_SYSROOT','LEAN_ABORT_ON_PANIC')},
             'compiler_or_checker_sha256':sha(Path(command[0])) if Path(command[0]).is_file() else None}
    (HERE/(label+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
    return code


def smoke(runtime,env):
    env={**env,'LEAN_PATH':''}
    pos=HERE/'smoke_positive.ndjson'
    rc=invoke([EXPORTER,'Init','--','Nat.add_zero'],
              'smoke_export',env,60,pos)
    if rc:return rc
    cfg=config(pos,HERE/'smoke_positive.json',['Nat.add_zero'])
    good=invoke([NANODA,cfg],'smoke_nanoda_positive',env,60)
    if good:return good
    rows=[json.loads(s) for s in pos.read_text().splitlines()]
    names={0:''}
    for row in rows:
        if 'in' in row:
            v=row.get('str',row.get('num'));pre=names[v['pre']]
            names[row['in']]=(pre+'.' if pre else '')+v.get('str',str(v.get('i')))
    nat=next(i for i,n in names.items() if n=='Nat')
    wrong_expr=next(row['ie'] for row in rows if 'const' in row and row['const']['name']==nat)
    damaged=[];changed=False
    for row in rows:
        if 'thm' in row and names[row['thm']['name']]=='Nat.add_zero':
            row={'thm':{**row['thm'],'value':wrong_expr}};changed=True
        damaged.append(row)
    if not changed:raise RuntimeError('Smoke target theorem body not found')
    neg=HERE/'smoke_wrong_body.ndjson'
    neg.write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in damaged))
    cfg=config(neg,HERE/'smoke_wrong_body.json')
    bad=invoke([NANODA,cfg],'smoke_nanoda_wrong_body',env,60)
    unauthorized=HERE/'smoke_unapproved_axiom.ndjson'
    name=max(names)+1
    rows.extend([{'in':name,'str':{'pre':0,'str':'MSCUnapprovedControlAxiom'}},
                 {'axiom':{'name':name,'levelParams':[],'type':wrong_expr,'isUnsafe':False}}])
    unauthorized.write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rows))
    cfg=config(unauthorized,HERE/'smoke_unapproved_axiom.json')
    ax=invoke([NANODA,cfg],'smoke_nanoda_unapproved_axiom',env,60)
    graph=invoke([Path(sys.executable),TOOLS/'verify_export_graph.py',pos,
                  '--target','Nat.add_zero','--output',HERE/'smoke_graph.json'],
                 'smoke_graph',env,60)
    wrong_error=(HERE/'smoke_nanoda_wrong_body.stderr.log').read_text(errors='replace')
    axiom_error=(HERE/'smoke_nanoda_unapproved_axiom.stderr.log').read_text(errors='replace')
    wrong_rejected=bad==101 and 'tc.rs' in wrong_error and 'assertion' in wrong_error
    axiom_rejected=ax==1 and 'unpermitted axiom' in axiom_error and 'MSCUnapprovedControlAxiom' in axiom_error
    status={'positive_exit':good,'wrong_body_exit':bad,'unapproved_axiom_exit':ax,
            'graph_exit':graph,'wrong_body_type_rejected':wrong_rejected,'extra_axiom_rejected':axiom_rejected,
            'status':'PASS_SMOKE' if good==0 and wrong_rejected and axiom_rejected and graph==0 else 'FAILED_SMOKE',
            'note':'Negative controls require the observed type-checking and axiom-policy rejection reasons for nanoda 0.4.31.'}
    (HERE/'smoke_summary.json').write_text(json.dumps(status,indent=2)+'\n')
    print(json.dumps(status,indent=2),flush=True)
    return 0 if status['status']=='PASS_SMOKE' else 1


def main():
    global HERE, EXPORTER, NANODA
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=['smoke','export','graph','nanoda'])
    p.add_argument('--lean-bin',type=Path,help='Directory containing the pinned lean executable')
    p.add_argument('--packages',type=Path,help='Pinned packages directory; default .lake/packages')
    p.add_argument('--exporter',type=Path,help='leanexport executable; default beside lean')
    p.add_argument('--checker',type=Path,help='nanoda executable; default nanoda_bin beside lean')
    p.add_argument('--output-dir',type=Path,default=HERE)
    p.add_argument('--timeout',type=int,default=1800)
    a=p.parse_args()
    check_targets()
    lean,env,identity,_=environment(a.lean_bin,a.packages)
    runtime=lean.parent.parent
    HERE=a.output_dir.resolve()
    HERE.mkdir(parents=True,exist_ok=True)
    EXPORTER=a.exporter.resolve() if a.exporter else lean.parent/'leanexport'
    NANODA=a.checker.resolve() if a.checker else lean.parent/'nanoda_bin'
    if a.action in ('smoke','export') and not EXPORTER.is_file():
        raise RuntimeError('leanexport is required: pass --exporter PATH')
    if a.action in ('smoke','nanoda') and not NANODA.is_file():
        raise RuntimeError('nanoda is required: pass --checker PATH')
    if a.action=='smoke':return smoke(runtime,env)
    export=HERE/'targets.ndjson'
    if a.action=='export':
        return invoke([EXPORTER,'CubeSections.Main','--',*TARGETS],
                      'targets_export',env,a.timeout,export)
    if not export.is_file():
        raise RuntimeError('Run export before graph or nanoda with the same --output-dir')
    if a.action=='graph':
        return invoke([Path(sys.executable),TOOLS/'verify_export_graph.py',export,
                       '--output',HERE/'targets_graph.json'],'targets_graph',env,a.timeout)
    cfg=config(export,HERE/'nanoda_targets.json',ALLOW+TARGETS+[
        'CubeSections.UpperBoundStatement','CubeSections.EqualityStatement',
        'CubeSections.AttainmentStatement','CubeSections.MainStatement'],HERE/'targets.pretty.txt')
    return invoke([NANODA,cfg],'targets_nanoda',env,a.timeout)


if __name__=='__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f'External checking error: {error}',file=sys.stderr)
        raise SystemExit(1)
