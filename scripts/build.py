"""Rebuild the web edition. Run outside the Windows sandbox for MiKTeX."""
from common import *
from prepare import prepare
import argparse, subprocess, shutil, time

AGGREGATE='SCT.WebEdition'

def run(args, cwd=BUILD):
    print('Running: '+' '.join(map(str,args)),flush=True)
    p=subprocess.run(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',errors='replace')
    write(BUILD/(Path(args[0]).stem+'-last.log'),p.stdout)
    if p.returncode:
        print(p.stdout[-7000:]); raise RuntimeError(f'{args[0]} failed ({p.returncode})')
    return p.stdout

def build(frozen=False, reuse=False):
    previous=json.loads(read(SNAP/'inputs.json')) if (SNAP/'inputs.json').exists() else None
    # Rebuild the distribution from an empty, explicitly bounded output tree.
    output=SITE.resolve()
    if output.parent!=ROOT.resolve() or output.name!='_site': raise ValueError('Unsafe distribution directory')
    if output.exists(): shutil.rmtree(output)
    output.mkdir()
    prepare(frozen)
    state=json.loads(read(SNAP/'inputs.json'))
    fingerprint=digest(json.dumps(state['files'],sort_keys=True))
    receipt=BUILD/'check.json'
    if reuse:
        old=json.loads(read(receipt))
        if old.get('checked') is not True or old.get('aggregate') != AGGREGATE:
            raise ValueError('Cannot reuse an incomplete aggregate check')
        if old['input_hash'] != fingerprint:
            agda_files=lambda files:{k:v for k,v in files.items() if k.startswith('agda/')}
            if not previous or old['input_hash']!=digest(json.dumps(previous['files'],sort_keys=True)) or agda_files(previous['files'])!=agda_files(state['files']):
                raise ValueError('Cannot reuse checks after Agda input changes or loss of the checked snapshot')
            old['input_hash']=fingerprint
            old['reused_after_non_agda_input_change']=True
            dump(receipt,old)
    else:
        # Only compiler-generated files in the validated build directory.
        generated=(BUILD/'agda').resolve()
        if ROOT.resolve() not in generated.parents: raise ValueError('Invalid Agda output directory')
        for stale in generated.glob('*'):
            if stale.is_file() and stale.suffix in ('.html','.css'): stale.unlink()
        args=['agda','--no-libraries','--safe','--without-K','--ignore-interfaces','-i','src','--html','--html-highlight=all','--html-dir='+str(BUILD/'agda'),'src/SCT/WebEdition.agda']
        output=run(args,SNAP/'agda')
        version=run(['agda','--version']).splitlines()[0]
        dump(receipt,{'input_hash':fingerprint,'agda':version,'command':args,'aggregate':AGGREGATE,'checked':True})
    convert()
    from assemble import assemble
    assemble()
    from validate import validate
    validate()

def convert():
    # Actual LaTeX, Biber and TeX4ht determine numbering and citations.
    run(['pdflatex','-interaction=nonstopmode','-halt-on-error','reference-chapter.tex'])
    aux=read(BUILD/'reference-chapter.aux')
    external=json.loads(read(BUILD/'external.json'))
    definitions=[]
    for entry in external:
        m=re.search(r'\\newlabel\{'+re.escape(entry['label'])+r'\}\{\{([^}]+)\}',aux)
        if not m: raise ValueError('Missing fresh reference number: '+entry['label'])
        entry['number']=m[1]
        definitions.append('\\expandafter\\def\\csname pilotref@'+entry['label']+'\\endcsname{Exercise '+m[1]+'}')
    definitions.append('\\newcommand{\\EditionExternal}[1]{\\href{outside-selection.html\\##1}{\\csname pilotref@#1\\endcsname{} (outside selection)}}')
    write(BUILD/'external-references.tex','\n'.join(definitions)+'\n')
    dump(BUILD/'external.json',external)
    run(['pdflatex','-interaction=nonstopmode','-halt-on-error','pilot-pdf.tex'])
    run(['biber','pilot-pdf'])
    for _ in range(2): run(['pdflatex','-interaction=nonstopmode','-halt-on-error','pilot-pdf.tex'])
    run(['make4ht','-a','warning','-f','html5','-d','html','pilot.tex','mathjax,charset=utf-8'])
    run(['biber','pilot'])
    run(['make4ht','-a','warning','-f','html5','-d','html','pilot.tex','mathjax,charset=utf-8'])
    convert_diagrams()
    shutil.copyfile(BUILD/'pilot-pdf.pdf',SITE/'book.pdf')

def convert_diagrams():
    for d in json.loads(read(BUILD/'selection.json'))['diagrams']:
        stem=d['id']; svg=SITE/'assets/diagrams'/f'{stem}.svg'
        # Include the full preamble in the cache identity, not merely the diagram.
        sha=digest(read(BUILD/(stem+'.tex'))+read(BUILD/'preamble.tex'))
        cache=BUILD/(stem+'.sha256')
        if svg.exists() and cache.exists() and read(cache)==sha: continue
        (BUILD/(stem+'.aux')).unlink(missing_ok=True)
        run(['latex','-interaction=nonstopmode','-halt-on-error',stem+'.tex'])
        svg.parent.mkdir(parents=True,exist_ok=True)
        run(['dvisvgm','--no-fonts','--exact-bbox','--output='+str(svg),stem+'.dvi'])
        write(cache,sha)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--frozen',action='store_true'); p.add_argument('--reuse-agda-check',action='store_true'); p.add_argument('--convert-only',action='store_true'); p.add_argument('--diagrams-only',action='store_true')
    a=p.parse_args()
    if a.diagrams_only: convert_diagrams()
    elif a.convert_only: convert()
    else: build(a.frozen,a.reuse_agda_check)
