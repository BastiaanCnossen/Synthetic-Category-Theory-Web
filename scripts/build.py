"""Rebuild the web edition. Run outside the Windows sandbox for MiKTeX."""
from common import *
from prepare import prepare
from authored_pages import require_authored_pages, AUTHORED_PAGES
from publish_site import publish_generated_pages
import argparse, subprocess, shutil, time, tempfile

AGGREGATE='SCT.WebEdition'

def run(args, cwd=BUILD):
    print('Running: '+' '.join(map(str,args)),flush=True)
    p=subprocess.run(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',errors='replace')
    write(BUILD/(Path(args[0]).stem+'-last.log'),p.stdout)
    if p.returncode:
        print(p.stdout[-7000:]); raise RuntimeError(f'{args[0]} failed ({p.returncode})')
    return p.stdout

def build(frozen=False, reuse=False, incremental=False, manuscript_only=False):
    previous=json.loads(read(SNAP/'inputs.json')) if (SNAP/'inputs.json').exists() else None
    # Keep the current preview available throughout checking and conversion.
    require_authored_pages(SITE)
    prepare(frozen, manuscript_only=manuscript_only)
    state=json.loads(read(SNAP/'inputs.json'))
    fingerprint=digest(json.dumps(state['files'],sort_keys=True))
    receipt=BUILD/'check.json'
    if manuscript_only:
        from checked_code import verify_checked_code
        print(verify_checked_code(state),flush=True)
    elif reuse:
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
        # In incremental mode Agda validates cached interface fingerprints and
        # rechecks changed modules and their affected dependants itself.
        args=['agda','--no-libraries','--safe','--without-K']
        if not incremental: args.append('--ignore-interfaces')
        args+=['-i','src','--html','--html-highlight=all','--html-dir='+str(BUILD/'agda'),'src/SCT/WebEdition.agda']
        output=run(args,SNAP/'agda')
        version=run(['agda','--version']).splitlines()[0]
        dump(receipt,{'input_hash':fingerprint,'agda':version,'command':args,'aggregate':AGGREGATE,'checked':True})
    with tempfile.TemporaryDirectory(prefix='site-stage-',dir=BUILD) as temporary:
        stage=Path(temporary)
        for name in AUTHORED_PAGES: shutil.copyfile(SITE/name,stage/name)
        convert(site=stage)
        from assemble import assemble
        assemble(site=stage)
        from validate import validate
        validate(site=stage)
        # An author may have edited a hand-written page during the build.
        changed=False
        for name in AUTHORED_PAGES:
            if (stage/name).read_bytes()!=(SITE/name).read_bytes():
                shutil.copyfile(SITE/name,stage/name); changed=True
        if changed: validate(site=stage)
        publish_generated_pages(stage,SITE,ROOT)

def convert(site=SITE):
    # Actual LaTeX, Biber and TeX4ht determine numbering and citations.
    external=json.loads(read(BUILD/'external.json'))
    references={}
    for job in sorted({e.get('reference_job','reference-chapter') for e in external}-set(references)):
        if not re.fullmatch(r'reference-chapter-\d+',job): raise ValueError('Invalid reference job')
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error',job+'.tex'])
        references[job]=read(BUILD/(job+'.aux'))
    definitions=[]
    for entry in external:
        m=re.search(r'\\newlabel\{'+re.escape(entry['label'])+r'\}\{\{([^}]+)\}',references[entry.get('reference_job','reference-chapter')])
        if not m: raise ValueError('Missing fresh reference number: '+entry['label'])
        entry['number']=m[1]
        definitions.append('\\expandafter\\def\\csname pilotref@'+entry['label']+'\\endcsname{'+entry['kind']+' '+m[1]+'}')
        definitions.append('\\expandafter\\def\\csname piloturl@'+entry['label']+'\\endcsname{'+external_anchor(entry['label'])+'}')
    definitions.append('\\newcommand{\\EditionExternal}[1]{\\href{outside-selection.html\\#\\csname piloturl@#1\\endcsname}{\\csname pilotref@#1\\endcsname{} (outside selection)}}')
    write(BUILD/'external-references.tex','\n'.join(definitions)+'\n')
    dump(BUILD/'external.json',external)
    run(['pdflatex','-interaction=nonstopmode','-halt-on-error','pilot-pdf.tex'])
    run(['biber','pilot-pdf'])
    for _ in range(2): run(['pdflatex','-interaction=nonstopmode','-halt-on-error','pilot-pdf.tex'])
    run(['make4ht','-a','warning','-f','html5','-d','html','pilot.tex','mathjax,charset=utf-8'])
    run(['biber','pilot'])
    run(['make4ht','-a','warning','-f','html5','-d','html','pilot.tex','mathjax,charset=utf-8'])
    convert_diagrams(site=site)
    shutil.copyfile(BUILD/'pilot-pdf.pdf',site/'book.pdf')

def convert_diagrams(site=SITE):
    for d in json.loads(read(BUILD/'selection.json'))['diagrams']:
        stem=d['id']; svg=site/'assets/diagrams'/f'{stem}.svg'
        # Include the full preamble in the cache identity, not merely the diagram.
        sha=digest(read(BUILD/(stem+'.tex'))+read(BUILD/'preamble.tex'))
        cache=BUILD/(stem+'.sha256')
        if svg.exists() and cache.exists() and read(cache)==sha: continue
        # Staging starts empty, but the checked DVI can survive a failed build.
        # Its receipt includes the complete generated input and preamble.
        dvi=BUILD/(stem+'.dvi')
        if not (dvi.exists() and cache.exists() and read(cache)==sha):
            (BUILD/(stem+'.aux')).unlink(missing_ok=True)
            run(['latex','-interaction=nonstopmode','-halt-on-error',stem+'.tex'])
        svg.parent.mkdir(parents=True,exist_ok=True)
        run(['dvisvgm','--no-fonts','--exact-bbox','--output='+str(svg),stem+'.dvi'])
        write(cache,sha)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--frozen',action='store_true'); checks=p.add_mutually_exclusive_group(); checks.add_argument('--reuse-agda-check',action='store_true'); checks.add_argument('--incremental-agda-check',action='store_true'); p.add_argument('--convert-only',action='store_true'); p.add_argument('--diagrams-only',action='store_true')
    checks.add_argument('--manuscript-only',action='store_true',help='Update manuscript; retain the exact previously checked Agda sources and HTML')
    a=p.parse_args()
    if a.diagrams_only: convert_diagrams()
    elif a.convert_only: convert()
    else: build(a.frozen,a.reuse_agda_check,a.incremental_agda_check,a.manuscript_only)
