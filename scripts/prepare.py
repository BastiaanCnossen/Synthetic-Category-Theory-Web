"""Capture the authoritative inputs and prepare a bounded TeX4ht conversion."""
from common import *
import shutil, subprocess, sys
from pilot_model import tex_markers

CHAPTER = 'Volume I - Synthetic Category Theory/1_Naive_Category_Theory.tex'
MASTER = 'Volume I - Synthetic Category Theory/Book_Vol_I.tex'

def prepare(frozen=False):
    BUILD.mkdir(exist_ok=True)
    if not frozen:
        from check_preservation import check_annotations
        check_annotations()
        inputs=[Path(CHAPTER),Path(MASTER),Path('preamble.tex'),Path('book.cls'),Path('Bibliography.bib')]
        inputs += [Path('agda')/p.relative_to(ROOT/'agda') for p in (ROOT/'agda/src').rglob('*') if p.suffix == '.agda' or p.name.endswith('.lagda.md')]
        if not (ROOT/'agda/src/SCT/WebEdition.agda').exists(): raise RuntimeError('WebEdition aggregate is absent')
        previous = json.loads(read(SNAP/'inputs.json'))['files'] if (SNAP/'inputs.json').exists() else {}
        for old in set(previous)-set(p.as_posix() for p in inputs):
            target=(SNAP/old).resolve()
            if SNAP.resolve() not in target.parents: raise ValueError('Unsafe snapshot path')
            target.unlink(missing_ok=True)
        files={}
        for rel in inputs:
            origin=ROOT/rel if rel.parts[0]=='agda' else REPO/rel
            data=origin.read_bytes(); target=SNAP/rel
            target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data)
            files[rel.as_posix()]=digest(data)
        revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
        dump(SNAP/'inputs.json',{'base_revision':revision,'note':'Exact working-tree inputs; hashes identify content, including uncommitted changes. Generated snapshots are not authoring sources.','files':files})
    inventory=json.loads(read(SNAP/'inputs.json'))
    for rel, sha in inventory['files'].items():
        if digest((SNAP/rel).read_bytes()) != sha: raise ValueError(f'Snapshot hash mismatch: {rel}')
    source=read(SNAP/CHAPTER)
    master=comments(read(SNAP/MASTER))
    active=re.findall(r'\\subfile\{([^}]+)\}',master)
    if '1_Naive_Category_Theory' not in active: raise ValueError('Selected chapter is no longer active in the volume master')
    # Selection follows semantic section labels, never line numbers.
    body=selected_source(source)
    stop=len(body)
    write(BUILD/'selected-source.tex',body)
    sections=list(re.finditer(r'\\section\{([^}]+)\}\s*\\label\[section\]\{([^}]+)\}',body))
    if [m[2] for m in sections] != ['sec:External_Theory','sec:Equivalence_Of_Categories']: raise ValueError('Selected section boundary changed; review selection')
    # A standalone faithful PDF is built from precisely the same selected source.
    preamble=read(SNAP/'preamble.tex')
    write(BUILD/'preamble.tex',preamble)
    shutil.copyfile(SNAP/'book.cls',BUILD/'sctbook.cls')
    (BUILD/'book.cls').unlink(missing_ok=True)
    shutil.copyfile(SNAP/'Bibliography.bib',BUILD/'Bibliography.bib')
    wrapper='\\documentclass[11pt]{book}\n\\newcommand{\\RepositoryRoot}{.}\n\\input{preamble}\n\\usepackage{framed,needspace}\n\\setcounter{secnumdepth}{2}\n\\begin{document}\n'
    full_body=read(SNAP/CHAPTER).split('\\begin{document}',1)[1].split('\\end{document}',1)[0]
    write(BUILD/'reference-chapter.tex',wrapper.replace('{book}','{sctbook}')+full_body+'\n\\end{document}\n')
    external=['exercise:Associativity_Products','exercise:Functoriality_Products2']
    external_records=[]
    for label in external:
        match=re.search(r'\\begin\{uexercise\}\s*\\label\[exercise\]\{'+re.escape(label)+r'\}[\s\S]*?\\end\{uexercise\}',full_body)
        if not match: raise ValueError('Outside-selection exercise moved: '+label)
        external_records.append({'label':label,'source':match[0]})
        # Resolve via fresh full-chapter counters before either final conversion.
        body=body.replace('\\Cref{'+label+'}','\\EditionExternal{'+label+'}')
    dump(BUILD/'external.json',external_records)
    wrapper=wrapper.replace('\\begin{document}', '\\input{external-references.tex}\n\\begin{document}')
    manifest=json.loads(read(ROOT/'correspondence.json'))
    for passage in manifest['passages']+manifest.get('reverse_only',[]):
        if not passage['declarations']: raise ValueError('Passage has no Agda declarations: '+passage['id'])
    print_body,markers=tex_markers(body,registry=manifest)
    if set(markers)!={p['id'] for p in manifest['passages']+manifest.get('reverse_only',[])}: raise ValueError('TeX/registry passage mismatch')
    write(BUILD/'pilot-pdf.tex',wrapper.replace('{book}','{sctbook}')+print_body+'\n\\printbibliography\n\\end{document}\n')
    body,_=tex_markers(body,html=True,registry=manifest)
    body=comments(body)
    body=re.sub(r'\\chapter\[([^\]]+)\]\{[^}]+\}',lambda m:'\\chapter{'+m[1]+'}',body)
    # Preserve whole displayed diagrams, including adjacent labels and punctuation.
    diagrams=[]
    def diagram(m):
        tex=m[0]
        if '\\begin{tikzcd}' not in tex: return tex
        key='diagram-'+digest(tex)[:16]
        diagrams.append({'id':key,'tex':tex})
        macro_start=preamble.index('\\DeclareMathOperator{\\Hom}')
        macro_end=preamble.index('% Theorem-style environments')
        diagram_macros=preamble[macro_start:macro_end]
        diagram_styles=preamble[preamble.index('\\tikzcdset{pullback/'):preamble.index('% Other\n') if '% Other\n' in preamble else preamble.index('\\newcommand\\noloc')]
        ds='\\documentclass[border=4pt]{standalone}\n\\usepackage{amsfonts,amsmath,amssymb,mathtools,dsfont,accents,stmaryrd,newtxtext,newtxmath,graphicx,tikz-cd,quiver}\n'+diagram_macros+'\n'+diagram_styles+'\n\\begin{document}\n$\\displaystyle '+tex[2:-2]+'$\n\\end{document}\n'
        write(BUILD/(key+'.tex'),ds)
        return '\\par\\HCode{<div class="diagram" data-diagram="'+key+'"></div>}\\par'
    body=re.sub(r'\\\[[\s\S]*?\\\]',diagram,body)
    if '\\begin{tikzcd}' in body: raise ValueError('Unconverted diagram outside a display')
    # Mark each logical theorem container; TeX still owns its title and counter.
    envs=set(re.findall(r'\\newtheorem\*?\{([^}]+)\}',preamble))
    def begin(m):
        env=m[1]
        if env not in envs: return m[0]
        scope='categorical' if env.startswith('u') else 'ordinary'
        return '\\par\\HCode{<section class="statement" data-environment="'+env+'" data-scope="'+scope+'">}\n'+m[0]
    body=re.sub(r'\\begin\{([^}]+)\}',begin,body)
    body=re.sub(r'\\end\{([^}]+)\}',lambda m:m[0]+ ('\n\\HCode{</section>}' if m[1] in envs else ''),body)
    def anchor(label): return '\\HCode{<span class="source-anchor" id="'+label+'"></span>}'
    # MathJax receives equation bodies verbatim, so HTML anchors must sit outside.
    equations=[]
    def protect_equation(match):
        text=match[0]
        labels=re.findall(r'\\label\{([^}]+)\}',text)
        equations.append(text+''.join(anchor(label) for label in labels))
        return 'PILOTEQUATIONTOKEN'+str(len(equations)-1)+'END'
    body=re.sub(r'\\begin\{equation\}[\s\S]*?\\end\{equation\}',protect_equation,body)
    body=re.sub(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',lambda m:m[0]+anchor(m[1]),body)
    body=re.sub(r'PILOTEQUATIONTOKEN(\d+)END',lambda m:equations[int(m[1])],body)
    # Keep references and bibliography delegated to the actual TeX packages.
    write(BUILD/'pilot.tex',wrapper+body+'\n\\printbibliography\n\\end{document}\n')
    dump(BUILD/'selection.json',{'chapter':CHAPTER,'sections':[{'title':m[1],'label':m[2]} for m in sections],'diagrams':diagrams,'source_characters':stop,'labels':re.findall(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',body)})
    print(f'Prepared 2 sections, {len(diagrams)} diagram displays, {len(inventory["files"])} pinned inputs.')

if __name__=='__main__': prepare('--frozen' in sys.argv)
