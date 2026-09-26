"""Capture the authoritative inputs and prepare a bounded TeX4ht conversion."""
from common import *
import shutil, subprocess, sys
from pilot_model import tex_markers


def manuscript_body(source):
    return source.split(r'\begin{document}',1)[1].split(r'\end{document}',1)[0]


def active_sources(master):
    return [(Path(MASTER).parent / (name+'.tex')).as_posix()
            for name in re.findall(r'\\subfile\{([^}]+)\}',comments(master))]


def resolve_external_references(body, sources, wrapper):
    """Resolve omitted material with fresh TeX counters in master-file order.

    Chapter-only references compile just the opening heading. References to
    statements compile their chapter privately, without publishing its prose.
    """
    selected=set(re.findall(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',comments(body)))
    catalog={}; chapters={}; number=0
    for relative in sources:
        text=manuscript_body(read(SNAP/relative))
        if not re.search(r'\\chapter(?:\[[^\]]*\])?\{',comments(text)): continue
        number+=1
        chapters[number]=text
        for match in re.finditer(r'\\label\[([^\]]+)\]\{([^}]+)\}',comments(text)):
            catalog.setdefault(match[2],[]).append((match[1],number))
    records={}; jobs={}
    def replace(match):
        labels=[label.strip() for label in match[1].split(',')]
        if all(label in selected for label in labels): return match[0]
        replacements=[]
        for label in labels:
            if label in selected:
                replacements.append(r'\Cref{'+label+'}'); continue
            candidates=catalog.get(label,[])
            if len(candidates)!=1: raise ValueError('Unresolved outside-selection reference: '+label)
            kind,number=candidates[0]
            records[label]={'label':label,'kind':kind.capitalize(),'reference_job':f'reference-chapter-{number}'}
            jobs.setdefault(number,[]).append((kind,label))
            replacements.append(r'\EditionExternal{'+label+'}')
        return ', '.join(replacements)
    body=re.sub(r'\\Cref\{([^}]+)\}',replace,body)
    for number,labels in jobs.items():
        text=chapters[number]
        if all(kind=='chapter' for kind,_ in labels):
            ends=[re.search(r'\\label\[chapter\]\{'+re.escape(label)+r'\}',text).end()
                  for _,label in labels]
            text=text[:max(ends)]
        write(BUILD/f'reference-chapter-{number}.tex',wrapper.replace('{book}','{sctbook}')+
              r'\setcounter{chapter}{'+str(number-1)+'}\n'+text+'\n'+r'\end{document}'+'\n')
    return body,list(records.values())


def chapter_external_references(body, full_body):
    """Route referenced Chapter 1 material according to the actual selection."""
    exercises=['exercise:Associativity_Products','exercise:Functoriality_Products2',
               'exercise:Associativity_Coproducts','exercise:Associativity_Fiber_Products2',
               'exercise:Pullback_Over_Terminal_Category2','exercise:Embeddings_Closed_Under_Base_Change',
               'exercise:Functoriality_Postcomposition']
    selected_labels=set(re.findall(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',body))
    records=[]
    for label in exercises+['sec:Functor_Categories']:
        reference='\\Cref{'+label+'}'
        if label in selected_labels or reference not in body:
            continue
        if label.startswith('exercise:'):
            match=re.search(r'\\begin\{(?P<env>u?exercise)\}\s*\\label\[exercise\]\{'+re.escape(label)+r'\}[\s\S]*?\\end\{(?P=env)\}',full_body)
            if not match: raise ValueError('Outside-selection exercise moved: '+label)
            records.append({'label':label,'source':match[0],'kind':'Exercise'})
        else:
            if not re.search(r'\\label\[section\]\{'+re.escape(label)+r'\}',full_body):
                raise ValueError('Functor-category section moved')
            records.append({'label':label,'title':'Functor categories','kind':'Section'})
        body=body.replace(reference,'\\EditionExternal{'+label+'}')
    return body,records

def prepare(frozen=False, manuscript_only=False):
    BUILD.mkdir(exist_ok=True)
    if not frozen:
        if manuscript_only:
            from checked_code import retain_checked_code
            retain_checked_code()
        from check_preservation import check_annotations
        check_annotations()
        previous = json.loads(read(SNAP/'inputs.json'))['files'] if (SNAP/'inputs.json').exists() else {}
        inputs=[Path(MASTER),Path('preamble.tex'),Path('book.cls'),Path('Bibliography.bib')]
        inputs += [Path(p) for p in active_sources(read(manuscript_input(MASTER)))]
        inputs += ([Path(name) for name in previous if name.startswith('agda/')] if manuscript_only else
                   [Path('agda')/p.relative_to(ROOT/'agda') for p in (ROOT/'agda/src').rglob('*') if p.suffix == '.agda' or p.name.endswith('.lagda.md')])
        if not (ROOT/'agda/src/SCT/WebEdition.agda').exists(): raise RuntimeError('WebEdition aggregate is absent')
        for old in set(previous)-set(p.as_posix() for p in inputs):
            target=(SNAP/old).resolve()
            if SNAP.resolve() not in target.parents: raise ValueError('Unsafe snapshot path')
            target.unlink(missing_ok=True)
        files={}; sources={}
        for rel in inputs:
            origin=(SNAP/rel if manuscript_only else ROOT/rel) if rel.parts[0]=='agda' else manuscript_input(rel)
            data=origin.read_bytes(); target=SNAP/rel
            target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data)
            files[rel.as_posix()]=digest(data)
            sources[rel.as_posix()]=('previously checked agda' if manuscript_only else 'agda') if rel.parts[0]=='agda' else 'annotated' if origin.is_relative_to(ANNOTATED) else 'private manuscript'
        revision=subprocess.check_output(['git','-c','safe.directory='+REPO.as_posix(),'rev-parse','HEAD'],cwd=REPO,text=True).strip()
        dump(SNAP/'inputs.json',{'base_revision':revision,'note':'The revision identifies the private manuscript repository; hashes and source kinds identify the actual inputs. Manuscript-only builds retain the earlier checked Agda snapshot explicitly.','files':files,'sources':sources})
    inventory=json.loads(read(SNAP/'inputs.json'))
    for rel, sha in inventory['files'].items():
        if digest((SNAP/rel).read_bytes()) != sha: raise ValueError(f'Snapshot hash mismatch: {rel}')
    master=comments(read(SNAP/MASTER))
    active=re.findall(r'\\subfile\{([^}]+)\}',master)
    for chapter in BOOK_FRONTMATTER+BOOK_CHAPTERS:
        if Path(chapter['source']).stem not in active: raise ValueError('Selected chapter is no longer active in the volume master')
    # Selection follows semantic section labels, never line numbers.
    body='\n'.join([manuscript_body(read(SNAP/p['source'])) for p in BOOK_FRONTMATTER]+
                   [selected_source(read(SNAP/chapter['source']),chapter['source']) for chapter in BOOK_CHAPTERS])
    stop=len(body)
    write(BUILD/'selected-source.tex',body)
    sections=section_headings(body)
    if [m['label'] for m in sections] != [label for _, _, label in BOOK_SECTIONS]: raise ValueError('Selected section boundary changed; review selection')
    # A standalone faithful PDF is built from precisely the same selected source.
    preamble=read(SNAP/'preamble.tex')
    write(BUILD/'preamble.tex',preamble)
    shutil.copyfile(SNAP/'book.cls',BUILD/'sctbook.cls')
    (BUILD/'book.cls').unlink(missing_ok=True)
    shutil.copyfile(SNAP/'Bibliography.bib',BUILD/'Bibliography.bib')
    wrapper='\\documentclass[11pt]{book}\n\\newcommand{\\RepositoryRoot}{.}\n\\input{preamble}\n\\usepackage{framed,needspace}\n\\setcounter{secnumdepth}{2}\n\\begin{document}\n'
    body,external_records=resolve_external_references(body,active_sources(master),wrapper)
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
        # TeX4ht's enclosing proof supplies its end marker after the SVG.
        # A standalone diagram has no proof environment for \qedhere.
        ds=ds.replace('\\begin{document}', '\\providecommand{\\qedhere}{}\n\\begin{document}')
        write(BUILD/(key+'.tex'),ds)
        return '\\par\\HCode{<div class="diagram" data-diagram="'+key+'"></div>}\\par'
    def numbered_diagram(m):
        content=m[1]
        if '\\begin{tikzcd}' not in content: return m[0]
        labels=re.findall(r'\\label\{([^}]+)\}',content)
        if len(labels)!=1: raise ValueError('A numbered diagram needs exactly one equation label')
        content=re.sub(r'\\label\{[^}]+\}','',content).strip()
        converted=diagram(re.match(r'[\s\S]*',r'\['+content+r'\]'))
        diagrams[-1]['equation_label']=labels[0]
        return r'\refstepcounter{equation}\label{'+labels[0]+'}'+converted
    body=re.sub(r'\\begin\{equation\}([\s\S]*?)\\end\{equation\}|\\\[[\s\S]*?\\\]',
                lambda m:numbered_diagram(m) if m[1] is not None else diagram(m),body)
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
    def anchor(label): return '\\HCode{<span class="source-anchor" id="'+conversion_anchor(label)+'"></span>}'
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
    dump(BUILD/'selection.json',{'frontmatter':[p['source'] for p in BOOK_FRONTMATTER],'chapters':[c['source'] for c in BOOK_CHAPTERS],'sections':[{'title':m['title'],'label':m['label']} for m in sections],'diagrams':diagrams,'source_characters':stop,'labels':re.findall(r'\\label(?:\[[^\]]+\])?\{([^}]+)\}',body)})
    print(f'Prepared {len(sections)} sections, {len(diagrams)} diagram displays, {len(inventory["files"])} pinned inputs.')

if __name__=='__main__': prepare('--frozen' in sys.argv)
