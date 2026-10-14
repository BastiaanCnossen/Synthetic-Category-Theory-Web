"""Audit the self-contained Pages artifact without access to the manuscript."""
from pathlib import Path
import json, hashlib


def check(site):
    site=Path(site).resolve()
    if not (site/'index.html').is_file(): raise ValueError('Distribution index is missing')
    info=json.loads((site/'build-info.json').read_text(encoding='utf-8'))
    allowed=set(info['published_modules'])
    editions=info.get('chapter_editions',[])
    edition_sources={e['source_prefix'].removeprefix('source-files/')+n.replace('.','/'):n
                     for e in editions for n in e['source_modules']}
    edition_html={e['code_prefix'].removeprefix('agda/')+n+'.html' for e in editions for n in e['compiled_modules']}
    root_files={'.nojekyll','index.html','basic-vocabulary.html','coherences.html','equivalences.html','mapping-animae.html','initial-categories-and-coproducts.html','pullbacks.html','functor-categories.html','pushouts.html',
                'introduction.html','overview-of-the-axioms.html','chapter-introduction.html','internal-structure-introduction.html','morphisms-and-diagrams.html','code-index.html','formalization.html',
                'segal-axiom.html','rezk-axiom.html','groupoids.html','recognizing-animae.html','chapter-2-exercises.html',
                'constructions-introduction.html','subcategories.html','full-subcategories.html','localizations.html',
                'geometric-realizations.html','exponentiable-functors.html','joins.html','slice-categories.html','chapter-3-exercises.html',
                'build-report.html','outside-selection.html','book.pdf','build-info.json','validation.json'}
    asset_files={'reader-shell.css','reader.css','reader.js','favicon.svg','Agda.css','math-config.js','agda-context.js'}
    from supplementary import catalog
    root_files.update({'supplementary-notes.html'} | {n['slug']+'.html' for n in catalog()})
    asset_files.add('supplementary.js')
    asset_files.update({'module-navigation.js','module-navigation-data.js'})
    if editions:
        root_files.update({'chapter01-code.html','chapter-edition.json'})
        asset_files.update({'chapter01-agda-context.js','chapter01-supplementary.js','chapter01-module-navigation-data.js'})
    asset_files.update('diagrams/'+name+'.svg' for name in info.get('diagrams',[]))
    compiled=set(info.get('compiled_modules',allowed))
    vendor_files=json.loads((Path(__file__).resolve().parent/'vendor-files.json').read_text(encoding='utf-8'))
    actual=set()
    for file in (site/'source-files').rglob('*'):
        if file.is_file():
            relative=file.relative_to(site/'source-files').as_posix()
            if not (relative.endswith('.lagda.md') or relative.endswith('.agda')):
                raise ValueError('Unexpected raw source artifact: '+relative)
            stem=relative.removesuffix('.lagda.md').removesuffix('.agda')
            actual.add(stem if stem in edition_sources else stem.replace('/','.'))
    if actual!=allowed|set(edition_sources): raise ValueError('Raw modules differ from the published module selection')
    for file in site.rglob('*'):
        if file.is_symlink(): raise ValueError('Symlink in distribution')
        if not file.is_file(): continue
        relative=file.relative_to(site)
        if file.suffix in ('.tex','.bib','.aux','.log','.bbl','.agdai','.py','.ps1','.toml'):
            raise ValueError('Private source/build file in distribution: '+str(relative))
        if len(relative.parts)==1:
            permitted=relative.name in root_files
        else:
            folder=relative.parts[0]
            tail=Path(*relative.parts[1:]).as_posix()
            permitted=(folder=='assets' and tail in asset_files or
                       folder=='vendor' and tail in vendor_files or
                       folder=='agda' and tail in ({name+'.html' for name in compiled}|edition_html) or
                       folder=='source-files' and (tail.removesuffix('.lagda.md').removesuffix('.agda').replace('/','.') in allowed or
                                                   tail.removesuffix('.lagda.md').removesuffix('.agda') in edition_sources))
        if not permitted: raise ValueError('File outside publication allowlist: '+str(relative))
        if relative.parts[0]=='vendor' and hashlib.sha256(file.read_bytes()).hexdigest()!=vendor_files[tail]:
            raise ValueError('Vendored asset changed: '+str(relative))
        if file.suffix in ('.html','.json','.js','.css','.md','.agda'):
            text=file.read_text(encoding='utf-8')
            for forbidden in ('C:/Users/','C:\\Users\\','Volume I - Synthetic Category Theory/','snapshot/','pilot/tex/','_build/'):
                if forbidden in text: raise ValueError('Private path in '+str(relative))
            if file.suffix=='.html' and 'noindex,nofollow' not in text:
                raise ValueError('Missing indexing policy: '+str(relative))
    return {'status':'passed','published_source_modules':len(actual)}


if __name__=='__main__':
    site=Path(__file__).resolve().parents[1]/'_site'
    result=check(site)
    if json.loads((site/'validation.json').read_text(encoding='utf-8')).get('status')!='passed':
        raise ValueError('Distribution has not passed the full local build validation')
    print(json.dumps(result))
