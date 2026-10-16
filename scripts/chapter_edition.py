"""Install independently checked chapter readers over the retained book edition.

Chapter 2 may supply a separate bundle, while other chapters retain their original
compiler pages and receipts. Mathematical sources remain commit-pinned.
"""
from common import *
from urllib.parse import urlsplit, unquote, quote
from collections import Counter
import copy

CONFIG = BUILD/'chapter-editions.json'
REPORT = BUILD/'chapter-edition-validation.json'
CODE = 'agda/chapter01/'
RAW = 'source-files/chapter01/'
CONTEXT = 'chapter01-agda-context.js'
EXTRA = 'chapter01-supplementary.js'
NAV = 'chapter01-module-navigation-data.js'


def rebuild2_code_introduction(checked_date):
    """Author-supplied introduction for the current Chapter 1 code page."""
    return ('<p>The current experimental webpage contains the version of the Chapter 1 agda code '
            'from <code>rebuild2/src</code>, last checked on '+escape(checked_date)+'.</p>'
            '<h2>Mathematical scope</h2><p>One deviation from the book is that we do not assume '
            'that <code>isAn</code> is closed under equivalences of categories. This is not needed '
            'for anything in Chapter 1 and will become provable after having available the '
            'groupoid recognition principle from Chapter 2.</p>'
            '<h2>Publication selection</h2><p>All mathematical Chapter 1 modules are included.</p>')


def clear_generated_overlay(site):
    """Remove only the known overlay artifacts before validating a fresh baseline."""
    candidates=[site/'chapter-edition.json',site/'chapter01-code.html']
    candidates += [site/'assets'/name for name in (CONTEXT,EXTRA,NAV,
        'chapter02-agda-context.js','chapter02-supplementary.js','chapter02-module-navigation-data.js')]
    for prefix in (CODE,RAW,'agda/chapter02/','source-files/chapter02/'):
        folder=(site/prefix).resolve()
        if site.resolve() not in folder.parents: raise ValueError('Unsafe edition directory')
        candidates += [p for p in folder.rglob('*') if p.is_file()]
    for file in candidates:
        if site.resolve() not in file.resolve().parents or file.is_symlink():
            raise ValueError('Unsafe generated edition path')
    for file in candidates: file.unlink(missing_ok=True)


def verify_bundle(bundle):
    receipt=json.loads(read(bundle/'receipt.json'))
    if not receipt.get('checked') or receipt.get('status')!='passed':
        raise ValueError('Chapter compiler export is incomplete')
    if receipt.get('assumption_inventory'):
        inventory=receipt['assumption_inventory']
        if digest((bundle/inventory['path']).read_bytes())!=inventory['sha256']:
            raise ValueError('Chapter assumption inventory changed')
    for source in receipt['sources'].values():
        if digest((bundle/source['path']).read_bytes())!=source['sha256']:
            raise ValueError('Chapter source changed: '+source['path'])
    aggregate=bundle/'src'/Path(*receipt['aggregate'].split('.')).with_suffix('.agda')
    if digest(aggregate.read_bytes())!=receipt['aggregate_sha256']:
        raise ValueError('Chapter import aggregate changed')
    actual={p.name:digest(p.read_bytes()) for p in (bundle/'html').iterdir() if p.is_file()}
    if actual!=receipt['html_sha256']:
        raise ValueError('Chapter compiler output changed')
    return receipt


def chapter_manifest(development='production'):
    if development=='rebuild2':
        return json.loads(read(ROOT/'chapter01-rebuild2-correspondence.json'))
    manifest=copy.deepcopy(json.loads(read(ROOT/'correspondence.json')))
    pages={slug for slug,_,_ in BOOK_CHAPTERS[0]['sections']}
    for key in ('passages','reverse_only'):
        manifest[key]=[p for p in manifest.get(key,[]) if p['page'] in pages]
    for p in manifest['passages']:
        if p['id']=='horizontal-preservation':
            p['declarations']=[d for d in p['declarations'] if d['module']!='Chapter01.Section02.JointPreservation']
            p['note']=('The displayed result proves preservation of identity identifications. '
                       'Joint preservation of composition requires an additional interchange hypothesis '
                       'in the separate JointPreservation investigation; that conditional result is '
                       'outside this Chapter 1 code edition.')
        if p['id']=='core-functoriality':
            p['retained_declarations']=[d for d in p['declarations'] if d['module'].startswith('Chapter02.')]
            p['declarations']=[d for d in p['declarations'] if not d['module'].startswith('Chapter02.')]
            p['note']='Postcomposition is specialized at the terminal source. The separate naturality equation remains available in the retained Chapter 2 code edition.'
    return manifest


def rewrite_links(tree, old, new):
    for node in tree.all():
        for attr in ('href','src'):
            value=node.attrs.get(attr,'')
            if value.startswith(old): node.attrs[attr]=new+value[len(old):]


def body_prose(tree):
    """Compare authored prose independently of replaced code and reader controls."""
    main=next(tree.all('main'))
    clone=parse(main.html())
    for node in list(clone.all()):
        if any(node.has(c) for c in ('agda-panel','agda-help','edition-notice','supplementary-targets')):
            node.replace('')
    return re.sub(r'\s+',' ',clone.text()).strip()


def apply(bundle, site=SITE, *, chapter2_bundle=None):
    from assemble import Agda, page, unique_agda_ids
    from reader_context import build_reader_data
    from supplementary import catalog, module_explanations
    from module_navigation import module_tree, module_label, standalone_navigation
    from validate import validate
    bundle=Path(bundle).resolve()
    receipt=verify_bundle(bundle)
    development=receipt.get('development','production')
    from datetime import datetime
    checked_date=datetime.fromisoformat(receipt['finished_utc']).strftime('%d %B %Y').lstrip('0')
    selection=json.loads(read(bundle/'publication-selection.json'))
    if selection['commit']!=receipt['commit'] or selection['source_hashes']!={n:s['commit_sha256'] for n,s in receipt['sources'].items()}:
        raise ValueError('Publication selection differs from checked export')
    skipped=selection.get('skipped_aggregates',[])
    # Establish the unchanged edition first with the existing full validator.
    if (site/'chapter-edition.json').exists():
        raise ValueError('Apply chapter edition to a freshly assembled baseline')
    baseline=validate(site=site)
    baseline_hashes={p.relative_to(site).as_posix():digest(p.read_bytes()) for p in site.rglob('*') if p.is_file()}
    manifest=chapter_manifest(development)
    correspondence_digest=digest((ROOT/'chapter01-rebuild2-correspondence.json').read_bytes()) if development=='rebuild2' else None
    if development=='rebuild2' and manifest['source_commit']!=receipt['commit']:
        raise ValueError('Correspondences require review for this source revision')
    chapter_notes=[n for n in catalog() if n['chapter']==1]
    notes=[] if development=='rebuild2' else chapter_notes
    combined=copy.deepcopy(manifest)
    for note in notes: combined['passages']+=copy.deepcopy(note['passages'])
    agda=Agda(source_root=bundle/'src',compiler_dir=bundle/'html',href_prefix=CODE,source_prefix=RAW)
    # Missing targets fail here instead of silently dropping formal coverage.
    data=build_reader_data(agda,combined,site,output_path=bundle/'reader.json',asset_name=CONTEXT,retained=False)
    from pilot_model import declaration_range
    retained_agda=Agda()
    for p in manifest['passages']:
        related=[]
        for d in p.get('retained_declarations',[]):
            name,source,pre,_=retained_agda.module(d['module'])
            loc=declaration_range(source,d['name'],d['qualified'])
            related.append({'href':'agda/'+name+'.html#'+str(loc['namepos']+1),
                            'title':d['name']+' (retained Chapter 2 edition)'})
        if related: data['passages'][p['id']]['related_links']=related
    extra={'passages':{},'explanations':{}}
    for note in notes:
        for p in note['passages']:
            data['passages'][p['id']]['supplementary']=True
            for d in data['passages'][p['id']]['declarations']:
                entry={'title':note['title'],'href':note['slug']+'.html#text-'+p['id']}
                entries=extra['explanations'].setdefault(d['module'],[])
                if entry not in entries: entries.append(entry)
    dump(bundle/'reader.json',data)
    write(site/'assets'/CONTEXT,'window.SCT_AGDA = '+json.dumps(data,ensure_ascii=False)+';\n')
    write(site/'assets'/EXTRA,'window.SCT_SUPPLEMENTARY = '+json.dumps(extra,ensure_ascii=False)+';\n')
    version=digest((bundle/'reader.json').read_bytes())[:16]
    notice=('<p class="coverage-note edition-notice">Chapter 1 code: '+escape(development)+' edition, checked '+checked_date+'. '
            '<a href="chapter01-code.html">Included modules and omissions.</a></p>')
    current_pages={p['page'] for p in manifest['passages']}|{n['slug'] for n in notes}
    prose={}
    for slug in sorted(current_pages):
        file=site/(slug+'.html'); tree=parse(read(file)); prose[slug]=body_prose(tree)
        for script in tree.all('script'):
            src=script.attrs.get('src','')
            if src.startswith('assets/agda-context.js'): script.attrs['src']='assets/'+CONTEXT+'?v='+version
            if src.startswith('assets/supplementary.js'): script.attrs['src']='assets/'+EXTRA+'?v='+version
        ids={n.attrs['id']:n for n in tree.all() if 'id' in n.attrs}
        for p in manifest['passages']:
            if p['page']!=slug: continue
            ids['agda-'+p['id']].replace(agda.panel(p))
        # Supplementary statements keep their prose and use new exact anchors.
        note=next((n for n in notes if n['slug']==slug),None)
        if note:
            for p in note['passages']:
                ds=data['passages'][p['id']]['declarations']
                ids['agda-'+p['id']].replace('<li id="agda-'+p['id']+'">'+escape(p['title'])+': '+', '.join(
                    '<a href="'+d['href']+'"><code>'+escape(d['qualified'])+'</code></a>' for d in ds)+'</li>')
        for link in tree.all('a'):
            if link.has('agda-start'):
                module=link.attrs['data-module']
                if module not in data['modules']: raise ValueError('Omitted reader entry: '+module)
                link.attrs['href']=CODE+module+'.html'
        main=next(tree.all('main')); addition=parse(notice).children[0]
        addition.parent=main; main.children.insert(0,addition)
        if body_prose(tree)!=prose[slug]: raise ValueError('Book/note prose changed: '+slug)
        write(file,'<!doctype html>\n'+tree.html())
    if development=='rebuild2':
        # These explanations describe historical implementation routes. Keep
        # their own checked links until their prose is reviewed for the redesign.
        for note in chapter_notes:
            slug=note['slug']; file=site/(slug+'.html'); tree=parse(read(file))
            prose[slug]=body_prose(tree); current_pages.add(slug)
            main=next(tree.all('main'))
            addition=parse('<p class="coverage-note edition-notice">This supplementary note and its code links describe the earlier formalization. Its proof explanation has not been migrated to rebuild2. <a href="chapter01-code.html">Browse the current Chapter 1 code.</a></p>').children[0]
            addition.parent=main; main.children.insert(0,addition)
            write(file,'<!doctype html>\n'+tree.html())
    names=set(data['modules'])
    # Module browsing can open later chapters in their retained edition. Symbol
    # links still stay strictly inside the compiler bundle that produced them.
    later={p.stem for p in (BUILD/'agda').glob('SCT.VolumeI.Chapter*.html')
           if not p.stem.startswith('SCT.VolumeI.Chapter01.')}
    browse=names|later
    nav={'tree':module_tree(browse),'labels':{n:module_label(n) for n in sorted(browse)},
         'hrefs':{n:('' if n in names else '../')+n+'.html' for n in browse}}
    write(site/'assets'/NAV,'window.SCT_MODULE_NAVIGATION = '+json.dumps(nav,ensure_ascii=False)+';\n')
    symbols=[]
    for compiler in sorted((bundle/'html').glob('*.html')):
        name=compiler.stem
        pre=next(parse(read(compiler)).all('pre')); unique_agda_ids(pre)
        if name.startswith('SCT.VolumeI.Chapter01.'):
            for anchor in pre.all('a'):
                identifier=anchor.attrs.get('id','')
                definition=(identifier.isdigit() and anchor.attrs.get('href')==compiler.name+'#'+identifier
                            and any(anchor.has(c) for c in ('Postulate','Function','Record','Datatype','Field','InductiveConstructor','CoinductiveConstructor')))
                if (development=='rebuild2' and definition) or (development!='rebuild2' and identifier and not identifier.isdigit()):
                    label=anchor.text() if development=='rebuild2' else identifier
                    symbols.append('<li class="symbol-entry"><a href="'+CODE+compiler.name+'#'+quote(identifier)+'"><code>'+escape(name+'.'+label)+'</code></a></li>')
        linked=[p for p in combined['passages']+combined.get('reverse_only',[])
                if any('SCT.VolumeI.'+d['module']==name for d in p['declarations'])]
        back=('<details class="module-book-passages"><summary>Corresponding book passages</summary><ul>'+''.join(
            '<li><a href="../../'+p['page']+'.html#text-'+p['id']+'">'+escape(p['title'])+'</a></li>' for p in linked)+'</ul></details>') if linked else ''
        navigation=standalone_navigation(name,names).replace('href="../code-index.html"','href="../../code-index.html"')
        content=navigation+'<p class="coverage-note">Chapter 1, '+escape(development)+', checked '+checked_date+' · source revision <code>'+receipt['commit'][:7]+'</code>.</p>'
        content+=module_explanations(name,extra,'../../')+back+pre.html()
        rendered=page(name,content,math=False,prefix='../../')
        rendered=re.sub(r'assets/module-navigation-data.js\?v=[^"]+', 'assets/'+NAV+'?v='+version, rendered)
        write(site/CODE/compiler.name,rendered)
    for name,source in receipt['sources'].items():
        target=site/RAW/Path(source['path']).relative_to('src')
        target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes((bundle/source['path']).read_bytes())
    # Include the generated aggregate's exact source, too.
    aggregate=receipt['aggregate']; relative=Path(*aggregate.split('.')).with_suffix('.agda')
    target=site/RAW/relative; target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes((bundle/'src'/relative).read_bytes())
    def group(node):
        inside=''.join('<article class="code-index-entry" data-module="'+n+'"><h3><a href="'+CODE+n+'.html">'+
            escape(module_label(n))+'</a></h3><p class="module-qualified">'+escape(n)+'</p></article>' for n in node['modules'])
        inside+=''.join(group(child) for child in node['children'])
        return ('<details class="module-group" data-module-group="'+node['key']+'"><summary>'+escape(node['label'])+'</summary><div class="module-group-content">'+inside+'</div></details>') if node['key'] else inside
    groups=group(module_tree(names))
    summary=('<p>'+str(len(receipt['sources']))+' source modules are included from <code>'+escape(receipt.get('repository_source_root','src'))+'</code> at revision <code>'+receipt['commit'][:7]+
             '</code>. Their compiler-highlighted output was generated after a successful check on '+checked_date+'. Chapters 2–3 retain their earlier checked edition.</p>')
    if development=='rebuild2':
        summary+='<p>The current Chapter 1 code includes the categories-over-a-base modules in Section 1.9; that manuscript section is not yet rendered here. The supplementary notes retain explicitly labelled links to the earlier implementation.</p><h2>Mathematical scope</h2><p>The ambient primitive assumptions are declared in the code. General closure of <code>isAn</code> under equivalence is neither assumed nor proved. The functor-category pushout criterion uses the specified evaluation-based cone; agreement with the older matching construction is not claimed.</p>'
    exclusions='<h2>Publication selection</h2><p>'+('The following source modules are excluded:' if receipt['excluded_modules'] else 'No mathematical Chapter 1 modules are excluded from this committed selection.')+'</p><ul>'+''.join('<li><code>'+escape(n)+'</code></li>' for n in receipt['excluded_modules'])+'</ul>'
    if skipped:
        exclusions+='<details><summary>'+str(len(skipped))+' import-only section summaries</summary><p>The selected proof modules are checked directly; these import-only summary files are not needed in this edition.</p><ul>'+''.join('<li><code>'+escape(n)+'</code></li>' for n in skipped)+'</ul></details>'
    if development=='rebuild2':
        if receipt['excluded_modules']:
            raise ValueError('Review the authored Chapter 1 publication text before excluding modules')
        summary=rebuild2_code_introduction(checked_date)
        exclusions=''
    write(site/'chapter01-code.html',page('Chapter 1 Agda code',summary+exclusions+'<h2>Modules</h2>'+groups,'code-index',math=False))
    # Main index points Chapter 1 readers to the new edition. Old pages remain
    # intact for symbol links from the later chapters' compiler output.
    tree=parse(read(site/'code-index.html'))
    for node in list(tree.all('details')):
        if node.attrs.get('data-module-group')=='SCT.VolumeI.Chapter01':
            chapter_group=next(c for c in module_tree(names)['children'] if c['key']=='SCT.VolumeI.Chapter01')
            node.replace(group(chapter_group))
    index_main=next(tree.all('main')); addition=parse('<p class="coverage-note">Chapter 1 has a newer checked edition. <a href="chapter01-code.html">Read its scope and omission list.</a> Later chapters and their supporting dependency pages retain the earlier checked code.</p>').children[0]
    addition.parent=index_main; index_main.children.insert(0,addition)
    # The old flat declaration index must not offer stale Chapter 1 offsets as
    # the main route. Retained pages remain reachable from the later code.
    for entry in list(tree.all('li')):
        if entry.has('symbol-entry') and 'SCT.VolumeI.Chapter01.' in entry.text(): entry.replace('')
    symbol_index=next(n for n in tree.all('details') if n.has('symbol-index'))
    symbol_list=next(symbol_index.all('ul'))
    for child in parse(''.join(symbols)).children:
        child.parent=symbol_list; symbol_list.children.append(child)
    for p in list(tree.all('p')):
        if 'source modules included in the recorded aggregate check.' in p.text():
            p.replace('<p>Chapter 1 uses its current checked selection; Chapters 2–3 and their dependency pages retain the earlier checked edition.</p>')
    write(site/'code-index.html','<!doctype html>\n'+tree.html())
    public={'chapter':1,'commit':receipt['commit'],'checked_utc':receipt['finished_utc'],
            'development':development,'repository_source_root':receipt.get('repository_source_root','src'),
            'assumption_inventory_sha256':receipt.get('assumption_inventory',{}).get('sha256'),
            'source_modules':sorted(set(receipt['sources'])|{aggregate}),
            'compiled_modules':sorted(names),'excluded_modules':receipt['excluded_modules'],
            'skipped_aggregates':skipped,
            'code_prefix':CODE,'source_prefix':RAW,'pages':sorted(current_pages),
            'retained_chapters':[2,3],
            'retained_supplementary_pages':[n['slug'] for n in chapter_notes] if development=='rebuild2' else []}
    dump(site/'chapter-edition.json',public)
    if chapter2_bundle is None and CONFIG.exists():
        configured=json.loads(read(CONFIG)).get('chapter2_bundle')
        if configured: chapter2_bundle=ROOT/configured
    second=None
    if chapter2_bundle:
        from chapter02_edition import apply as apply_chapter2
        second=apply_chapter2(chapter2_bundle,site)
        public['retained_chapters']=[3]
        public['additional_editions']=[second['public']]
        dump(site/'chapter-edition.json',public)
    info=json.loads(read(site/'build-info.json')); info['chapter_editions']=[public]+([second['public']] if second else []); dump(site/'build-info.json',info)
    hashes={p.relative_to(site).as_posix():digest(p.read_bytes()) for p in site.rglob('*') if p.is_file() and p.name!='validation.json'}
    report={'bundle':str(bundle),'baseline':baseline,'baseline_hashes':baseline_hashes,'files':hashes,
            'prose':prose,'reader_sha256':digest((bundle/'reader.json').read_bytes()),
            'inputs_sha256':digest((BUILD/'build-info.json').read_bytes()),
            'correspondence_sha256':digest((ROOT/'correspondence.json').read_bytes())}
    if development=='rebuild2':
        if chapter_manifest(development)!=manifest:
            raise ValueError('Correspondences changed during assembly; rebuild the stage')
        report['rebuild2_correspondence_sha256']=correspondence_digest
    if second: report['chapter2']=second
    dump(REPORT,report)
    if development=='rebuild2':
        apply_availability(site)
    return validate_overlay(site)


def apply_availability(site):
    """Apply the temporary chapter policy to an otherwise validated edition."""
    from chapter_availability import suspend, DISABLED_CHAPTERS
    report=json.loads(read(REPORT))
    actual={p.relative_to(site).as_posix():digest(p.read_bytes()) for p in site.rglob('*') if p.is_file() and p.name!='validation.json'}
    if actual!=report['files']:
        raise ValueError('Edition changed before availability update')
    if report.get('availability_files'):
        raise ValueError('Availability policy already applied; reassemble before changing it')
    enabled=(2,) if report.get('chapter2') else ()
    prose,changed=suspend(site,enabled=enabled)
    report['prose'].update(prose)
    report['availability_files']=changed
    info=json.loads(read(site/'chapter-edition.json'))
    info['disabled_chapters']=[n for n in DISABLED_CHAPTERS if n not in enabled]
    dump(site/'chapter-edition.json',info)
    build=json.loads(read(site/'build-info.json')); build['chapter_editions']=[info]+info.get('additional_editions',[])
    dump(site/'build-info.json',build)
    report['files']={p.relative_to(site).as_posix():digest(p.read_bytes()) for p in site.rglob('*') if p.is_file() and p.name!='validation.json'}
    dump(REPORT,report)


def validate_overlay(site=SITE):
    """Validate the new bundle and every local URL without recertifying old code."""
    from reader_context import module_lines, compiler_anchors
    from check_site_boundary import check
    report=json.loads(read(REPORT)); bundle=Path(report['bundle']); receipt=verify_bundle(bundle)
    if report['baseline']['status']!='passed': raise ValueError('Retained edition lacked validation')
    if digest((BUILD/'build-info.json').read_bytes())!=report['inputs_sha256'] or digest((ROOT/'correspondence.json').read_bytes())!=report['correspondence_sha256']:
        raise ValueError('Edition inputs changed; reassemble')
    if report.get('rebuild2_correspondence_sha256') and digest((ROOT/'chapter01-rebuild2-correspondence.json').read_bytes())!=report['rebuild2_correspondence_sha256']:
        raise ValueError('Rebuild2 correspondences changed; reassemble')
    from checked_code import verify_checked_code
    verify_checked_code(json.loads(read(SNAP/'inputs.json')))
    actual={p.relative_to(site).as_posix():digest(p.read_bytes()) for p in site.rglob('*') if p.is_file() and p.name!='validation.json'}
    if actual!=report['files']: raise ValueError('Generated edition changed; reassemble')
    info=json.loads(read(site/'chapter-edition.json'))
    if info.get('disabled_chapters'):
        from chapter_availability import validate_suspension
        validate_suspension(site,report['availability_files'])
    # Preserve retained compiler bytes. The availability policy may remove
    # controls and filter navigation, while separately checking prose equality.
    changed=set(info['pages'])|{'code-index'}
    for name,sha in report['baseline_hashes'].items():
        if name in {'build-info.json','validation.json'} or name in {s+'.html' for s in changed}: continue
        if name in report.get('availability_files',[]): continue
        if name in report.get('chapter2',{}).get('changed',[]): continue
        if actual.get(name)!=sha: raise ValueError('Retained edition artifact changed: '+name)
    trees={p:parse(read(p)) for p in site.rglob('*.html')}; ids={}
    for file,tree in trees.items():
        values=[n.attrs['id'] for n in tree.all() if 'id' in n.attrs]
        if any(n>1 for n in Counter(values).values()): raise ValueError('Duplicate HTML IDs: '+file.name)
        ids[file.resolve()]=set(values)
    links=0; targets={}
    def link(base,href):
        nonlocal links
        url=urlsplit(href)
        if url.scheme or url.netloc: return
        key=(base.parent if url.path else base,url.path)
        if key not in targets:
            target=(base.parent/unquote(url.path)).resolve() if url.path else base.resolve()
            if site.resolve() not in target.parents or not target.exists(): raise ValueError('Broken/escaping link: '+href)
            targets[key]=target
        target=targets[key]
        if target.suffix=='.html' and url.fragment and unquote(url.fragment) not in ids[target]:
            raise ValueError('Missing fragment: '+str(base)+': '+href)
        links+=1
    for file,tree in trees.items():
        for node in tree.all():
            for attr in ('href','src'):
                if node.attrs.get(attr): link(file,node.attrs[attr])
    data=json.loads(read(bundle/'reader.json'))
    if digest((bundle/'reader.json').read_bytes())!=report['reader_sha256']: raise ValueError('Reader metadata changed')
    if receipt.get('development')=='rebuild2':
        manifest=chapter_manifest('rebuild2')
        for p in manifest['passages']+manifest.get('reverse_only',[]):
            shown=data['passages'][p['id']]
            expected=[('SCT.VolumeI.'+d['module'],d['qualified'],d['role']) for d in p['declarations']]
            if [(d['module'],d['qualified'],d['role']) for d in shown['declarations']]!=expected or shown['note']!=p['note']:
                raise ValueError('Stale rebuild2 passage: '+p['id'])
    for name,payload in data['modules'].items():
        pre=next(parse(read(bundle/'html'/(name+'.html'))).all('pre')); text=pre.text()
        displayed=next(trees[site/CODE/(name+'.html')].all('pre'))
        if displayed.text()!=text: raise ValueError('Displayed compiler source changed: '+name)
        expected=module_lines(text,pre,CODE)
        if [(l['number'],l['html']) for l in payload['lines']]!=[(l['number'],l['html']) for l in expected]:
            raise ValueError('Reader source differs: '+name)
        if payload['anchors']!=compiler_anchors(pre,{l['number'] for l in expected}): raise ValueError('Reader anchors differ')
        for line in payload['lines']:
            for anchor in parse(line['html']).all('a'):
                if anchor.attrs.get('href'): link(site/'basic-vocabulary.html',anchor.attrs['href'])
    for p in data['passages'].values():
        for d in p['declarations']: link(site/(p['page']+'.html'),d['href'])
    for slug,text in report['prose'].items():
        if body_prose(trees[site/(slug+'.html')])!=text: raise ValueError('Book prose changed')
    chapter2=None
    if report.get('chapter2'):
        from chapter02_edition import validate as validate_chapter2
        chapter2=validate_chapter2(report['chapter2'],site,trees,link)
    check(site)
    result={'status':'passed','html_pages':len(trees),'local_links_checked':links,
            'chapter_1_source_modules':len(receipt['sources']),'chapter_1_omissions':len(receipt['excluded_modules']),
            'chapter_1_commit':receipt['commit'],'retained_chapters':info['retained_chapters'],
            'disabled_chapters':info.get('disabled_chapters',[]),
            'baseline_validation':report['baseline']}
    if chapter2: result['chapter_2']=chapter2
    dump(site/'validation.json',result)
    return result


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(); parser.add_argument('--bundle',required=True,type=Path)
    parser.add_argument('--site',type=Path,default=SITE)
    args=parser.parse_args(); print(json.dumps(apply(args.bundle,args.site)))
