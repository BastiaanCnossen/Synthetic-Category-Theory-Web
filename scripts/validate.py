"""Check joined artifacts, exact snippets, local links, counters and provenance."""
from common import *
from urllib.parse import urlsplit, unquote
from collections import Counter

def require(condition,message):
    if not condition: raise ValueError(message)

def validate_tex_log(path):
    # TeX's font diagnostics can contain raw font-encoding bytes. The
    # reference/citation diagnostics we check are ASCII in every encoding.
    text=Path(path).read_bytes()
    require(not re.search(rb'LaTeX Warning: (?:Reference|Citation).*undefined|There were undefined references',text),f'Unresolved LaTeX reference: {Path(path).name}')


def validate(site=SITE):
    info=json.loads(read(BUILD/'build-info.json'))
    require(info['correspondence_hash']==digest((ROOT/'correspondence.json').read_bytes()),'Correspondence changed since assembly; rebuild the pilot')
    for rel,sha in info['inputs']['files'].items():
        require(digest((SNAP/rel).read_bytes())==sha,'Snapshot changed: '+rel)
    files=list(site.rglob('*.html'))
    trees={p:parse(read(p)) for p in files}
    for opening in BOOK_FRONTMATTER:
        tree=trees.get(site/(opening['slug']+'.html'))
        require(tree is not None,'Missing opening page: '+opening['slug'])
        require(not any(n.has('agda-panel') or n.has('agda-trigger') or n.has('agda-help') for n in tree.all()),
                'Unexpected Agda correspondence on opening page: '+opening['slug'])
    id_sets={}
    for chapter in BOOK_CHAPTERS:
        for slug in [chapter['slug']]+[s[0] for s in chapter['sections']]:
            tree=trees[site/(slug+'.html')]
            turns=next(n for n in tree.all('nav') if n.has('page-turns'))
            controls=[n for n in turns.all() if 'data-step' in n.attrs]
            require([n.attrs['data-step'] for n in controls]==['prev-chapter','next-chapter','prev-section','next-section'],
                    'Missing or reordered navigation controls: '+slug)
            trail=next(n for n in tree.all('nav') if n.has('book-breadcrumbs'))
            expected=['index.html']+([chapter['slug']+'.html'] if slug!=chapter['slug'] else [])
            require([a.attrs['href'] for a in trail.all('a')]==expected,'Breadcrumb ancestry differs: '+slug)
        landing=trees[site/(chapter['slug']+'.html')]
        cards=next(n for n in landing.all('section') if n.has('available-sections'))
        require([a.attrs['href'] for a in cards.all('a') if a.parent.tag=='h3']==[s[0]+'.html' for s in chapter['sections']],
                'Chapter cards omit or reorder sections: '+chapter['slug'])
    for file,tree in trees.items():
        require(next(tree.all('body')).has('hide-agda-links'),'Agda links must default to hidden: '+file.name)
        tools=next(n for n in tree.all('aside') if n.has('utility-dock'))
        preferences=list(tools.all('input'))
        require([n.attrs.get('id') for n in preferences]==['collapse-proofs','show-agda-links'] and
                all('checked' not in n.attrs for n in preferences),'Unexpected default reading preferences: '+file.name)
        require('hidden' in next(tools.all('section')).attrs,'Settings panel open by default: '+file.name)
        sidebar=next(n for n in tree.all('aside') if n.has('reader-nav'))
        require(not any(isinstance(n,Node) and n.tag=='details' for n in sidebar.children),
                'Contents still wrapped in a disclosure: '+file.name)
        require([n.text() for n in sidebar.all('h2')]==['Resources','Contents'],
                'Resources must precede Contents: '+file.name)
        ids=[n.attrs['id'] for n in tree.all() if 'id' in n.attrs]
        require(all(not any(c.isspace() for c in identifier) for identifier in ids),
                f'Whitespace in HTML ID: {file.name}')
        duplicates=[x for x,c in Counter(ids).items() if c>1]
        require(not duplicates,f'Duplicate IDs in {file.name}: {duplicates[:5]}')
        id_sets[file.resolve()]=set(ids)
        require(not re.search(r'(?<!\?)\?\?(?!\?)',tree.text()),f'Unresolved reference in {file.name}')
        for n in tree.all():
            resource=n.attrs.get('src') if n.tag in ('script','img') else n.attrs.get('href') if n.tag=='link' and n.attrs.get('rel')=='stylesheet' else None
            if resource:
                url=urlsplit(resource)
                require(not url.scheme and not url.netloc,f'External runtime resource: {resource}')
    links=0; targets={}
    for file,tree in trees.items():
        for n in tree.all():
            for attr in ('href','src'):
                href=n.attrs.get(attr)
                if not href: continue
                url=urlsplit(href)
                if url.scheme or url.netloc: continue
                key=(file.parent,url.path)
                if key not in targets:
                    target=(file.parent/unquote(url.path)).resolve() if url.path else file.resolve()
                    require(site.resolve() in target.parents or target==site.resolve(),f'Link leaves distribution: {file.name}: {href}')
                    require(target.exists(),f'Missing file: {file.name}: {href}')
                    targets[key]=target
                target=targets[key]
                if url.fragment and target.suffix=='.html':
                    if target not in id_sets: id_sets[target]={a.attrs['id'] for a in parse(read(target)).all() if 'id' in a.attrs}
                    require(unquote(url.fragment) in id_sets[target],f'Missing fragment: {file.name}: {href}')
                links+=1
    from checked_code import publication_manifest, verify_checked_code
    verify_checked_code(info['inputs'])
    manifest=publication_manifest()
    panels=[n for p,t in trees.items() if p.parent==site for n in t.all('details') if n.has('agda-panel')]
    require(len(panels)==len(manifest['passages']),'Panel count mismatch')
    require(all('open' not in n.attrs for n in panels),'Agda panel open by default')
    source=comments(read(BUILD/'selected-source.tex'))
    underlined=set(re.findall(r'\\newtheorem\*?\{(u[^}]+)\}',read(SNAP/'preamble.tex')))
    expected=sum(env in underlined for env in re.findall(r'\\begin\{([^}]+)\}',source))
    actual=sum(1 for p,t in trees.items() if p.parent==site for n in t.all('section') if n.attrs.get('data-scope')=='categorical')
    require(actual==expected,f'Underlined statement count changed: {actual} vs {expected}')
    # The actual PDF and HTML LaTeX jobs must agree on numbered labels.
    def counters(file):
        return {m[1]:(m[2].split(']')[0],m[2].split(']')[-1]) for m in re.finditer(r'\\newlabel\{([^}]+)@cref\}\{\{([^}]+)\}',read(file))}
    pdf=counters(BUILD/'pilot-pdf.aux'); html=counters(BUILD/'pilot.aux')
    # Unnumbered subsubsections and the unlabeled framed principle inherit an
    # incidental previous counter differently between classes. They retain
    # stable source anchors, but have no number of their own to compare.
    for label in ('sec:Products_Of_Categories','sec:Products_And_Coproducts_Of_Categories',
                  'sec:Unitality_And_Associativity','ref:Fundamental_Principle_Higher_Category_Theory'):
        pdf.pop(label,None); html.pop(label,None)
    require(pdf==html,'PDF and HTML theorem/reference counters differ')
    for log in ('pilot.log','pilot-pdf.log'):
        validate_tex_log(BUILD/log)
    # Signatures and proofs must equal slices of the exact compiled source.
    from pilot_model import declaration_range, tex_markers
    declarations=[n for p,t in trees.items() if p.parent==site for n in t.all('section') if n.has('agda-declaration')]
    require(len(declarations)==len(info['passages']),'Declaration count mismatch')
    resolved={(entry['module'],entry['declaration']):entry for entry in info['passages']}
    for node in declarations:
        key=(node.attrs.get('data-module'),node.attrs.get('data-declaration'))
        require(key in resolved,'Unresolved snippet identity: '+str(key))
        entry=resolved[key]
        src=SNAP/'agda/src'/Path(*entry['module'].split('.')).with_suffix('.lagda.md')
        text=read(src); name=entry['declaration'].split('.')[-1]
        loc=declaration_range(text,name,entry['declaration'])
        start,proof,end=loc['start'],loc['proof'],loc['end']
        if loc['kind']=='record': proof=None
        signature=next(n for n in node.all('pre') if n.has('signature'))
        require(signature.text().rstrip()==text[start:proof if proof is not None else end].rstrip(),f'Signature differs: {name}')
        if proof is not None:
            impl=next(n for n in node.all('details') if n.has('agda-proof'))
            require(next(impl.all('pre')).text()==text[proof:end],f'Implementation differs: {name}')
    markers=[]
    markers=tex_markers(read(BUILD/'selected-source.tex'),registry=manifest)[1]
    require(set(markers)=={p['id'] for p in manifest['passages']+manifest.get('reverse_only',[])},'TeX/registry mismatch')
    for p in manifest['passages']+manifest.get('reverse_only',[]):
        require('text-'+p['id'] in id_sets[(site/(p['page']+'.html')).resolve()],'Missing phrase marker: '+p['id'])
        marker=next(n for n in trees[site/(p['page']+'.html')].all() if n.attrs.get('id')=='text-'+p['id'])
        if p in manifest.get('reverse_only',[]):
            require(marker.tag=='span' and marker.has('agda-book-anchor') and 'href' not in marker.attrs and 'data-agda' not in marker.attrs and marker.attrs.get('tabindex')=='-1','Reverse-only marker must be noninteractive and focusable')
        else: require(marker.tag=='a' and marker.has('agda-trigger'),'Forward marker must remain clickable')
        for d in p['declarations']:
            module=manifest['module_prefix']+d['module']
            src=SNAP/'agda/src'/Path(*module.split('.')).with_suffix('.lagda.md')
            text=read(src); loc=declaration_range(text,d['name'],d['qualified'])
            module_tree=trees[site/'agda'/(module+'.html')]
            require(any(n.attrs.get('href')=='../'+p['page']+'.html#text-'+p['id'] for n in module_tree.all('a')),'Missing generated module backlink: '+p['id'])
    require({e['module'] for e in info['source_inventory']}=={p.stem for p in (BUILD/'agda').glob('SCT.*.html')},'Published source inventory differs from checked SCT modules')
    from reader_context import focused_lines
    reader=json.loads(read(BUILD/'agda-context.json'))
    from book_navigation import AGDA_ENTRY_MODULES
    for slug,module in AGDA_ENTRY_MODULES.items():
        tree=trees[site/(slug+'.html')]
        entry=next(n for n in tree.all('a') if n.has('agda-start'))
        require(entry.attrs['data-module']=='SCT.VolumeI.'+module and
                entry.attrs['data-module'] in reader['modules'],'Unavailable reader entry module: '+slug)
        require(any(n.has('agda-trigger') for n in tree.all()),'Agda invitation without passage links: '+slug)
    source_targets={}
    require(read(site/'assets/agda-context.js')=='window.SCT_AGDA = '+json.dumps(reader,ensure_ascii=False)+';\n','Side-reader script/data differ')
    require(set(reader['passages'])=={p['id'] for p in manifest['passages']+manifest.get('reverse_only',[])},'Side-reader passage coverage differs')
    expected_modules={entry['module'] for entry in info['source_inventory']} | {file.stem for file in (BUILD/'agda').glob('*.html')}
    require(set(reader['modules'])==expected_modules,'Module browser omits a source module')
    from module_navigation import module_tree
    from checked_code import verify_checked_code
    retained=verify_checked_code(json.loads(read(SNAP/'inputs.json')))=='updated manuscript with previously checked Agda snapshot'
    require(reader['module_tree']==module_tree(expected_modules,retained=retained),'Reader chapter/section navigation differs from module inventory')
    def navigation_modules(node):
        return node['modules']+[module for child in node['children'] for module in navigation_modules(child)]
    require(sorted(navigation_modules(reader['module_tree']))==sorted(expected_modules),'Module hierarchy drops or duplicates a module')
    index_modules=[node.attrs['data-module'] for node in trees[site/'code-index.html'].all('article') if node.has('code-index-entry')]
    require(sorted(index_modules)==sorted(expected_modules),'Code index drops or duplicates a module')
    expected_groups={}
    def collect_groups(node, parents=()):
        ancestors=parents+(node['key'],) if node['key'] else parents
        for module in node['modules']: expected_groups[module]=ancestors
        for child in node['children']: collect_groups(child,ancestors)
    collect_groups(reader['module_tree'])
    for entry in trees[site/'code-index.html'].all('article'):
        if not entry.has('code-index-entry'): continue
        ancestors=[]; parent=entry.parent
        while parent is not None:
            if parent.has('module-group'): ancestors.insert(0,parent.attrs.get('data-module-group'))
            parent=parent.parent
        require(tuple(ancestors)==expected_groups[entry.attrs['data-module']],
                'Code index places module in wrong folder: '+entry.attrs['data-module'])
    for module,payload in reader['modules'].items():
        src=SNAP/'agda/src'/Path(*module.split('.')).with_suffix('.lagda.md')
        if not src.exists(): src=src.with_suffix('').with_suffix('.agda')
        compiled_file=BUILD/'agda'/(module+'.html')
        require(payload['checked']==compiled_file.exists(),'Incorrect reader module check status')
        compiled=next(parse(read(compiled_file) if payload['checked'] else '<pre>'+escape(read(src))+'</pre>').all('pre'))
        text=read(src) if src.exists() else compiled.text()
        require(text==compiled.text(),'Reader source differs from checked compiler output')
        lines=text.split('\n')
        require(digest(text)==payload['source_sha256'],'Side-reader source changed')
        require(payload['href']==('agda/' if payload['checked'] else 'source/')+module+'.html','Incorrect module browser link')
        from reader_context import compiler_anchors
        require(payload['anchors']==compiler_anchors(compiled,{line['number'] for line in payload['lines']}),'Definition anchor index differs')
        for line in payload['lines']:
            expected_targets={}
            for pid,p in reader['passages'].items():
                for d in p['declarations']:
                    if d['module']==module and line['number'] in d['range']:
                        focused=line['number'] in d['focus']
                        rank=[0 if p['reverse_only'] else 1 if focused else 2,len(d['focus']) if focused else len(d['range'])]
                        if pid not in expected_targets or rank<expected_targets[pid]: expected_targets[pid]=rank
            require({t['id']:t['rank'] for t in line['targets']}==expected_targets,'Reverse line correspondence differs')
            fragment=parse(line['html'])
            require(fragment.text()==lines[line['number']-1],'Side-reader line differs from compiler source')
            for anchor in fragment.all('a'):
                href=anchor.attrs.get('href')
                if href:
                    url=urlsplit(href)
                    if url.path not in source_targets: source_targets[url.path]=(site/unquote(url.path)).resolve()
                    target=source_targets[url.path]
                    require(target in id_sets and (not url.fragment or unquote(url.fragment) in id_sets[target]),'Broken side-reader symbol link: '+href)
                    destination=Path(unquote(url.path)).stem
                    require(destination in reader['modules'],'Definition module unavailable in reader')
                    require(not url.fragment or unquote(url.fragment) in reader['modules'][destination]['anchors'],'Definition anchor unavailable in reader')
    for passage in manifest['passages']+manifest.get('reverse_only',[]):
        payload=reader['passages'][passage['id']]
        require(payload['page']==passage['page'] and payload['reverse_only']==(passage in manifest.get('reverse_only',[])),'Reverse passage metadata differs')
        mapped=payload['declarations']
        require(len(mapped)==len(passage['declarations']),'Side-reader declaration count differs')
        for d,shown in zip(passage['declarations'],mapped):
            module=manifest['module_prefix']+d['module']
            text=read(SNAP/'agda/src'/Path(*module.split('.')).with_suffix('.lagda.md'))
            loc=declaration_range(text,d['name'],d['qualified'])
            require(shown['module']==module and shown['qualified']==d['qualified'],'Side-reader declaration identity differs')
            require(shown['range']==list(range(text.count('\n',0,loc['start'])+1,text.count('\n',0,loc['end']-1)+2)),'Reverse declaration range differs')
            available={line['number'] for line in reader['modules'][module]['lines']}
            require(shown['focus']==[line for line in focused_lines(text,loc,d) if line in available],'Incorrect side-reader focus')
    validate_distribution(info,site=site)
    from check_site_boundary import check
    check(site)
    report={'status':'passed','html_pages':len(files),'local_links_checked':links,'passage_panels':len(panels),'declaration_mappings':len(declarations),'reverse_only_passages':len(manifest.get('reverse_only',[])),'underlined_statements':actual,'pdf_html_counters':len(pdf),'input_hashes':len(info['inputs']['files']),'source_modules':len(info['source_inventory']),'omitted_source_modules':sum(1 for p in (SNAP/'agda/src').rglob('*') if p.suffix=='.agda' or p.name.endswith('.lagda.md'))-len(info['source_inventory'])}
    dump(site/'validation.json',report); print(json.dumps(report))

def validate_distribution(info,site=SITE):
    """The only publishable tree must not contain private inputs or excess code."""
    checked={e['source'] for e in info['source_inventory']}
    published={p.relative_to(site/'source-files').as_posix() for p in (site/'source-files').rglob('*') if p.is_file()}
    require(published==checked,'Raw source distribution differs from checked module selection')
    for file in site.rglob('*'):
        if not file.is_file(): continue
        relative=file.relative_to(site)
        require(relative.parts[0] not in ('snapshot','pilot','_build','scripts','docs'),'Private/build directory in distribution: '+str(relative))
        require(file.suffix not in ('.tex','.aux','.log','.bbl','.bib','.agdai','.toml','.ps1','.py'),'Build or manuscript file in distribution: '+str(relative))
        if file.suffix in ('.html','.js','.json','.css') and 'vendor' not in relative.parts:
            text=read(file)
            for private in ('C:/Users/','C:\\Users\\','Volume I - Synthetic Category Theory/','snapshot/','pilot/tex/','_build/'):
                require(private not in text,'Private path exposed in '+str(relative)+': '+private)
    return len(checked)

if __name__=='__main__': validate()
