"""Add a separately verified rebuild2 Chapter 2 bundle to the chapter overlay.

Compiler links stay inside the bundle which generated them, including its
Chapter 1 dependencies. The existing Chapter 1 edition is not recertified.
"""
from common import *
from urllib.parse import quote
import copy

CODE = 'agda/chapter02/'
RAW = 'source-files/chapter02/'
CONTEXT = 'chapter02-agda-context.js'
EXTRA = 'chapter02-supplementary.js'
NAV = 'chapter02-module-navigation-data.js'
MANIFEST_PATH = ROOT/'chapter02-rebuild2-correspondence.json'


def manifest():
    return json.loads(read(MANIFEST_PATH))


def apply(bundle, site):
    from chapter_edition import verify_bundle, body_prose
    from assemble import Agda, page, unique_agda_ids
    from reader_context import build_reader_data
    from module_navigation import module_tree, module_label, standalone_navigation
    bundle=Path(bundle).resolve(); receipt=verify_bundle(bundle)
    selected=json.loads(read(bundle/'publication-selection.json'))
    registry=manifest()
    if receipt.get('development')!='rebuild2' or receipt.get('chapter')!=2:
        raise ValueError('Expected a rebuild2 Chapter 2 compiler bundle')
    if registry['source_commit']!=receipt['commit'] or selected['commit']!=receipt['commit']:
        raise ValueError('Chapter 2 mappings require review at this revision')
    if selected['source_hashes']!={n:s['commit_sha256'] for n,s in receipt['sources'].items()}:
        raise ValueError('Chapter 2 selection differs from the checked sources')
    agda=Agda(source_root=bundle/'src',compiler_dir=bundle/'html',href_prefix=CODE,source_prefix=RAW)
    data=build_reader_data(agda,registry,site,output_path=bundle/'reader.json',asset_name=CONTEXT,retained=False)
    write(site/'assets'/EXTRA,'window.SCT_SUPPLEMENTARY = {"passages":{},"explanations":{}};\n')
    version=digest((bundle/'reader.json').read_bytes())[:16]
    passages=registry['passages']+registry.get('reverse_only',[])
    pages={p['page'] for p in passages}; prose={}; changed=set()
    entry={
        'morphisms-and-diagrams':'Chapter02.Section01.Morphisms',
        'segal-axiom':'Chapter02.Section02.SegalAxiom',
        'rezk-axiom':'Chapter02.Section03.RezkAxiom',
        'groupoids':'Chapter02.Section04.Groupoids',
        'recognizing-animae':'Chapter02.Section05.Recognition',
        'chapter-2-exercises':'Chapter02.Section06.HomIsomorphisms',
    }
    for slug in sorted(pages):
        file=site/(slug+'.html'); tree=parse(read(file)); prose[slug]=body_prose(tree)
        ids={n.attrs['id']:n for n in tree.all() if 'id' in n.attrs}
        for p in registry['passages']:
            if p['page']==slug: ids['agda-'+p['id']].replace(agda.panel(p))
        for script in tree.all('script'):
            src=script.attrs.get('src','')
            for old,new in [('agda-context.js',CONTEXT),('supplementary.js',EXTRA)]:
                if src.startswith('assets/'+old): script.attrs['src']='assets/'+new+'?v='+version
        for node in tree.all('a'):
            if node.has('agda-start'):
                name='SCT.VolumeI.'+entry[slug]
                if name not in data['modules']: raise ValueError('Missing Chapter 2 entry: '+name)
                node.attrs.update({'data-module':name,'href':CODE+name+'.html'})
        if body_prose(tree)!=prose[slug]: raise ValueError('Chapter 2 prose changed: '+slug)
        write(file,'<!doctype html>\n'+tree.html()); changed.add(file.relative_to(site).as_posix())
    names=set(data['modules'])
    ch1={p.stem for p in (site/'agda/chapter01').glob('*.html')}
    ch2={n for n in names if n.startswith('SCT.VolumeI.Chapter02.')}
    # Browsing offers both current chapters. Definition links never cross editions.
    browse={n for n in ch1|ch2 if n.startswith('SCT.VolumeI.Chapter')}
    for asset,own,other_prefix in [(NAV,names,'../chapter01/'),('chapter01-module-navigation-data.js',ch1,'../chapter02/')]:
        nav={'tree':module_tree(browse),'labels':{n:module_label(n) for n in browse},
             'hrefs':{n:('' if n in own else other_prefix)+n+'.html' for n in browse}}
        write(site/'assets'/asset,'window.SCT_MODULE_NAVIGATION = '+json.dumps(nav,ensure_ascii=False)+';\n')
        changed.add('assets/'+asset)
    # Retained standalone modules also browse the current published editions.
    nav={'tree':module_tree(browse),'labels':{n:module_label(n) for n in browse},
         'hrefs':{n:('chapter02/' if n in ch2 else 'chapter01/')+n+'.html' for n in browse}}
    write(site/'assets/module-navigation-data.js','window.SCT_MODULE_NAVIGATION = '+json.dumps(nav,ensure_ascii=False)+';\n')
    changed.add('assets/module-navigation-data.js')
    symbols=[]
    for compiler in sorted((bundle/'html').glob('*.html')):
        name=compiler.stem; pre=next(parse(read(compiler)).all('pre')); unique_agda_ids(pre)
        if name in ch2:
            for anchor in pre.all('a'):
                identifier=anchor.attrs.get('id','')
                if (identifier.isdigit() and anchor.attrs.get('href')==compiler.name+'#'+identifier
                    and any(anchor.has(c) for c in ('Postulate','Function','Record','Datatype','Field','InductiveConstructor','CoinductiveConstructor'))):
                    symbols.append('<li class="symbol-entry"><a href="'+CODE+compiler.name+'#'+quote(identifier)+'"><code>'+escape(name+'.'+anchor.text())+'</code></a></li>')
        linked=[p for p in passages if any('SCT.VolumeI.'+d['module']==name for d in p['declarations'])]
        back=('<details class="module-book-passages"><summary>Corresponding book passages</summary><ul>'+''.join(
            '<li><a href="../../'+p['page']+'.html#text-'+p['id']+'">'+escape(p['title'])+'</a></li>' for p in linked)+'</ul></details>') if linked else ''
        navigation=standalone_navigation(name,names).replace('href="../code-index.html"','href="../../code-index.html"')
        rendered=page(name,navigation+back+pre.html(),math=False,prefix='../../')
        rendered=re.sub(r'assets/module-navigation-data.js\?v=[^"]+','assets/'+NAV+'?v='+version,rendered)
        write(site/CODE/compiler.name,rendered)
    for source in receipt['sources'].values():
        target=site/RAW/Path(source['path']).relative_to('src')
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((bundle/source['path']).read_bytes())
    aggregate=receipt['aggregate'];relative=Path(*aggregate.split('.')).with_suffix('.agda')
    target=site/RAW/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((bundle/'src'/relative).read_bytes())
    def group(node):
        inside=''.join('<article class="code-index-entry" data-module="'+n+'"><h3><a href="'+CODE+n+'.html">'+escape(module_label(n))+'</a></h3><p class="module-qualified">'+escape(n)+'</p></article>' for n in node['modules'])
        inside+=''.join(group(c) for c in node['children'])
        return '<details class="module-group" data-module-group="'+node['key']+'"><summary>'+escape(node['label'])+'</summary><div class="module-group-content">'+inside+'</div></details>' if node['key'] else inside
    tree=parse(read(site/'code-index.html'))
    for node in list(tree.all('details')):
        if node.attrs.get('data-module-group')=='SCT.VolumeI.Chapter02':
            node.replace(group(module_tree(ch2)['children'][0]))
    for node in list(tree.all('li')):
        if node.has('symbol-entry') and 'SCT.VolumeI.Chapter02.' in node.text():node.replace('')
    container=next(n for n in tree.all('details') if n.has('symbol-index'))
    symbol_list=next(container.all('ul'))
    for child in parse(''.join(symbols)).children:
        child.parent=symbol_list;symbol_list.children.append(child)
    write(site/'code-index.html','<!doctype html>\n'+tree.html());changed.add('code-index.html')
    public={'chapter':2,'commit':receipt['commit'],'checked_utc':receipt['finished_utc'],
            'development':'rebuild2','repository_source_root':'rebuild2/src',
            'assumption_inventory_sha256':receipt.get('assumption_inventory',{}).get('sha256'),
            'source_modules':sorted(set(receipt['sources'])|{aggregate}),
            'compiled_modules':sorted(names),'excluded_modules':receipt['excluded_modules'],
            'skipped_aggregates':selected.get('skipped_aggregates',[]),
            'code_prefix':CODE,'source_prefix':RAW,'pages':sorted(pages)}
    return {'bundle':str(bundle),'public':public,'prose':prose,'changed':sorted(changed),
            'reader_sha256':digest((bundle/'reader.json').read_bytes()),
            'manifest_sha256':digest(MANIFEST_PATH.read_bytes())}


def validate(record, site, trees, link):
    from chapter_edition import verify_bundle, body_prose
    from reader_context import module_lines, compiler_anchors
    bundle=Path(record['bundle']);receipt=verify_bundle(bundle)
    if digest(MANIFEST_PATH.read_bytes())!=record['manifest_sha256']:
        raise ValueError('Chapter 2 correspondence changed; reassemble')
    if digest((bundle/'reader.json').read_bytes())!=record['reader_sha256']:
        raise ValueError('Chapter 2 reader changed')
    data=json.loads(read(bundle/'reader.json'))
    rendered=json.loads(read(site/'assets'/CONTEXT).split(' = ',1)[1].rstrip(';\n'))
    if rendered!=data:raise ValueError('Chapter 2 published reader differs from checked data')
    registry=manifest()
    for p in registry['passages']+registry.get('reverse_only',[]):
        shown=data['passages'][p['id']]
        expected=[('SCT.VolumeI.'+d['module'],d['qualified'],d['role']) for d in p['declarations']]
        if [(d['module'],d['qualified'],d['role']) for d in shown['declarations']]!=expected or shown['note']!=p['note']:
            raise ValueError('Stale Chapter 2 passage: '+p['id'])
        for d in shown['declarations']:link(site/(p['page']+'.html'),d['href'])
    for name,payload in data['modules'].items():
        pre=next(parse(read(bundle/'html'/(name+'.html'))).all('pre'))
        if next(trees[site/CODE/(name+'.html')].all('pre')).text()!=pre.text():
            raise ValueError('Chapter 2 compiler source changed: '+name)
        expected=module_lines(pre.text(),pre,CODE)
        if [(x['number'],x['html']) for x in payload['lines']]!=[(x['number'],x['html']) for x in expected]:
            raise ValueError('Chapter 2 reader lines differ: '+name)
        if payload['anchors']!=compiler_anchors(pre,{x['number'] for x in expected}):
            raise ValueError('Chapter 2 reader anchors differ: '+name)
        for line in payload['lines']:
            for a in parse(line['html']).all('a'):
                if a.attrs.get('href'):link(site/'morphisms-and-diagrams.html',a.attrs['href'])
    for slug,prose in record['prose'].items():
        if body_prose(trees[site/(slug+'.html')])!=prose:raise ValueError('Chapter 2 manuscript changed')
    return {'source_modules':len(receipt['sources']), 'chapter_modules':sum('.Chapter02.' in n for n in receipt['sources']),
            'commit':receipt['commit'],'passages':len(data['passages'])}
