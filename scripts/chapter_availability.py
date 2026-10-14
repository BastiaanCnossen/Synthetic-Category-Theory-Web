"""Temporarily suspend code entry points for chapters awaiting rebuild2."""
from common import *

DISABLED_CHAPTERS = (2, 3)
NOTICE = ('Agda links are temporarily unavailable for Chapters 2 and 3 while '
          'their code is updated to the foundations used in Chapter 1.')


def suspended_module(name):
    return any(f'.Chapter{n:02d}.' in name for n in DISABLED_CHAPTERS)


def prune_tree(node):
    node['modules'] = [name for name in node['modules'] if not suspended_module(name)]
    node['children'] = [prune_tree(child) for child in node['children']
                        if not any(child['key'] == f'SCT.VolumeI.Chapter{n:02d}'
                                   for n in DISABLED_CHAPTERS)]
    return node


def disable_page(tree):
    # Keep fragment destinations, including old bookmarks, without code controls.
    for node in list(tree.all()):
        if any(node.has(cls) for cls in ('agda-panel', 'supplementary-targets', 'agda-help')):
            anchors = [n.attrs['id'] for n in [node, *node.all()] if 'id' in n.attrs]
            node.replace(''.join('<span id="'+escape(a, quote=True)+'"></span>' for a in anchors))
        elif node.has('agda-trigger'):
            node.tag = 'span'
            node.attrs = {k:v for k,v in node.attrs.items() if k == 'id'}
        elif node.tag == 'script' and any('/'+name in node.attrs.get('src','')
                for name in ('agda-context.js', 'supplementary.js')):
            node.replace('')
        elif node.tag == 'input' and node.attrs.get('id') == 'show-agda-links':
            node.parent.replace('')
    main = next(tree.all('main'))
    notice = parse('<p class="coverage-note edition-notice">'+NOTICE+'</p>').children[0]
    notice.parent = main
    main.children.insert(0, notice)


def suspend(site):
    from chapter_edition import body_prose
    from supplementary import catalog
    slugs = {slug for chapter in BOOK_CHAPTERS if chapter['number'] in DISABLED_CHAPTERS
             for slug in [chapter['slug'], *(s[0] for s in chapter['sections'])]}
    slugs.update(note['slug'] for note in catalog() if note['chapter'] in DISABLED_CHAPTERS)
    prose = {}
    changed = set()
    for slug in sorted(slugs):
        path = site/(slug+'.html'); tree = parse(read(path))
        prose[slug] = body_prose(tree)
        disable_page(tree)
        if body_prose(tree) != prose[slug]:
            raise ValueError('Suspending code changed book prose: '+slug)
        write(path, '<!doctype html>\n'+tree.html())
        changed.add(path.relative_to(site).as_posix())
    for filename, variable, key in [('agda-context.js','SCT_AGDA','module_tree'),
                                     ('module-navigation-data.js','SCT_MODULE_NAVIGATION','tree'),
                                     ('chapter01-module-navigation-data.js','SCT_MODULE_NAVIGATION','tree')]:
        path = site/'assets'/filename
        source = read(path)
        data = json.loads(source.split(' = ',1)[1].rstrip(';\n'))
        prune_tree(data[key])
        data['disabled_chapters'] = list(DISABLED_CHAPTERS)
        write(path,'window.'+variable+' = '+json.dumps(data,ensure_ascii=False)+';\n')
        changed.add(path.relative_to(site).as_posix())
    # Remove both the hierarchical listing and the flat symbol search results.
    path = site/'code-index.html'; tree = parse(read(path))
    for node in list(tree.all()):
        if node.attrs.get('data-module-group') in {f'SCT.VolumeI.Chapter{n:02d}' for n in DISABLED_CHAPTERS}:
            node.replace('')
        elif node.has('symbol-entry') and suspended_module(node.text()):
            node.replace('')
        elif node.tag == 'p' and ('Later chapters and their supporting dependency pages retain' in node.text()
                                 or 'Chapters 2–3 and their dependency pages retain' in node.text()):
            node.replace('<p>Chapter 1 uses the current rebuild2 edition. <a href="chapter01-code.html">Read its scope and module list.</a></p>')
    main = next(tree.all('main'))
    notice = parse('<p class="coverage-note edition-notice">'+NOTICE+'</p>').children[0]
    notice.parent = main; main.children.insert(0,notice)
    write(path,'<!doctype html>\n'+tree.html())
    changed.add('code-index.html')
    path = site/'chapter01-code.html'
    write(path,read(path).replace('Chapters 2–3 retain their earlier checked edition.',
                                'Agda access from Chapters 2–3 is temporarily disabled pending their migration.'))
    changed.add('chapter01-code.html')
    return prose, sorted(changed)


def validate_suspension(site, files):
    for relative in files:
        if relative.endswith('.html') and relative not in ('code-index.html','chapter01-code.html'):
            tree=parse(read(site/relative))
            if any(n.has('agda-trigger') or n.has('agda-panel') or n.has('agda-start')
                   or n.attrs.get('id')=='show-agda-links' for n in tree.all()):
                raise ValueError('Suspended chapter still offers code: '+relative)
    for relative in ('assets/agda-context.js','assets/module-navigation-data.js',
                     'assets/chapter01-module-navigation-data.js'):
        data=json.loads(read(site/relative).split(' = ',1)[1].rstrip(';\n'))
        tree=data.get('tree',data.get('module_tree'))
        def check(node):
            if any(suspended_module(name) for name in node['modules']):
                raise ValueError('Suspended module in browser: '+relative)
            for child in node['children']: check(child)
        check(tree)
    tree=parse(read(site/'code-index.html'))
    if any((n.has('code-index-entry') or n.has('symbol-entry')) and suspended_module(n.text())
           for n in tree.all()):
        raise ValueError('Suspended chapter in code index')
