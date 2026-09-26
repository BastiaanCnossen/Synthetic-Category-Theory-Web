"""Shared chapter contents and page turns for generated and authored pages."""
from common import BOOK_CHAPTERS, BOOK_FRONTMATTER, BOOK_PAGES, escape, parse


def contents(current='', prefix=''):
    def link(slug, label):
        active=' aria-current="page"' if current==slug else ''
        return f'<a{active} href="{prefix}{slug}.html">{escape(label)}</a>'
    parts=[link('index','Overview')]
    parts.extend(link(p['slug'],p['title']) for p in BOOK_FRONTMATTER)
    for chapter in BOOK_CHAPTERS:
        slugs=[chapter['slug']]+[s[0] for s in chapter['sections']]
        expanded=current in slugs or current.startswith(f'SCT.VolumeI.Chapter{chapter["number"]:02d}.')
        parts.append('<details class="contents-chapter"'+(' open' if expanded else '')+'>')
        parts.append(f'<summary><span class="chapter-number">Chapter {chapter["number"]}</span><span class="chapter-name">{escape(chapter["title"])}</span></summary>')
        parts.append('<div class="chapter-sections">'+link(chapter['slug'],'Chapter introduction'))
        parts.extend(link(slug,f'{chapter["number"]}.{i} · {title}') for i,(slug,title,_) in enumerate(chapter['sections'],1))
        parts.append('</div></details>')
    return ''.join(parts)


def chapter_for(current):
    return next((c for c in BOOK_CHAPTERS
                 if current==c['slug'] or current in {s[0] for s in c['sections']}),None)


def reading_tools(prefix=''):
    return f'''<aside class="utility-dock" aria-label="Reading tools">
<button id="reading-settings-button" class="utility-button" type="button" aria-label="Reading settings" title="Reading settings" aria-controls="reading-settings" aria-expanded="false"><span aria-hidden="true">⚙</span></button>
<a class="utility-button" href="{prefix}book.pdf" aria-label="Read the web edition PDF" title="Read the web edition PDF"><span aria-hidden="true">📖</span></a>
<section id="reading-settings" class="settings-panel" aria-label="Reading preferences" hidden><h2>Reading preferences</h2>
<label><input id="collapse-proofs" type="checkbox"> Collapse book proofs</label>
<label><input id="show-agda-links" type="checkbox"> Show links to Agda code</label>
</section></aside>'''


def book_sidebar(current='', prefix=''):
    resources=''.join(f'<a href="{prefix}{slug}.html"'+(' aria-current="page"' if current==slug else '')+f'>{title}</a>'
                      for slug,title in [('code-index','All Agda code'),('formalization','Agda guide'),('build-report','Build details')])
    return '<aside class="reader-nav" aria-label="Book navigation"><h2>Resources</h2><nav aria-label="Resources" class="reader-resources">'+resources+'</nav><h2>Contents</h2><nav aria-label="Contents">'+contents(current,prefix)+'</nav></aside>'


# Reader entry points, deliberately chosen instead of the first technical lemma.
AGDA_ENTRY_MODULES = {
    'basic-vocabulary': 'Chapter01.Section01.Vocabulary',
    'coherences': 'Chapter01.Section02.Coherence',
    'equivalences': 'Chapter01.Section03.Equivalences',
    'mapping-animae': 'Chapter01.Section04.MappingAnimae',
    'initial-categories-and-coproducts': 'Chapter01.Section05.Initial',
    'pullbacks': 'Chapter01.Section06.PullbackSquares',
    'functor-categories': 'Chapter01.Section07.FunctorCategories',
    'pushouts': 'Chapter01.Section08.PushoutSquares',
    'morphisms-and-diagrams': 'Chapter02.Section01.Morphisms',
    'segal-axiom': 'Chapter02.Section02.SegalAxiom',
    'rezk-axiom': 'Chapter02.Section03.RezkAxiom',
    'groupoids': 'Chapter02.Section04.Groupoids',
    'recognizing-animae': 'Chapter02.Section05.Recognition',
    'chapter-2-exercises': 'Chapter02.Section06.ElementaryYoneda',
    'subcategories': 'Chapter03.Section01.Subcategories',
    'full-subcategories': 'Chapter03.Section02.FullSubcategories',
    'localizations': 'Chapter03.Section03.Localizations',
    'geometric-realizations': 'Chapter03.Section04.GeometricRealization',
    'exponentiable-functors': 'Chapter03.Section05.ExponentiableFunctors',
    'joins': 'Chapter03.Section06.Joins',
    'slice-categories': 'Chapter03.Section07.RelativeSlices',
    'chapter-3-exercises': 'Chapter03.Section01.SubcategoryFunctoriality',
}


def agda_invitation(current, manifest):
    passages=[p for p in manifest['passages'] if p['page']==current]
    if not passages: return ''
    module=AGDA_ENTRY_MODULES[current]
    if not any(d['module']==module for p in passages for d in p['declarations']):
        raise ValueError('Review Agda reader entry point for '+current)
    module=manifest['module_prefix']+module
    return ('<p class="agda-help"><span class="agda-invitation">'
            f'<a class="agda-start" data-module="{module}" href="agda/{module}.html">Read the Agda code</a> alongside the book.</span>'
            '<span class="agda-instructions">Click dotted-underlined prose to read its Agda code alongside the book. '
            '<button type="button" class="agda-hide text-button">Hide links.</button> '
            '<a href="code-index.html">Browse all code.</a></span></p>')


def breadcrumbs(current, prefix=''):
    chapter=chapter_for(current)
    if not chapter: return f'<a class="collection-return" href="{prefix}index.html">Synthetic category theory</a>'
    items=[f'<li><a href="{prefix}index.html">Synthetic category theory</a></li>']
    label=f'Chapter {chapter["number"]}'
    if current==chapter['slug']:
        items.append(f'<li aria-current="page">{label}</li>')
    else:
        number=next(i for i,s in enumerate(chapter['sections'],1) if s[0]==current)
        items.append(f'<li><a href="{prefix}{chapter["slug"]}.html" title="{escape(chapter["title"],quote=True)}">{label}</a></li>')
        items.append(f'<li aria-current="page">Section {chapter["number"]}.{number}</li>')
    return '<nav class="book-breadcrumbs" aria-label="Breadcrumb"><ol>'+''.join(items)+'</ol></nav>'


def chapter_sections(current, overview=''):
    chapter=next((c for c in BOOK_CHAPTERS if c['slug']==current),None)
    if not chapter: return ''
    # The directly edited overview owns these descriptions, avoiding a second
    # maintained copy of the author's text in a template or build script.
    descriptions={}
    for card in parse(overview).all('article'):
        if not card.has('chapter-card'): continue
        link=next(card.all('a'),None)
        if link:
            descriptions[link.attrs.get('href','')]=''.join(p.html() for p in card.all('p') if not p.has('eyebrow'))
    cards=[]
    for number,(slug,title,_) in enumerate(chapter['sections'],1):
        cards.append(f'<article class="section-card"><p class="section-card-meta">Section {chapter["number"]}.{number}</p>'
                     f'<h3><a href="{slug}.html">{escape(title)}</a></h3>{descriptions.get(slug+".html","")}</article>')
    return '<section class="available-sections" aria-labelledby="chapter-sections-heading"><h2 id="chapter-sections-heading">Sections</h2><div class="section-card-grid">'+''.join(cards)+'</div></section>'


def page_turns(current, prefix=''):
    chapters={c['slug']:c for c in BOOK_CHAPTERS}
    pages={slug:(title,label) for slug,title,label in BOOK_PAGES}
    if current not in pages: return ''
    chapter=chapter_for(current)
    numbers={slug:f'{c["number"]}.{i}' for c in BOOK_CHAPTERS for i,(slug,_,_) in enumerate(c['sections'],1)}
    def control(slug,rel,kind=''):
        arrow,label=('←','Previous') if rel=='prev' else ('→','Next')
        direction=label+(' '+kind if kind else '')
        step=f' data-step="{rel}-{kind}"' if kind else ''
        if slug is None:
            return f'<button type="button" disabled{step} aria-label="No {direction.lower()}" title="No {direction.lower()} in this web edition"><span class="turn-direction">{arrow} {direction}</span><span class="turn-target">Not available</span></button>'
        title=pages[slug][0]
        target=f'Chapter {chapters[slug]["number"]}' if slug in chapters else 'Section '+numbers[slug] if slug in numbers else title
        return f'<a rel="{rel}"{step} href="{prefix}{slug}.html" title="{escape(title,quote=True)}" aria-label="{direction}: {target}, {escape(title,quote=True)}"><span class="turn-direction">{arrow} {direction}</span><span class="turn-target">{target}</span></a>'
    if chapter:
        at=BOOK_CHAPTERS.index(chapter)
        previous=BOOK_CHAPTERS[at-1]['slug'] if at else None
        following=BOOK_CHAPTERS[at+1]['slug'] if at+1<len(BOOK_CHAPTERS) else None
        ordered=list(pages); position=ordered.index(current)
        before=[slug for slug in ordered[:position] if slug in numbers]
        after=[slug for slug in ordered[position+1:] if slug in numbers]
        links=[control(previous,'prev','chapter'),control(following,'next','chapter'),
               control(before[-1] if before else None,'prev','section'),
               control(after[0] if after else None,'next','section')]
    else:
        order=[p['slug'] for p in BOOK_FRONTMATTER]+list(chapters)
        at=order.index(current)
        links=[control(order[i],rel) for i,rel in [(at-1,'prev'),(at+1,'next')] if 0<=i<len(order)]
    return '<nav class="page-turns" aria-label="Reading navigation">'+''.join(links)+'</nav>'
