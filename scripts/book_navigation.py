"""Shared chapter contents and page turns for generated and authored pages."""
from common import BOOK_CHAPTERS, BOOK_FRONTMATTER, BOOK_PAGES, escape


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
    parts.extend(link(slug,title) for slug,title in [('code-index','All Agda code'),('formalization','Agda guide'),('build-report','Build details')])
    return ''.join(parts)


def page_turns(current, prefix=''):
    chapters={c['slug']:c for c in BOOK_CHAPTERS}
    pages={slug:(title,label) for slug,title,label in BOOK_PAGES}
    if current not in pages: return ''
    openings=[p['slug'] for p in BOOK_FRONTMATTER]+list(chapters)
    order=openings if current in openings else list(pages)
    index=order.index(current); links=[]
    numbers={slug:f'{c["number"]}.{i}' for c in BOOK_CHAPTERS for i,(slug,_,_) in enumerate(c['sections'],1)}
    for offset,rel,arrow,label in [(-1,'prev','←','Previous'),(1,'next','→','Next')]:
        at=index+offset
        if not 0<=at<len(order): continue
        slug=order[at]; title=pages[slug][0]
        target=f'Chapter {chapters[slug]["number"]}' if slug in chapters else 'Section '+numbers[slug] if slug in numbers else title
        links.append(f'<a rel="{rel}" href="{prefix}{slug}.html" title="{escape(title,quote=True)}" aria-label="{label}: {target}, {escape(title,quote=True)}"><span class="turn-direction">{arrow} {label}</span><span class="turn-target">{target}</span></a>')
    return '<nav class="page-turns" aria-label="'+('Chapter' if current in chapters else 'Reading')+' navigation">'+''.join(links)+'</nav>' if links else ''
