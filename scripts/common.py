"""Small shared utilities. No third-party Python dependencies."""
from pathlib import Path
from html.parser import HTMLParser
from html import escape
import hashlib, json, os, re

ROOT = Path(__file__).resolve().parents[1]

def _manuscript():
    """Use the main private manuscript repository for shared source files."""
    return Path(os.environ.get('SCT_MANUSCRIPT', str(ROOT.parent / 'Synthetic Category Theory'))).resolve()

REPO = _manuscript()
ANNOTATED = ROOT / 'Annotated tex-files'
BUILD = ROOT / '_build'
SNAP = BUILD / 'snapshot'
SITE = ROOT / '_site'
CHAPTER = 'Volume I - Synthetic Category Theory/1_Naive_Category_Theory.tex'
CHAPTER2 = 'Volume I - Synthetic Category Theory/2_Groupoids.tex'
MASTER = 'Volume I - Synthetic Category Theory/Book_Vol_I.tex'
BOOK_FRONTMATTER = [
    {'source': 'Volume I - Synthetic Category Theory/0_Introduction.tex',
     'slug': 'introduction', 'title': 'Introduction'},
    {'source': 'Volume I - Synthetic Category Theory/0_Overview_Of_The_Axioms.tex',
     'slug': 'overview-of-the-axioms', 'title': 'Overview of the axioms'},
]
BOOK_SECTIONS = [
    ('basic-vocabulary', 'The basic vocabulary', 'sec:External_Theory'),
    ('coherences', 'Coherences', 'sec:Coherences'),
    ('equivalences', 'Equivalences of categories', 'sec:Equivalence_Of_Categories'),
    ('mapping-animae', 'Mapping animae', 'sec:Mapping_Animae'),
    ('initial-categories-and-coproducts', 'Initial categories and coproducts', 'sec:Initial_Categories_And_Coproducts'),
    ('pullbacks', 'Pullbacks of categories', 'sec:Pullbacks_Of_Categories'),
    ('functor-categories', 'Functor categories', 'sec:Functor_Categories'),
    ('pushouts', 'Pushout squares', 'sec:Pushouts_Of_Categories'),
]
BOOK_CHAPTERS = [
    {'number': 1, 'source': CHAPTER, 'slug': 'chapter-introduction',
     'title': 'The language of synthetic category theory', 'label': 'chap:Naive_Category_Theory',
     'sections': BOOK_SECTIONS},
    {'number': 2, 'source': CHAPTER2, 'slug': 'internal-structure-introduction',
     'title': 'The internal structure of categories', 'label': 'chap:Groupoids',
     'sections': [('morphisms-and-diagrams', 'Morphisms and diagrams', 'sec:Morphisms_and_Diagrams'),
                  ('segal-axiom', 'The Segal axiom', 'sec:The_Segal_Axiom'),
                  ('rezk-axiom', 'The Rezk axiom', 'sec:Rezk_Axiom'),
                  ('groupoids', 'Groupoids', 'sec:Groupoids'),
                  ('recognizing-animae', 'Recognizing animae', 'sec:Recognizing_Animae'),
                  ('chapter-2-exercises', 'Exercises', 'web:chapter02-exercises')]},
]
BOOK_SECTIONS = [s for chapter in BOOK_CHAPTERS for s in chapter['sections']]
BOOK_PAGES = [(p['slug'], p['title'], None) for p in BOOK_FRONTMATTER] + [(slug, title, label) for chapter in BOOK_CHAPTERS
              for slug, title, label in [(chapter['slug'], chapter['title'], chapter['label'])]+chapter['sections']]
NAVIGATION = [('index', 'Overview')] + [(p['slug'], p['title']) for p in BOOK_FRONTMATTER] + [
    entry for chapter in BOOK_CHAPTERS for entry in
    [(chapter['slug'], f'Chapter {chapter["number"]} introduction')] +
    [(slug, f'{chapter["number"]}.{i} · {title}') for i, (slug, title, _) in enumerate(chapter['sections'], 1)]
] + [('code-index', 'All Agda code'), ('formalization', 'Agda guide'), ('build-report', 'Build details')]

def manuscript_input(relative):
    """Prefer a local annotated file; obtain all other inputs from the private repo."""
    relative = Path(relative)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('Manuscript input must be a repository-relative path')
    annotated = ANNOTATED / relative
    return annotated if annotated.is_file() else REPO / relative

def selected_source(source, chapter=CHAPTER):
    """Select a chapter opening and its configured initial sections by labels."""
    body = source.split(r'\begin{document}', 1)[1].split(r'\end{document}', 1)[0]
    # Unlabelled selected headings receive a web-only label in the conversion
    # input, keeping the maintained annotated manuscript unchanged.
    sections = list(re.finditer(r'\\section\{([^}]+)\}(?:\s*\\label\[section\]\{([^}]+)\})?', body))
    config = next(c for c in BOOK_CHAPTERS if c['source']==chapter)
    expected = [label for _, _, label in config['sections']]
    if len(sections)<len(expected):
        raise ValueError('The selected manuscript sections changed; review the selection')
    insertions=[]
    for match,(_,title,label) in zip(sections,config['sections']):
        if match[2]==label: continue
        if match[2] is None and label.startswith('web:') and match[1]==title:
            insertions.append((match.end(),r'\label[section]{'+label+'}'))
        else: raise ValueError('The selected manuscript sections changed; review the selection')
    selected=body[:sections[len(expected)].start()] if len(sections)>len(expected) else body
    for at,text in reversed(insertions): selected=selected[:at]+text+selected[at:]
    return selected

def read(path):
    return Path(path).read_text(encoding='utf-8-sig')

def write(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8', newline='\n')

def dump(path, data):
    write(path, json.dumps(data, ensure_ascii=False, indent=2) + '\n')

def digest(data):
    if isinstance(data, str): data = data.encode('utf-8')
    return hashlib.sha256(data).hexdigest()

def external_anchor(label):
    """Keep readable label anchors without whitespace that TeX4ht truncates."""
    return re.sub(r'[^A-Za-z0-9:_.-]', '_', label)

def comments(text):
    # TeX discards the newline after a comment too; retaining it can introduce
    # an illegal paragraph inside display math when a comment-only line occurs.
    return re.sub(r'(?<!\\)%[^\n]*(?:\n|$)', '', text)

VOID = {'area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'}
class Node:
    def __init__(self, tag='', attrs=None, parent=None):
        self.tag, self.attrs, self.parent, self.children = tag, dict(attrs or []), parent, []
    def all(self, tag=None):
        for child in self.children:
            if isinstance(child, Node):
                if tag is None or child.tag == tag: yield child
                yield from child.all(tag)
    def has(self, cls): return cls in (self.attrs.get('class') or '').split()
    def text(self): return ''.join(c.text() if isinstance(c, Node) else c for c in self.children)
    def html(self):
        attrs = ''.join(' '+k+(('="'+escape(v, quote=True)+'"') if v is not None else '') for k,v in self.attrs.items())
        inner = ''.join(c.html() if isinstance(c, Node) else escape(c, quote=False) for c in self.children)
        if not self.tag: return inner
        if self.tag in VOID: return f'<{self.tag}{attrs}>'
        return f'<{self.tag}{attrs}>{inner}</{self.tag}>'
    def replace(self, html):
        nodes = parse(html).children
        i = self.parent.children.index(self)
        self.parent.children[i:i+1] = nodes
        for n in nodes:
            if isinstance(n, Node): n.parent = self.parent

class Parser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node(); self.stack = [self.root]
    def handle_starttag(self, tag, attrs):
        n = Node(tag, attrs, self.stack[-1]); self.stack[-1].children.append(n)
        if tag not in VOID: self.stack.append(n)
    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID: self.handle_endtag(tag)
    def handle_endtag(self, tag):
        for i in range(len(self.stack)-1,0,-1):
            if self.stack[i].tag == tag:
                del self.stack[i:]; break
    def handle_data(self, data): self.stack[-1].children.append(data)

def parse(html):
    p=Parser(); p.feed(html); return p.root

def group(text, start, opening='{', closing='}'):
    while start < len(text) and text[start].isspace(): start += 1
    if start == len(text) or text[start] != opening: raise ValueError(f'Expected {opening}: {text[start:start+70]}')
    depth=1; i=start+1
    while i < len(text):
        if text[i] == opening and text[i-1] != '\\': depth+=1
        if text[i] == closing and text[i-1] != '\\': depth-=1
        if depth == 0: return text[start+1:i], i+1
        i+=1
    raise ValueError('Unclosed argument')
