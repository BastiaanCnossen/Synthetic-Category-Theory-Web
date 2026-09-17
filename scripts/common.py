"""Small shared utilities. No third-party Python dependencies."""
from pathlib import Path
from html.parser import HTMLParser
from html import escape
import hashlib, json, os, re

ROOT = Path(__file__).resolve().parents[1]

def _manuscript():
    """Use the explicitly supplied annotated private checkout or its sibling."""
    return Path(os.environ.get('SCT_MANUSCRIPT', str(ROOT.parent / 'Synthetic Category Theory Web Annotations'))).resolve()

REPO = _manuscript()
BUILD = ROOT / '_build'
SNAP = BUILD / 'snapshot'
SITE = ROOT / '_site'
CHAPTER = 'Volume I - Synthetic Category Theory/1_Naive_Category_Theory.tex'
MASTER = 'Volume I - Synthetic Category Theory/Book_Vol_I.tex'

def selected_source(source):
    """Select chapter opening and Sections 1.1–1.3 by their existing labels."""
    body = source.split(r'\begin{document}', 1)[1].split(r'\end{document}', 1)[0]
    sections = list(re.finditer(r'\\section\{([^}]+)\}\s*\\label\[section\]\{([^}]+)\}', body))
    expected = ['sec:External_Theory', 'sec:Equivalence_Of_Categories', 'sec:Mapping_Animae']
    if [m[2] for m in sections[:3]] != expected or len(sections) < 4:
        raise ValueError('The selected manuscript sections changed; review the selection')
    return body[:sections[3].start()]

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
