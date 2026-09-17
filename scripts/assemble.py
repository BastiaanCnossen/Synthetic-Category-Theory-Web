"""Join TeX4ht output to compiler-produced Agda fragments, without copying prose."""
from common import *
from urllib.parse import quote, unquote
import copy, textwrap, shutil
from pilot_model import declaration_range, prelude

MANIFEST=json.loads(read(ROOT/'correspondence.json'))
PREFIX=MANIFEST['module_prefix']
ROLES={'assumption':'Assumption · boundary checked','derived':'Derived · checked against supplied interface','definition':'Definition · checked'}

def math_config():
    source=comments(read(SNAP/'preamble.tex')); macros={}
    for m in re.finditer(r'\\DeclareMathOperator\*?\{\\([A-Za-z]+)\}',source):
        value,end=group(source,m.end()); macros[m[1]]='\\operatorname{'+value+'}'
    for m in re.finditer(r'\\(?:newcommand|renewcommand|providecommand)\*?\s*(?:\{\\([A-Za-z]+)\}|\\([A-Za-z]+))\s*(?:\[(\d+)\])?',source):
        try: value,end=group(source,m.end())
        except ValueError: continue
        if not re.search(r'\\(?:tikz|HCode|color|notehelper|raisebox)',value):
            macros[m[1] or m[2]]=[value,int(m[3])] if m[3] else value
    macros.update({'iso':r'\xrightarrow{\sim}','inviso':r'\xleftarrow{\sim}','qedhere':'','qed':r'\square'})
    return {'loader':{'paths':{'fonts':'vendor/mathjax/fonts'},'load':['[tex]/mathtools']},'tex':{'inlineMath':[['\\(','\\)']],'displayMath':[['\\[','\\]']],'packages':{'[+]':['ams','mathtools']},'macros':macros},'options':{'enableMenu':False}}

def page(title, content, current='', math=True, prefix=''):
    navigation=[]
    for slug,label in [('index','Overview'),('basic-vocabulary','1.1 · The basic vocabulary'),('equivalences','1.2 · Equivalences of categories'),('code-index','All Agda code'),('formalization','Agda guide'),('build-report','Build and coverage')]:
        active=' aria-current="page"' if current==slug else ''
        navigation.append(f'<a{active} href="{prefix}{slug}.html">{label}</a>')
    nav=''.join(navigation)
    scripts=f'<script src="{prefix}assets/math-config.js"></script><script defer src="{prefix}vendor/mathjax/tex-chtml.js"></script>' if math else ''
    has_passages=current in ('basic-vocabulary','equivalences')
    reader_script=f'<script defer src="{prefix}assets/agda-context.js"></script>' if has_passages else ''
    body_class='has-passages' if has_passages else ''
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="robots" content="noindex,nofollow"><title>{escape(title)} | Synthetic category theory</title>
<link rel="icon" href="{prefix}assets/favicon.svg" type="image/svg+xml"><link rel="stylesheet" href="{prefix}assets/reader-shell.css"><link rel="stylesheet" href="{prefix}assets/reader.css"><link rel="stylesheet" href="{prefix}assets/Agda.css">
{scripts}{reader_script}<script defer src="{prefix}assets/reader.js"></script></head>
<body class="{body_class}"><a class="skip-link" href="#main">Skip to content</a>
<header class="site-header"><a class="collection-return" href="{prefix}index.html">Synthetic category theory</a><p class="eyebrow">Volume I · Experimental web edition</p><h1>{escape(title)}</h1></header>
<div class="reader-grid"><aside class="reader-nav" aria-label="Book navigation"><details open><summary>Contents</summary><nav>{nav}</nav></details>
<details class="settings"><summary>Reading preferences</summary><label><input id="collapse-proofs" type="checkbox"> Collapse book proofs</label><label><input id="hide-agda-links" type="checkbox"> Hide links to Agda code</label>{'<button id="open-code-browser" type="button">Browse Agda modules</button>' if has_passages else ''}<a href="{prefix}book.pdf">Read the web edition PDF</a></details></aside>
<main id="main" class="notes-page" tabindex="-1">{content}</main></div>
<footer>Experimental web edition · Generated from annotated LaTeX and Agda sources. <a href="{prefix}build-report.html">Build details</a></footer></body></html>'''

def code_range(source, name):
    matches=list(re.finditer(r'^( *)'+re.escape(name)+r'\s*:',source,re.M))
    if len(matches)!=1: raise ValueError(f'Declaration {name}: expected unique signature, found {len(matches)}')
    m=matches[0]; indent=len(m[1]); start=m.start(); end=len(source); proof=None
    for line in re.finditer(r'^.*(?:\n|$)',source[m.end():],re.M):
        text=line[0]; pos=m.end()+line.start()
        if pos == m.end(): continue
        if text.startswith('```'): end=pos; break
        if not text.strip() or text.lstrip().startswith('--'): continue
        pad=len(text)-len(text.lstrip(' '))
        if pad<=indent:
            if re.match(r'^ *'+re.escape(name)+r'(?:\s|\{|=)',text):
                if proof is None: proof=pos
            else: end=pos; break
    while end>start and source[end-1].isspace(): end-=1
    return start,proof,end

class Agda:
    def __init__(self): self.cache={}; self.resolved=[]
    def module(self, short):
        name=PREFIX+short
        if name in self.cache: return self.cache[name]
        src=SNAP/'agda/src'/Path(*name.split('.')).with_suffix('.lagda.md')
        source=read(src).replace('\r\n','\n')
        tree=parse(read(BUILD/'agda'/(name+'.html')))
        pre=next(tree.all('pre'))
        # The all-highlighting backend retains exact literate input. This equality
        # makes character slicing fail closed if a backend changes its encoding.
        if pre.text()!=source: raise ValueError(f'Backend/source text mismatch: {name}')
        self.cache[name]=(name,source,pre,src); return self.cache[name]
    def fragment(self, pre, start, end):
        pos=0
        def take(child):
            nonlocal pos
            if isinstance(child,str):
                a=max(start-pos,0); b=min(end-pos,len(child)); pos+=len(child)
                return escape(child[a:b],quote=False) if b>a else ''
            length=len(child.text()); begin=pos
            if begin+length<=start or begin>=end:
                pos+=length; return ''
            attrs={k:v for k,v in child.attrs.items() if k not in ('id','name')}
            if 'href' in attrs: attrs['href']='agda/'+attrs['href']
            inner=''.join(take(c) for c in child.children)
            attributes=''.join(f' {k}="{escape(v or "",quote=True)}"' for k,v in attrs.items())
            return f'<{child.tag}{attributes}>{inner}</{child.tag}>'
        return ''.join(take(c) for c in pre.children)
    def declaration(self, d):
        name,source,pre,src=self.module(d['module'])
        loc=declaration_range(source,d['name'],d.get('qualified'))
        start,proof,end=loc['start'],loc['proof'],loc['end']
        if loc['kind']=='record': proof=None
        # Anchor from compiler output, not an assumed stable numeric convention.
        position=loc['namepos']
        candidates=[n for n in pre.all('a') if n.text()==d['name'] and n.attrs.get('id','').isdigit() and int(n.attrs['id'])==position+1]
        if len(candidates)!=1: raise ValueError(f'Missing compiler declaration anchor: {name}.{d["name"]}')
        qualified=d.get('qualified',d['name'])
        named=sum(1 for n in pre.all('a') if n.attrs.get('id')==qualified)
        if named!=1:
            # Agda omits named anchors for some fields of nested records.
            # Require the compiler's field classification and its named owner;
            # the qualified source scope and exact character anchor still agree.
            owner=qualified.rsplit('.',1)[0]
            if named or not candidates[0].has('Field') or sum(1 for n in pre.all('a') if n.attrs.get('id')==owner)!=1:
                raise ValueError(f'Missing qualified declaration anchor: {name}.{qualified}')
        anchor=candidates[0].attrs['id']; target=f'agda/{name}.html#{anchor}'
        role=d.get('role','derived'); signature_end=proof if proof is not None else end
        signature=self.fragment(pre,start,signature_end).rstrip()
        implementation=self.fragment(pre,proof,end) if proof is not None else ''
        line=source.count('\n',0,start)+1
        self.resolved.append({'module':name,'declaration':d.get('qualified',d['name']),'target':target,'line':line,'start':start,'end':end,'source_sha256':digest(source),'role':role})
        context=prelude(source,loc)
        heading=f'<h4><code>{escape(d["name"])}</code></h4><p class="status">{ROLES[role]}</p>'
        links=f'<p class="source-links"><a href="{target}">Open full module</a> · <a href="{quote('source-files/'+src.relative_to(SNAP/'agda/src').as_posix())}">Literate source, line {line}</a></p>'
        focus=', '.join(d.get('regions',[]))
        focus_html=f'<p class="focus-note">In this proof, inspect <code>{escape(focus)}</code>. The enclosing proof is shown to retain its local parameters.</p>' if focus else ''
        expanded=' open' if focus else ''
        proof_html=f'<details class="agda-proof"{expanded}><summary>Proof / implementation</summary>{focus_html}<pre class="Agda">{implementation}</pre></details>' if implementation else ''
        context_html=f'<details class="module-context"><summary>Enclosing interface and module parameters</summary><p>The enclosing headers show supplied parameters. Open the full module for imports and surrounding definitions.</p><pre>{escape(context.strip())}</pre></details>'
        html=f'<section class="agda-declaration" data-module="{escape(name,quote=True)}" data-declaration="{escape(d["qualified"],quote=True)}">{heading}<pre class="Agda signature">{signature}</pre>{proof_html}{context_html}{links}</section>'
        if d.get('secondary'): html=f'<details class="supporting"><summary>Supporting result: {escape(d["name"])}</summary>{html}</details>'
        return html
    def panel(self,p):
        content=''.join(self.declaration(d) for d in p['declarations'])
        note=f'<p>{escape(p["note"])}</p>' if p['note'] else ''
        context=f'<details class="mapping-note"><summary>About this correspondence</summary>{note}<p class="scope-note">{escape(MANIFEST["scope_note"])}</p></details>'
        return f'<details class="agda-panel agda-inline" id="agda-{p["id"]}"><summary><span class="agda-tag">Agda</span> {escape(p["title"])}</summary><div class="agda-content">{content}{context}<p class="panel-return"><a href="#text-{p["id"]}">Return to this passage</a> · <a class="permalink" href="#agda-{p["id"]}">Panel link</a></p></div></details>'

def assemble():
    SITE.mkdir(exist_ok=True)
    for name in ('reader-shell.css','reader.css','reader.js','favicon.svg'):
        (SITE/'assets').mkdir(exist_ok=True)
        shutil.copyfile(ROOT/'assets'/name,SITE/'assets'/name)
    vendor_files=json.loads(read(ROOT/'scripts/vendor-files.json'))
    for relative,sha in vendor_files.items():
        source=ROOT/'vendor'/relative
        if digest(source.read_bytes())!=sha: raise ValueError('Vendored asset changed: '+relative)
        target=SITE/'vendor'/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,target)
    write(SITE/'.nojekyll','')
    dump(SITE/'validation.json',{'status':'pending'})
    receipt=json.loads(read(BUILD/'check.json'))
    inputs=json.loads(read(SNAP/'inputs.json'))
    if not receipt['checked'] or receipt['input_hash']!=digest(json.dumps(inputs['files'],sort_keys=True)): raise ValueError('Checked input receipt is stale')
    selection=json.loads(read(BUILD/'selection.json'))
    raw=read(BUILD/'html/pilot.html')
    # Explicit equation tags come from LaTeX, independent of page splitting.
    equation_numbers={m[1]:m[2] for m in re.finditer(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}',read(BUILD/'pilot-pdf.aux'))}
    def numbered_equation(match):
        content=match[1]
        label=re.search(r'\\label\s*\{([^}]+)\}',content)
        if not label or label[1] not in equation_numbers: raise ValueError('Numbered equation needs a resolved source label')
        content=content[:label.start()]+content[label.end():]
        return r'\['+content+r'\tag{'+equation_numbers[label[1]]+r'}\]'
    raw=re.sub(r'\\begin\s*\{equation\}([\s\S]*?)\\end\s*\{equation\}',numbered_equation,raw)
    tree=parse(raw); body=next(tree.all('body'))
    # Drop TeX4ht's whitespace-only page padding before adding exact code slices.
    for node in [body]+list(body.all()):
        node.children=[re.sub(r'(?m)^[ \t]+\n','\n',c) if isinstance(c,str) else c for c in node.children]
    agda=Agda()
    # The framed package repeats a layout-only ID. No source label uses it.
    referenced={n.attrs.get('href','').split('#')[-1] for n in body.all('a')}
    for n in body.all():
        if n.has('framedenv') and 'id' in n.attrs:
            if n.attrs['id'] in referenced: raise ValueError('Referenced TeX4ht frame ID needs an explicit migration')
            del n.attrs['id']
    # TeX4ht normalizes punctuation in IDs. Restore the original source labels.
    ids={n.attrs['id']:n for n in body.all() if 'id' in n.attrs}
    for label in selection['labels']:
        key=label.replace(':','_')
        if key not in ids: raise ValueError(f'Missing manuscript label {label}')
        ids[key].attrs['id']=label
    ids={n.attrs['id']:n for n in body.all() if 'id' in n.attrs}
    for d in selection['diagrams']:
        nodes=[n for n in body.all() if n.attrs.get('data-diagram')==d['id']]
        if len(nodes)!=1: raise ValueError('Diagram marker mismatch')
        nodes[0].replace(f'<figure class="diagram"><img src="assets/diagrams/{d["id"]}.svg" alt="Commutative diagram from the manuscript; its arrows and comparisons are described in the surrounding text."></figure>')
    for statement in body.all('section'):
        if statement.has('statement') and statement.attrs.get('data-scope')=='categorical':
            statement.attrs['aria-label']='Statement with intended validity in categorical contexts'
    inserted={}
    for p in MANIFEST['passages']:
        if p.get('tex_label'):
            anchor=ids[p['tex_label']]
            trigger=parse('<a class="agda-trigger agda-point" id="text-'+p['id']+'" href="#agda-'+p['id']+'" data-agda="'+p['id']+'">Agda</a>').children[0]
            trigger.parent=anchor.parent
            anchor.parent.children.insert(anchor.parent.children.index(anchor)+1,trigger)
            ids['text-'+p['id']]=trigger
        trigger=ids.get('text-'+p['id'])
        if trigger is None: raise ValueError('Missing explicit TeX marker: '+p['id'])
        trigger.attrs['title']='Agda: '+', '.join(d['name'] for d in p['declarations'])
        trigger.attrs['aria-controls']='agda-'+p['id']
        if trigger.text().strip()=='Agda' and not trigger.has('agda-point'): trigger.attrs['class']+=' agda-point'
        target=trigger
        while target.parent is not body and target.tag not in ('p','dd','li','div'):
            target=target.parent
        parent=target.parent
        last=inserted.get(id(target),target)
        panel=parse(agda.panel(p)).children[0]; panel.parent=parent
        parent.children.insert(parent.children.index(last)+1,panel)
        inserted[id(target)]=panel
    from reader_context import build_reader_data
    build_reader_data(agda,MANIFEST)
    # Native proof disclosure leaves the manuscript proof displayed initially.
    for proof in list(body.all('div')):
        if proof.has('proof'):
            proof.replace('<details class="book-proof" open><summary>Proof</summary><div class="proof-content">'+''.join(c.html() if isinstance(c,Node) else escape(c) for c in proof.children)+'</div></details>')
    # Split only at top-level section headings after all semantic joins.
    children=body.children; headings=[i for i,n in enumerate(children) if isinstance(n,Node) and n.has('sectionHead')]
    if len(headings)!=2: raise ValueError(f'Expected two top-level section headings, got {len(headings)}')
    segments={'chapter-introduction':children[:headings[0]],'basic-vocabulary':children[headings[0]:headings[1]],'equivalences':children[headings[1]:]}
    route={}
    for slug,nodes in segments.items():
        root=Node(); root.children=nodes
        for n in root.all():
            if 'id' in n.attrs: route[n.attrs['id']]=slug+'.html'
    for a in body.all('a'):
        href=a.attrs.get('href','')
        if href=='pilot.html' and not a.text().strip():
            del a.attrs['href']
        if href.startswith('outside-selection.html#'):
            fragment=href.split('#',1)[1]
            external_labels=[e['label'] for e in json.loads(read(BUILD/'external.json'))]
            restored=[l for l in external_labels if l.replace(':','_')==fragment]
            if len(restored)!=1: raise ValueError('Outside-pilot anchor changed')
            a.attrs['href']='outside-selection.html#'+restored[0]
        if href.startswith('pilot.html#') or href.startswith('#'):
            fragment=unquote(href.split('#',1)[1]); fragment=next((l for l in selection['labels'] if l.replace(':','_')==fragment),fragment)
            aliases={}
            for m in re.finditer(r'\\newlabel\{([^}@]+)\}\{\{\\rEfLiNK\{([^}]+)\}',read(BUILD/'pilot.aux')):
                if m[1] in route: aliases.setdefault(m[2],m[1])
            fragment=aliases.get(fragment,fragment)
            if fragment not in route: raise ValueError(f'Unresolved TeX fragment: {href}')
            a.attrs['href']=route[fragment]+'#'+fragment
    titles={'chapter-introduction':'The language of synthetic category theory','basic-vocabulary':'The basic vocabulary','equivalences':'Equivalences of categories'}
    for slug,nodes in segments.items():
        content=''.join(n.html() if isinstance(n,Node) else escape(n) for n in nodes)
        if slug!='chapter-introduction':
            content='<p class="agda-help">Click dotted-underlined prose to read its Agda code alongside the book. <a href="code-index.html">Browse all code</a>.</p>'+content
        content+='<nav class="page-turns">'+('<a href="basic-vocabulary.html">← The basic vocabulary</a>' if slug=='equivalences' else '<a href="equivalences.html">Equivalences of categories →</a>')+'</nav>'
        write(SITE/(slug+'.html'),page(titles[slug],content,slug))
    write(SITE/'assets/math-config.js','window.MathJax = '+json.dumps(math_config(),ensure_ascii=False)+';\n')
    shutil.copyfile(BUILD/'agda/Agda.css',SITE/'assets/Agda.css')
    # Keep all dependency modules and compiler anchors in the same release.
    (SITE/'agda').mkdir(exist_ok=True)
    current_modules={f.name for f in (BUILD/'agda').glob('*.html')}
    for stale in (SITE/'agda').glob('*.html'):
        if stale.name not in current_modules: stale.unlink()
    passages={p['id']:p for p in MANIFEST['passages']+MANIFEST.get('reverse_only',[])}
    def reverse_links(module):
        linked=[p for p in passages.values() if any(MANIFEST['module_prefix']+d['module']==module for d in p['declarations'])]
        if not linked: return ''
        return '<details class="module-book-passages"><summary>Corresponding book passages</summary><ul>'+''.join('<li><a href="../'+p['page']+'.html#text-'+p['id']+'">'+escape(p['title'])+'</a></li>' for p in linked)+'</ul></details>'
    for file in (BUILD/'agda').glob('*.html'):
        source_tree=parse(read(file)); pre=next(source_tree.all('pre'))
        content='<p class="module-caption">Complete compiler-highlighted source. Follow a symbol to its declaration.</p>'+reverse_links(file.stem)+pre.html()
        write(SITE/'agda'/file.name,page(file.stem,content,math=False,prefix='../'))
    from source_index import build_index
    inventory=build_index(page,current_modules,MANIFEST)
    dump(BUILD/'build-info.json',{'inputs':inputs,'correspondence_hash':digest((ROOT/'correspondence.json').read_bytes()),'verification':receipt,'passages':agda.resolved,'source_inventory':inventory,'selection':{'sections':selection['sections'],'diagrams':[d['id'] for d in selection['diagrams']]}})
    landing='''<p class="lede">The opening of the book, with optional access to its Agda formalization.</p>
<p>This experimental site renders Sections 1.1 and 1.2 from the annotated manuscript. The mathematical text and proofs are readable on their own. Click a subtly underlined passage to reveal its Agda code. Code stays hidden until requested. Hovering identifies the associated declarations.</p>
<h2>About this experiment</h2>\n<p>This site is an experiment carried out by Bastiaan Cnossen. It renders two sections of the opening chapter of <em>Synthetic category theory</em>, a book in preparation with Denis-Charles Cisinski and Tashi Walde, together with an Agda formalization of the same material. The conversion pipeline, the reader interface, and the presentation around the mathematics were produced with substantial AI assistance.</p>\n<p>My coauthors are aware of the experiment. They have not endorsed it, and in particular do not necessarily endorse its AI-generated nature. Responsibility for this site rests with me alone; the mathematics is drawn from the joint manuscript, and any error introduced by the conversion is mine.</p>\n<div class="chapter-card-grid"><article class="chapter-card"><p class="eyebrow">Section 1.1</p><h2><a href="basic-vocabulary.html">The basic vocabulary</a></h2><p>Categories, functors, natural isomorphisms, and the coherence axioms.</p></article><article class="chapter-card"><p class="eyebrow">Section 1.2</p><h2><a href="equivalences.html">Equivalences of categories</a></h2><p>Equivalence calculus and finite compatibility of products.</p></article></div>
<p><a href="chapter-introduction.html">Read the chapter introduction</a> · <a href="book.pdf">Download the web edition PDF</a></p>
<h2>Try the formalization</h2><ol><li><a href="basic-vocabulary.html#agda-joint-interchange">Joint interchange</a>: a primitive field, with derived restrictions.</li><li><a href="equivalences.html#agda-composite-of-equivalences">Composition of equivalences</a>: a checked signature and its proof.</li><li><a href="equivalences.html#lem:Finite_Compatibility_Of_Products">Finite compatibility of products</a>: four clauses, each linked to several formal declarations.</li></ol>
<p>This edition contains 135 explicit passage links. The <a href="code-index.html">complete Agda index</a> also exposes checked supporting source. Absence of a passage link does not imply missing formalization. <a href="formalization.html">Read the integration guide</a>.</p>'''
    landing=landing.replace('135 explicit passage links',str(len(MANIFEST['passages']))+' explicit passage links')
    write(SITE/'index.html',page('Synthetic category theory',landing,'index'))
    external='<p>These references point to exercises later in the same chapter. Their numbers are obtained from a fresh LaTeX compilation of the complete source chapter. Their full statements are outside the current web selection.</p>'
    for e in json.loads(read(BUILD/'external.json')):
        external+=f'<section id="{e["label"]}"><h2>Exercise {e["number"]}</h2><p>This exercise is outside the current web selection.</p></section>'
    write(SITE/'outside-selection.html',page('References beyond the selection',external))
    for slug,title in [('formalization','Reading the Agda formalization'),('build-report','Build and coverage')]:
        content=read(ROOT/'docs'/(slug+'.html'))
        if slug=='build-report':
            content+=f'<h2>Recorded build</h2><p>{escape(receipt["agda"])}. Aggregate: <code>{receipt["aggregate"]}</code>.</p><p>{len(agda.resolved)} declaration mappings; {len(selection["diagrams"])} SVG diagram displays.</p>'
        write(SITE/(slug+'.html'),page(title,content,slug))
    dump(SITE/'build-info.json',{'agda':receipt['agda'],'aggregate':receipt['aggregate'],'declaration_mappings':len(agda.resolved),'published_modules':[e['module'] for e in inventory],'compiled_modules':sorted(file.stem for file in (BUILD/'agda').glob('*.html')),'diagrams':[d['id'] for d in selection['diagrams']]})
    print(f'Assembled web edition with {len(agda.resolved)} checked declaration mappings.')

if __name__=='__main__': assemble()
