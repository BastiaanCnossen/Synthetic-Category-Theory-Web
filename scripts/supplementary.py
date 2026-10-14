"""Web-only TeX notes, with a separate conversion cache and reader metadata."""
from common import *
from pilot_model import tex_markers, declaration_range
from reader_context import focused_lines
from source_anchors import conversion_anchor
import subprocess

NOTES = ROOT/'Supplementary notes'
NOTICE = ('AI-generated prose accompanying the Agda code. This note is supplementary '
          'to the book and is not part of the authors\' manuscript.')


def catalog():
    return json.loads(read(NOTES/'notes.json'))


def fingerprint(note):
    return digest(read(NOTES/note['source'])+read(NOTES/'preamble.tex')+
                  json.dumps(note,sort_keys=True)+read(Path(__file__)))


def convert_notes():
    for note in catalog():
        work=BUILD/'supplementary'/note['slug']
        receipt=work/'input.sha256'
        if receipt.exists() and read(receipt)==fingerprint(note) and (work/'html/note.html').exists():
            continue
        source,found=tex_markers(read(NOTES/note['source']),html=True,registry=note)
        if set(found)!={p['id'] for p in note['passages']}:
            raise ValueError('Supplementary TeX/registry mismatch: '+note['slug'])
        source=re.sub(r'(\\href\{[^{}]+\\#)([^{}]+)(\})',lambda m:m[1]+conversion_anchor(m[2])+m[3],source)
        source=re.sub(r'\\begin\{(lemma|corollary)\}',lambda m:
            '\\par\\HCode{<section class="statement supplementary-statement">}'+m[0],source)
        source=re.sub(r'\\end\{(lemma|corollary)\}',lambda m:m[0]+'\\par\\HCode{</section>}',source)
        source=re.sub(r'\\label\[(?:lemma|corollary)\]\{([^}]+)\}',lambda m:
            m[0]+'\\HCode{<span id="'+conversion_anchor(m[1])+'"></span>}',source)
        write(work/'note.tex',source)
        write(work/'preamble.tex',read(NOTES/'preamble.tex'))
        with (work/'conversion.log').open('w',encoding='utf-8') as log:
            subprocess.run(['make4ht','-a','warning','-f','html5','-d','html',
                            'note.tex','mathjax,charset=utf-8'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
        from validate import validate_tex_log
        validate_tex_log(work/'note.log')
        write(receipt,fingerprint(note))


def rendered_note(note):
    work=BUILD/'supplementary'/note['slug']
    if not (work/'input.sha256').exists() or read(work/'input.sha256')!=fingerprint(note):
        raise ValueError('Convert supplementary notes first: python scripts/supplementary.py --convert')
    tree=parse(read(work/'html/note.html')); body=next(tree.all('body'))
    for p in note['passages']:
        if not p.get('tex_label'): continue
        anchor=next(n for n in body.all() if n.attrs.get('id')==conversion_anchor(p['tex_label']))
        anchor.attrs['id']=p['tex_label']
        statement=anchor.parent
        while not statement.has('supplementary-statement'): statement=statement.parent
        heading=next(n for n in statement.all() if n.has('head'))
        name=next(n for n in heading.children if isinstance(n,Node) and n.text().strip())
        name.replace('<a class="agda-trigger" id="text-'+p['id']+'" data-agda="'+p['id']+
                     '" href="#agda-'+p['id']+'">'+name.html()+'</a>')
    for proof in list(body.all('div')):
        if proof.has('proof'):
            for head in list(proof.all()):
                if head.has('head'): head.replace('')
            proof.replace('<details class="book-proof" open><summary>Proof idea</summary><div class="proof-content">'+
                          ''.join(c.html() if isinstance(c,Node) else escape(c) for c in proof.children)+'</div></details>')
    book_targets={conversion_anchor(m[1]):m[1] for m in re.finditer(r'\\href\{[^{}]+\\#([^{}]+)\}',read(NOTES/note['source']))}
    for a in body.all('a'):
        href=a.attrs.get('href','')
        if '#' in href and href.split('#')[1] in book_targets:
            a.attrs['href']=href.split('#')[0]+'#'+book_targets[href.split('#')[1]]
        if href.startswith('note.html#'): a.attrs['href']='#'+href.split('#',1)[1]
    return ''.join(n.html() if isinstance(n,Node) else escape(n) for n in body.children)


def section_notes(slug, prefix='', *, heading=True, descriptions=False):
    notes=[n for n in catalog() if n['section']==slug or slug in n.get('related_sections',[])]
    if not notes: return ''
    return '<section class="supplementary-links">'+('<h2>Supplementary notes</h2>' if heading else '')+'<ul>'+''.join(
        f'<li><a href="{prefix}{n["slug"]}.html">{escape(n["title"])}</a> <span class="ai-label">AI-generated</span>'+
        ('<p>'+escape(n['description'])+'</p>' if descriptions else '')+'</li>'
        for n in notes)+'</ul></section>'


def reader_metadata(agda):
    data={'passages':{},'explanations':{},'inputs':{}}
    for note in catalog():
        data['inputs'][note['slug']]=fingerprint(note)
        for p in note['passages']:
            declarations=[]
            for d in p['declarations']:
                module,source,pre,_=agda.module(d['module'])
                loc=declaration_range(source,d['name'],d['qualified'])
                anchor=str(loc['namepos']+1)
                if not any(a.attrs.get('id')==anchor and a.text()==d['name'] for a in pre.all('a')):
                    raise ValueError('Supplementary target is not a checked compiler declaration: '+d['qualified'])
                declarations.append(dict(module=module,name=d['name'],qualified=d['qualified'],role=d['role'],
                    range=list(range(source.count('\n',0,loc['start'])+1,source.count('\n',0,loc['end']-1)+2)),
                    focus=focused_lines(source,loc,d),href='agda/'+module+'.html#'+anchor))
                explanation=dict(title=note['title'],href=note['slug']+'.html#text-'+p['id'])
                if explanation not in data['explanations'].setdefault(module,[]):
                    data['explanations'][module].append(explanation)
            data['passages'][p['id']]={**{k:p[k] for k in ('title','note','page')},
                'declarations':declarations,'reverse_only':False,'supplementary':True}
    return data


def module_explanations(module, data, prefix=''):
    entries=data['explanations'].get(module,[])
    if not entries: return ''
    # One link per note on module pages; the side reader can choose a passage.
    notes={e['href'].split('#')[0]:e['title'] for e in entries}
    return '<p class="supplementary-links">Explanation (AI-generated): '+', '.join(
        '<a href="'+prefix+href+'">'+escape(title)+'</a>' for href,title in notes.items())+'</p>'


def write_notes(page, agda, site=SITE):
    data=reader_metadata(agda)
    write(site/'assets/supplementary.js','window.SCT_SUPPLEMENTARY = '+json.dumps(data,ensure_ascii=False)+';\n')
    dump(BUILD/'supplementary/reader.json',data)
    index='<p>AI-generated prose accompanying the Agda code. These notes are supplementary to the book and are not part of the authors\' manuscript.</p>'
    for chapter in BOOK_CHAPTERS:
        selected=[n for n in catalog() if n['chapter']==chapter['number']]
        if not selected: continue
        index+=f'<details class="overview-chapter"><summary><h2>Chapter {chapter["number"]}: {escape(chapter["title"])}</h2></summary>'
        for section,title,_ in chapter['sections']:
            if any(n['section']==section or section in n.get('related_sections',[]) for n in selected):
                index+=f'<h3><a href="{section}.html">{escape(title)}</a></h3>'+section_notes(section,heading=False,descriptions=True)
        index+='</details>'
    write(site/'supplementary-notes.html',page('Supplementary notes',index,'supplementary-notes',supplementary=True))
    for note in catalog():
        module='SCT.VolumeI.'+note['entry_module']
        invite=('<p class="agda-help"><span class="agda-invitation"><a class="agda-start" data-module="'+module+
                '" href="agda/'+module+'.html">Read the Agda code</a> alongside this note.</span>'
                '<span class="agda-instructions">Click dotted-underlined statements to read their Agda code. '
                '<button type="button" class="agda-hide text-button">Hide links.</button> <a href="code-index.html">Browse all code.</a></span></p>')
        content=invite+rendered_note(note)
        content+='<section class="supplementary-targets"><h2>Checked declarations</h2><p>The linked Agda declarations were type-checked in the displayed edition. The explanatory prose and proof ideas are AI-generated and are not verified by that check.</p><ul>'
        for p in note['passages']:
            content+='<li id="agda-'+p['id']+'">'+escape(p['title'])+': '+', '.join(
                '<a href="'+d['href']+'"><code>'+escape(d['qualified'])+'</code></a>' for d in data['passages'][p['id']]['declarations'])+'</li>'
        content+='</ul></section>'
        write(site/(note['slug']+'.html'),page(note['title'],content,note['slug'],supplementary=True))
    return data


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(); parser.add_argument('--convert',action='store_true')
    if parser.parse_args().convert: convert_notes()
