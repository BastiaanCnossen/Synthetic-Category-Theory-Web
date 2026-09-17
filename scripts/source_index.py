"""Publish only the checked source closure selected for this web edition."""
from common import *
from urllib.parse import quote
from pilot_model import scopes
from module_navigation import module_tree, module_label

def build_index(page, compiled, manifest, site=SITE):
    sources=SNAP/'agda/src'
    entries=[]; rows={}
    for src in sorted(sources.rglob('*')):
        if not (src.suffix=='.agda' or src.name.endswith('.lagda.md')): continue
        rel=src.relative_to(sources).as_posix()
        module=rel.removesuffix('.lagda.md').removesuffix('.agda').replace('/','.')
        checked=module+'.html' in compiled
        if not checked: continue
        href='agda/'+module+'.html'
        # Publish raw source separately from the private build snapshot.
        raw=quote('source-files/'+rel)
        write(site/'source-files'/rel,read(src))
        linked=[p for p in manifest['passages']+manifest.get('reverse_only',[]) if any(manifest['module_prefix']+d['module']==module for d in p['declarations'])]
        status='Checked aggregate' if checked else 'Source only: outside this check'
        entries.append({'module':module,'source':rel,'checked':checked,'href':href,'passages':len(linked)})
        back=''.join(f'<li><a href="{p["page"]}.html#text-{p["id"]}">{escape(p["title"])}</a></li>' for p in linked)
        rows[module]=f'<article class="code-index-entry" data-module="{escape(module)}"><h3><a href="{href}" title="{escape(module)}">{escape(module_label(module))}</a></h3><p class="module-qualified">{escape(module)}</p><p>{status} · <a href="{raw}">Source file</a></p>'+(f'<details><summary>{len(linked)} book passages</summary><ol>{back}</ol></details>' if linked else '')+'</article>'
    for filename in sorted(compiled):
        module=filename.removesuffix('.html')
        if module not in rows:
            rows[module]=f'<article class="code-index-entry" data-module="{escape(module)}"><h3><a href="agda/{filename}">{escape(module)}</a></h3><p>Compiler support</p></article>'
    def group_html(node):
        inside=''.join(rows[module] for module in node['modules'])
        inside+=''.join(group_html(child) for child in node['children'])
        if not node['key']: return inside
        return f'<details class="module-group" data-label="{escape(node["label"])}"><summary>{escape(node["label"])}</summary><div class="module-group-content">{inside}</div></details>'
    symbols=[]
    for file in sorted((BUILD/'agda').glob('*.html')):
        if not file.stem.startswith('SCT.'): continue
        tree=parse(read(file))
        named={n.attrs['id'] for n in tree.all('a') if n.attrs.get('id') and not n.attrs['id'].isdigit()}
        src=next((sources/e['source'] for e in entries if e['module']==file.stem),None)
        source=read(src) if src else ''
        context=scopes(source)
        seen=set()
        for n in tree.all('a'):
            anchor=n.attrs.get('id','')
            if anchor and not anchor.isdigit():
                if anchor in seen: continue
                seen.add(anchor)
                symbols.append(f'<li class="symbol-entry"><a href="agda/{file.name}#{quote(anchor)}"><code>{escape(file.stem+"."+anchor)}</code></a></li>')
            elif anchor.isdigit() and n.has('Field') and n.attrs.get('href')==file.name+'#'+anchor:
                position=int(anchor)-1
                owners=[s['name'] for s in context if s['start']<position<s['end'] and '.' not in s['name']]
                qualified='.'.join(owners+[n.text()])
                if qualified not in named:
                    symbols.append(f'<li class="symbol-entry"><a href="agda/{file.name}#{anchor}"><code>{escape(file.stem+"."+qualified)}</code></a></li>')
    checked=sum(e['checked'] for e in entries)
    content=f'<p class="lede">The checked modules supporting these sections are accessible here.</p><p>{checked} source modules included in the fresh aggregate check. Compiler support modules are also reachable through symbol links.</p>'
    content+='<label class="code-search">Find a module or declaration <input type="search" id="code-search" placeholder="CAT, equiv-compose, Coherence…"></label><p id="search-count" aria-live="polite"></p>'
    content+='<h2>Modules</h2><div class="module-tree">'+group_html(module_tree(rows))+'</div><details class="symbol-index"><summary>All named declarations in checked SCT modules</summary><ul>'+''.join(symbols)+'</ul></details>'
    write(site/'code-index.html',page('Agda code for these sections',content,'code-index',math=False))
    return entries
