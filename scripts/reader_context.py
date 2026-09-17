"""Compiler-highlighted module lines and precise passage focus for the side reader."""
from common import *
from pilot_model import declaration_range
from agda_regions import region_ranges

def focused_lines(source, loc, declaration):
    """Select explicit source regions or the declaration's default signature.

    A region must contain code inside its enclosing declaration. Marker lines
    never contribute to the returned source-line selection.
    """
    if 'focus_note' in declaration:
        raise ValueError('Legacy focus_note must be migrated to stable regions')
    def lines(a, b):
        if b <= a:
            raise ValueError('Empty Agda selection')
        return list(range(source.count('\n', 0, a) + 1,
                          source.count('\n', 0, b - 1) + 2))
    if 'regions' not in declaration:
        end = loc['end'] if loc['kind'] == 'record' else loc['proof'] or loc['end']
        selected = lines(loc['start'], end)
    else:
        names = declaration['regions']
        if (not isinstance(names, list) or not names or
                any(not isinstance(name, str) for name in names) or
                len(set(names)) != len(names)):
            raise ValueError('regions must be a nonempty list of unique region names')
        available = region_ranges(source)
        selected = []
        for name in names:
            if name not in available:
                raise ValueError('Missing Agda region: ' + name)
            region = available[name]
            content = source[region['start']:region['end']]
            first = region['start'] + len(content) - len(content.lstrip())
            last = region['start'] + len(content.rstrip())
            if not (loc['start'] <= first < last <= loc['end']):
                raise ValueError('Agda region lies outside its declaration: ' + name)
            selected.extend(lines(region['start'], last))
    raw_lines = source.split('\n')
    return sorted({number for number in selected
                   if not raw_lines[number - 1].lstrip().startswith('--!')})

def module_lines(source,pre):
    """Split highlighted tokens without copying compiler IDs into the page."""
    region_ranges(source)  # Fail on malformed source markers before hiding them.
    rendered=['']
    for child in pre.children:
        raw=child if isinstance(child,str) else child.text()
        attrs={} if isinstance(child,str) else {k:v for k,v in child.attrs.items() if k not in ('id','name')}
        if 'href' in attrs: attrs['href']='agda/'+attrs['href']
        attributes=''.join(f' {k}="{escape(v or "",quote=True)}"' for k,v in attrs.items())
        for i,part in enumerate(raw.split('\n')):
            if i: rendered.append('')
            if part:
                value=escape(part,quote=False)
                rendered[-1]+=f'<a{attributes}>{value}</a>' if attrs else value
    original=source.split('\n')
    if len(rendered)!=len(original): raise ValueError('Compiler line count differs')
    code='```agda' not in source; result=[]
    for number,(raw,html) in enumerate(zip(original,rendered),1):
        if raw.startswith('```'):
            code=raw.startswith('```agda'); continue
        if not code or '-- @sct-link ' in raw or raw.lstrip().startswith('--!'): continue
        if parse(html).text()!=raw: raise ValueError('Compiler line text differs')
        result.append({'number':number,'html':html})
    return result

def compiler_anchors(pre,available):
    """Resolve compiler IDs to their source lines, including local binders."""
    anchors={}; line=1
    for child in pre.children:
        if not isinstance(child,str):
            anchor=child.attrs.get('id')
            if anchor and line in available: anchors[anchor]=line
        line+=(child if isinstance(child,str) else child.text()).count('\n')
    return anchors

def build_reader_data(agda,manifest):
    data={'modules':{},'passages':{}}
    all_passages=manifest['passages']+manifest.get('reverse_only',[])
    for p in all_passages:
        declarations=[]
        for d in p['declarations']:
            name,source,pre,src=agda.module(d['module'])
            if name not in data['modules']:
                data['modules'][name]={'lines':module_lines(source,pre),'source_sha256':digest(source)}
            loc=declaration_range(source,d['name'],d['qualified'])
            focus=focused_lines(source,loc,d)
            available={line['number'] for line in data['modules'][name]['lines']}
            focus=[line for line in focus if line in available]
            if not focus: raise ValueError('Empty passage focus: '+p['id'])
            body=list(range(source.count('\n',0,loc['start'])+1,source.count('\n',0,loc['end']-1)+2))
            declarations.append({'module':name,'name':d['name'],'qualified':d['qualified'],'range':body,
                'role':d['role'],'focus':focus,'regions':d.get('regions',[]),
                'href':'agda/'+name+'.html#'+str(loc['namepos']+1)})
        data['passages'][p['id']]={'title':p['title'],'note':p['note'],'page':p['page'],
            'reverse_only':p in manifest.get('reverse_only',[]),'declarations':declarations}
    # Include the entire checked dependency closure for in-panel definition jumps.
    for file in (BUILD/'agda').glob('*.html'):
        pre=next(parse(read(file)).all('pre')); source=pre.text()
        if file.stem not in data['modules']:
            data['modules'][file.stem]={'lines':module_lines(source,pre),'source_sha256':digest(source)}
        payload=data['modules'][file.stem]
        payload['checked']=True
        payload['href']='agda/'+file.name
        payload['anchors']=compiler_anchors(pre,{line['number'] for line in payload['lines']})
    for module,payload in data['modules'].items():
        for line in payload['lines']:
            candidates={}
            for pid,p in data['passages'].items():
                for d in p['declarations']:
                    if d['module']!=module or line['number'] not in d['range']: continue
                    direct=line['number'] in d['focus']
                    rank=(0 if p['reverse_only'] else 1 if direct else 2,
                          len(d['focus']) if direct else len(d['range']))
                    if pid not in candidates or rank<candidates[pid]: candidates[pid]=rank
            line['targets']=[{'id':pid,'rank':list(rank)} for pid,rank in sorted(candidates.items(),key=lambda item:(item[1],item[0]))]
    dump(BUILD/'agda-context.json',data)
    write(SITE/'assets/agda-context.js','window.SCT_AGDA = '+json.dumps(data,ensure_ascii=False)+';\n')
    return data
