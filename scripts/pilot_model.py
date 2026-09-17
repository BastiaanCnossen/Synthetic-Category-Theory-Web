"""Explicit passage markers and layout-aware declaration ranges for the pilot."""
from common import *

def tex_markers(source, html=False, registry=None):
    """Read publication comments without making prose part of a TeX command.

    Marker comments consume their newline exactly like ordinary TeX comments.
    Both standalone comments and comments at exact inline boundaries are valid.
    Label-backed passages are returned for the assembler to attach to the
    rendered environment; they do not introduce a second inline link here.
    """
    entries=[] if registry is None else registry.get('passages',[])+registry.get('reverse_only',[])
    known={p['id']:p for p in entries}
    reverse={p['id'] for p in (registry or {}).get('reverse_only',[])}
    if len(known)!=len(entries): raise ValueError('Duplicate passage ID in correspondence registry')

    # Only the first unescaped percent begins a TeX comment. A publication
    # marker mentioned inside an ordinary comment is therefore just prose.
    chunks=[]; events=[]; length=0
    for line in source.splitlines(keepends=True):
        comment=None
        for m in re.finditer('%',line):
            backslashes=len(line[:m.start()])-len(line[:m.start()].rstrip('\\'))
            if backslashes%2==0: comment=m.start(); break
        if comment is not None and line[comment:].startswith('%!%'):
            marker=line[comment:].rstrip('\r\n')
            match=re.fullmatch(r'%!%\s+(begin|end|paragraph|point)\s+([a-z0-9]+(?:-[a-z0-9]+)*)\s*',marker)
            if not match: raise ValueError('Malformed publication marker: '+marker)
            prefix=line[:comment]; chunks.append(prefix); length+=len(prefix)
            events.append((length,match[1],match[2]))
        else:
            chunks.append(line); length+=len(line)
    plain=''.join(chunks)

    # Mask comments at their original offsets for TeX token and label checks.
    masked=[]
    for line in plain.splitlines(keepends=True):
        at=None
        for m in re.finditer('%',line):
            backslashes=len(line[:m.start()])-len(line[:m.start()].rstrip('\\'))
            if backslashes%2==0: at=m.start(); break
        # A comment consumes its newline, so it must not create a paragraph
        # boundary in the structural view. Spaces preserve source offsets.
        masked.append(line if at is None else line[:at]+' '*len(line[at:]))
    semantic=''.join(masked)
    if re.search(r'\\Agda(?:Link|Point|Anchor)\b',semantic):
        raise ValueError('Legacy Agda prose commands must be replaced by %!% comments')

    found=[]; ranges=[]; active=None
    for at,kind,pid in events:
        if registry is not None and pid not in known: raise ValueError('Unknown TeX passage ID: '+pid)
        if kind=='end':
            if active is None or active[0]!=pid: raise ValueError('Unmatched or crossed end marker: '+pid)
            ranges.append((active[1],at,pid,'begin')); active=None
            continue
        if active is not None: raise ValueError('Nested publication markers: '+pid)
        if pid in found: raise ValueError('Duplicate TeX passage ID: '+pid)
        if known.get(pid,{}).get('tex_label'): raise ValueError('Passage has both a label and a comment marker: '+pid)
        found.append(pid)
        if kind=='begin': active=(pid,at)
        elif kind=='point': ranges.append((at,at,pid,kind))
        else:
            following=re.search(r'\S',semantic[at:])
            if following is None: raise ValueError('Paragraph marker has no following paragraph: '+pid)
            start=at+following.start()
            boundary=re.search(r'\n[ \t\r]*\n',semantic[start:])
            end=start+boundary.start() if boundary else len(plain)
            ranges.append((start,end,pid,kind))
    if active is not None: raise ValueError('Unclosed begin marker: '+active[0])
    for start,end,pid,kind in ranges:
        if kind!='point' and not semantic[start:end].strip(): raise ValueError('Empty passage: '+pid)
        if kind=='paragraph' and any(start<=at<end and other!=pid for at,_,other in events):
            raise ValueError('Nested publication markers in paragraph: '+pid)
        if kind!='point':
            content=semantic[start:end]
            if (re.search(r'\\(?:begin|end|part|chapter|section|subsection|subsubsection|paragraph|subparagraph|item|par)\b|\\[\[\]]|(?<!\\)\$\$',content)
                    or re.search(r'\n[ \t\r]*\n',content)):
                raise ValueError('A passage cannot cross TeX block boundaries; use an existing label or a point marker: '+pid)

    math_environments=r'(?:equation|align|alignat|gather|multline|flalign|displaymath|math)\*?'
    tokens=re.compile(r'(?<!\\)\$\$?|\\[\[\]()]|\\(?:begin|end)\{'+math_environments+r'\}')
    def in_math(at):
        stack=[]
        for token in tokens.finditer(semantic,0,at):
            value=token[0]
            if value.startswith(r'\begin{'): stack.append(value[7:-1])
            elif value.startswith(r'\end{'):
                if stack: stack.pop()
            elif value in (r'\[',r'\('): stack.append(value)
            elif value in (r'\]',r'\)'):
                if stack: stack.pop()
            elif stack and stack[-1]==value: stack.pop()
            else: stack.append(value)
        return bool(stack)
    hyperlinks=[]
    for command in re.finditer(r'\\(Cref|cref|ref|eqref|autoref|href|url|hyperref|hyperlink)\b\*?',semantic):
        pos=command.end()
        while pos<len(semantic) and semantic[pos].isspace(): pos+=1
        while pos<len(semantic) and semantic[pos]=='[':
            _,pos=group(semantic,pos,'[',']')
            while pos<len(semantic) and semantic[pos].isspace(): pos+=1
        for _ in range(2 if command[1] in ('href','hyperlink') else 1):
            _,pos=group(semantic,pos)
        hyperlinks.append((command.start(),pos))
    for start,end,pid,kind in ranges:
        if in_math(start) or in_math(end):
            raise ValueError('Place publication boundaries outside math delimiters: '+pid)
        if pid not in reverse and any((start<b and end>a) or a<start<b for a,b in hyperlinks):
            raise ValueError('A linked passage cannot contain another hyperlink: '+pid)

    labels={}
    for label in re.finditer(r'\\label(?:\[[^\]]*\])?\s*\{([^{}]+)\}',semantic):
        labels.setdefault(label[1],[]).append(label.start())
    for entry in entries:
        label=entry.get('tex_label')
        if not label or label not in labels: continue
        if len(labels[label])!=1: raise ValueError('Duplicate TeX label: '+label)
        found.append(entry['id'])
    if not html: return plain,found

    insertions=[]
    for start,end,pid,kind in ranges:
        if pid in reverse:
            opening=r'\HCode{<span class="agda-book-anchor" tabindex="-1" id="text-'+pid+'">}'
            closing=r'\HCode{</span>}'
        else:
            opening=r'\HCode{<a class="agda-trigger" id="text-'+pid+r'" href="\#agda-'+pid+'" data-agda="'+pid+'">}'
            closing=r'\HCode{</a>}'
        if kind=='point': insertions.append((start,1,opening+('' if pid in reverse else 'Agda')+closing))
        else:
            insertions.append((start,2,opening)); insertions.append((end,0,closing))
    out=[]; cursor=0
    for at,_,content in sorted(insertions):
        out.append(plain[cursor:at]); out.append(content); cursor=at
    return ''.join(out)+plain[cursor:],found

def scopes(source):
    """Record/module scopes with explicit layout boundaries, excluding let blocks."""
    # Literate prose between Agda fences does not end an indented module.
    # Mask it without moving offsets used by compiler declaration anchors.
    if '```agda' in source:
        code=False; masked=[]
        for line in source.splitlines(keepends=True):
            fence=line.startswith('```')
            if fence: code=line.startswith('```agda')
            masked.append(line if code and not fence else re.sub(r'[^\r\n]', ' ', line))
        layout=''.join(masked)
    else:
        layout=source
    result=[]
    for m in re.finditer(r'^( *)(record|module)\s+([^\s{(:]+)',layout,re.M):
        indent=len(m[1]); end=layout.find('where',m.end())
        if end<0: continue
        header=source[m.start():end+5]
        # A scope ends at a non-comment declaration at its own layout level.
        boundary=len(source)
        for line in re.finditer(r'^([^\n]*)(?:\n|$)',layout[end+5:],re.M):
            value=line[1]; at=end+5+line.start()
            if source.startswith('```',at) and m[2]=='record': boundary=at; break
            if at==end+5 or not value.strip(): continue
            if value.startswith('```') and m[2]=='record': boundary=at; break
            if value.lstrip().startswith('--'):
                if value.lstrip().startswith('--!'): continue
                if len(value)-len(value.lstrip(' '))<=indent: boundary=at; break
                continue
            if value.startswith('```'): continue
            if len(value)-len(value.lstrip(' '))<=indent:
                boundary=at; break
        # A top-level module header scopes the entire file, despite indentation.
        if m[2]=='module' and '.' in m[3]: boundary=len(source)
        result.append({'name':m[3],'start':m.start(),'body':end+5,'end':boundary,'indent':indent,'header':header,'kind':m[2]})
    return result

def declaration_range(source,name,qualified=None):
    pattern=r'^( *)(?:(record|data)\s+)?'+re.escape(name)+r'(?=\s|\{|:)[^\n]*'
    candidates=[]; ss=scopes(source)
    for m in re.finditer(pattern,source,re.M):
        if not m[2] and not re.match(r'^ *'+re.escape(name)+r'\s*:',m[0]): continue
        enclosing=[s for s in ss if s['start']<m.start()<s['end']]
        parts=[s['name'] for s in enclosing if '.' not in s['name']]
        q='.'.join(parts+[name])
        if qualified and q!=qualified: continue
        candidates.append((m,enclosing,q))
    if len(candidates)!=1: raise ValueError(f'Ambiguous/missing declaration {qualified or name}: {len(candidates)}')
    m,enclosing,q=candidates[0]; start=m.start(); indent=len(m[1]); proof=None; end=len(source)
    if m[2]:
        scope=next(s for s in ss if s['start']==start)
        proof=scope['body']; end=scope['end']
    else:
        lines=list(re.finditer(r'^[^\n]*(?:\n|$)',source[m.end():],re.M))
        for line in lines:
            value=line[0]; at=m.end()+line.start()
            if at==m.end(): continue
            if value.startswith('```'): end=at; break
            if not value.strip(): continue
            if value.lstrip().startswith('-- @sct-link '): end=at; break
            if value.lstrip().startswith('--'): continue
            pad=len(value)-len(value.lstrip(' '))
            if pad<=indent:
                # Infix definitions need not begin with the mixfix name.
                if proof is None and (re.match(r'^ *'+re.escape(name)+r'(?:\s|\{|=)',value) or (name.startswith('_') and '=' in value)):
                    proof=at
                elif proof is not None and (value.lstrip().startswith(name+' ') or value.lstrip().startswith(name+'{')): continue
                else: end=at; break
    while end>start and source[end-1].isspace(): end-=1
    namepos=source.index(name,start,m.end())
    return {'start':start,'proof':proof,'end':end,'namepos':namepos,'qualified':q,'scopes':enclosing,'kind':m[2] or 'declaration'}

def prelude(source,entry):
    first=source.find('```agda')
    begin=first+len('```agda') if first>=0 else 0
    top=next((s for s in entry['scopes'] if '.' in s['name']),None)
    text=source[begin:top['body']].strip() if top else ''
    for s in entry['scopes']:
        if '.' not in s['name']: text+='\n\n'+s['header']
    return text
