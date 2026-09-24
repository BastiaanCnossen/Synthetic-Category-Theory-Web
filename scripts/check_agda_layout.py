"""Check source layout, imports, aggregate coverage and passage targets without Agda."""
from common import *
from pilot_model import declaration_range
from reader_context import focused_lines


def code_text(source):
    if '```agda' not in source:
        return source
    return '\n'.join(re.findall(r'```agda\s*\n(.*?)```',source,re.S))


def check():
    root=ROOT/'agda/src'
    modules={}
    for path in root.rglob('*'):
        if path.suffix!='.agda' and not path.name.endswith('.lagda.md'): continue
        name=path.relative_to(root).as_posix().removesuffix('.lagda.md').removesuffix('.agda').replace('/','.')
        if name in modules: raise ValueError('Duplicate module: '+name)
        source=read(path); code=code_text(source)
        declared=re.findall(r'^module (SCT\.[\w.]+)(?=\s)',code,re.M)
        if declared!=[name]: raise ValueError('Module/path mismatch: '+str(path))
        if '{-# OPTIONS --safe --without-K #-}' not in code: raise ValueError('Missing safe options: '+name)
        modules[name]={'path':path,'source':source,'imports':set(re.findall(r'\bimport (SCT\.[\w.]+)',code))}
    for name,data in modules.items():
        missing=data['imports']-modules.keys()
        if missing: raise ValueError('Unresolved imports in '+name+': '+str(sorted(missing)))
    visiting=[]; visited=set()
    def visit(name):
        if name in visiting: raise ValueError('Import cycle: '+' -> '.join(visiting+[name]))
        if name in visited: return
        visiting.append(name)
        for target in modules[name]['imports']: visit(target)
        visiting.pop(); visited.add(name)
    for name in modules: visit(name)
    def closure(name):
        result={name}
        for target in modules[name]['imports']: result.update(closure_cached(target))
        return result
    from functools import cache
    closure_cached=cache(closure)
    expected={name for name in modules if '.VolumeI.' in name}
    if not expected<=closure_cached('SCT.Everything'):
        raise ValueError('Full aggregate omits modules: '+str(sorted(expected-closure_cached('SCT.Everything'))))
    for name,data in modules.items():
        if re.fullmatch(r'SCT\.VolumeI\.Chapter\d+\.Section\d+\.Everything',name):
            siblings={n for n in modules if n.rsplit('.',1)[0]==name.rsplit('.',1)[0] and n!=name}
            if data['imports']!=siblings: raise ValueError('Section aggregate differs from its files: '+name)
    web=closure_cached('SCT.WebEdition')
    expected_web={n for n in modules if re.match(r'SCT\.VolumeI\.(?:Chapter01\.Section0[1-8]|Chapter02\.Section0[1-6])\.',n)}
    if not expected_web<=web: raise ValueError('Web aggregate omits selected modules')
    if any(re.match(r'SCT\.VolumeI\.Chapter(?!01\.|02\.)',n) for n in web):
        raise ValueError('Web aggregate unexpectedly imports later chapters/sections')
    manifest=json.loads(read(ROOT/'correspondence.json'))
    targets=0
    for passage in manifest['passages']+manifest.get('reverse_only',[]):
        for target in passage['declarations']:
            name=manifest['module_prefix']+target['module']
            if name not in web: raise ValueError('Passage target outside web aggregate: '+name)
            source=modules[name]['source']
            loc=declaration_range(source,target['name'],target['qualified'])
            if not focused_lines(source,loc,target): raise ValueError('Empty focus: '+passage['id'])
            targets+=1
    report={'status':'passed','source_modules':len(modules),'imports':sum(len(x['imports']) for x in modules.values()),
            'web_source_modules':len(web),'passages':len(manifest['passages'])+len(manifest.get('reverse_only',[])),
            'declaration_mappings':targets,'agda_invoked':False}
    dump(BUILD/'agda-layout-validation.json',report)
    print(json.dumps(report))
    return report


if __name__=='__main__': check()
