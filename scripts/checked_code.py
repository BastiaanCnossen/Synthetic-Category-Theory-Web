"""Refresh manuscript pages while retaining an explicitly older checked Agda edition."""
from common import *
from pilot_model import declaration_range
from module_layout import previous_module
import copy

RETAINED = BUILD / 'retained-agda-check.json'
# Explicit names from the author's pending notation migration, not fuzzy aliases.
PREVIOUS_NAMES = {'_=₁_':'=₁', '_=₂_':'=₂', '_=₃_':'=₃',
                  '＝-isAn':'iso-isAn', '＝-inv':'isoInv', '_⁻¹':'invIso', '⁻¹-pre':'invIso-pre'}

def agda_files(files):
    return {name:sha for name,sha in files.items() if name.startswith('agda/')}

def retain_checked_code():
    inputs=json.loads(read(SNAP/'inputs.json'))
    receipt=json.loads(read(BUILD/'check.json'))
    if not receipt.get('checked'): raise ValueError('No completed Agda check to retain')
    if receipt['input_hash']==digest(json.dumps(inputs['files'],sort_keys=True)):
        for name,sha in agda_files(inputs['files']).items():
            if digest((SNAP/name).read_bytes())!=sha: raise ValueError('Checked source changed: '+name)
        html={file.name:digest(file.read_bytes()) for file in (BUILD/'agda').glob('*') if file.suffix in ('.html','.css')}
        if not html: raise ValueError('Missing checked compiler output')
        dump(RETAINED,{'receipt':receipt,'original_inputs':inputs,'html':html})
    else:
        verify_checked_code(inputs)

def verify_checked_code(inputs):
    receipt=json.loads(read(BUILD/'check.json'))
    if not receipt.get('checked'): raise ValueError('No completed Agda check')
    if receipt['input_hash']==digest(json.dumps(inputs['files'],sort_keys=True)):
        return 'checked current snapshot'
    retained=json.loads(read(RETAINED))
    original=retained['original_inputs']
    if retained['receipt']!=receipt or receipt['input_hash']!=digest(json.dumps(original['files'],sort_keys=True)):
        raise ValueError('Retained check does not match its original inputs')
    if agda_files(inputs['files'])!=agda_files(original['files']):
        raise ValueError('Agda inputs changed; cannot retain the earlier check')
    for name,sha in agda_files(original['files']).items():
        if digest((SNAP/name).read_bytes())!=sha: raise ValueError('Retained Agda source changed: '+name)
    actual={file.name:digest(file.read_bytes()) for file in (BUILD/'agda').glob('*') if file.suffix in ('.html','.css')}
    if actual!=retained['html']: raise ValueError('Retained compiler output changed')
    return 'updated manuscript with previously checked Agda snapshot'

def publication_manifest():
    result=copy.deepcopy(json.loads(read(ROOT/'correspondence.json')))
    mode=verify_checked_code(json.loads(read(SNAP/'inputs.json')))
    if mode=='updated manuscript with previously checked Agda snapshot':
        result['scope_note']=(result.get('scope_note','')+' Canonical sources now follow the revised book structure; this reader retains the earlier checked names, notation, and declaration order until the final compiler check.').strip()
    for p in result['passages']+result.get('reverse_only',[]):
        renamed=False
        relocated=False
        for d in p['declarations']:
            rel=Path('agda/src')/Path(*(result['module_prefix']+d['module']).split('.')).with_suffix('.lagda.md')
            # Canonical targets must resolve even when displaying older code.
            declaration_range(read(ROOT/rel),d['name'],d['qualified'])
            if mode=='updated manuscript with previously checked Agda snapshot':
                canonical=result['module_prefix']+d['module']
                previous=previous_module(canonical,d['qualified'])
                if previous!=canonical:
                    d['module']=previous.removeprefix(result['module_prefix'])
                    rel=Path('agda/src')/Path(*previous.split('.')).with_suffix('.lagda.md')
                    relocated=True
            text=read(SNAP/rel)
            try: declaration_range(text,d['name'],d['qualified'])
            except ValueError:
                if mode!='updated manuscript with previously checked Agda snapshot' or d['name'] not in PREVIOUS_NAMES:
                    raise
                newname=PREVIOUS_NAMES[d['name']]
                qualified=d['qualified'].rsplit('.',1)[0]+'.'+newname if '.' in d['qualified'] else newname
                declaration_range(text,newname,qualified)
                d['name']=newname;d['qualified']=qualified;renamed=True
        if renamed:
            p['note']=(p.get('note','')+' The displayed checked edition uses the previous spelling of these declarations; the source notation review is pending its final Agda check.').strip()
        if relocated:
            p['note']=(p.get('note','')+' The canonical source has moved to the current book section; this panel retains the module name and declaration order of the earlier checked edition.').strip()
    return result
