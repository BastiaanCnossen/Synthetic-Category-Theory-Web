"""Validate local annotated TeX and report its relation to the main manuscript.

The historical filename is retained for existing build entry points. Annotated
files are ordinary local files, not a Git branch or a commit-bound overlay.
"""
from common import *
from pilot_model import tex_markers


def check_annotations():
    manifest = json.loads(read(ROOT / 'correspondence.json'))
    reports=[]; found_all=[]
    for chapter in BOOK_CHAPTERS:
        relative=chapter['source']; path=ANNOTATED/relative
        if not path.is_file():
            raise ValueError('Missing annotated chapter: ' + str(path))
        source=read(path)
        plain,_=tex_markers(source,registry=manifest)
        _,found=tex_markers(selected_source(source,relative),registry=manifest)
        expected={p['id'] for p in manifest['passages']+manifest.get('reverse_only',[])
                  if p.get('tex_file',CHAPTER)==relative}
        if set(found)!=expected:
            raise ValueError('Annotated TeX passages do not match correspondence.json: '+relative)
        original=read(REPO/relative)
        reports.append({'source':relative,'chapter_sha256':digest(plain),
                        'private_chapter_sha256':digest(original),
                        'matches_private_manuscript':plain==original,'passages':len(found)})
        found_all.extend(found)
    expected_all={p['id'] for p in manifest['passages']+manifest.get('reverse_only',[])}
    if set(found_all)!=expected_all or len(found_all)!=len(set(found_all)):
        raise ValueError('Annotated TeX passages do not match the selected chapters')
    report={'status':'passed','source_kind':'local annotated files',
            'chapters':reports,'passages':len(found_all),
            'matches_private_manuscript':all(r['matches_private_manuscript'] for r in reports),
            'note':'Passage markers validated. Differences from the private manuscript are reported, not merged or discarded.'}
    dump(BUILD / 'annotation-verification.json', report)
    return report


if __name__=='__main__': print(json.dumps(check_annotations()))
