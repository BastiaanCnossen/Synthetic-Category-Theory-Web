"""Verify that private annotation commits preserve the selected authorial baseline."""
from common import *
from pilot_model import tex_markers
import subprocess


def git(*args, check=True):
    return subprocess.run(['git',*args],cwd=REPO,encoding='utf-8',stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=check)


def check_annotations():
    metadata=json.loads(read(REPO/'.web-annotations.json'))
    if metadata.get('schema')!=1 or metadata.get('chapter')!=CHAPTER or metadata.get('marker_prefix')!='%!%':
        raise ValueError('Invalid annotation baseline metadata')
    base=metadata['base_commit']
    if not re.fullmatch(r'[0-9a-f]{40}',base): raise ValueError('Annotation baseline must be a full commit hash')
    if git('merge-base','--is-ancestor',base,'HEAD',check=False).returncode:
        raise ValueError('Annotation baseline is not an ancestor of this checkout')
    baseline=git('show',base+':'+CHAPTER).stdout
    manifest=json.loads(read(ROOT/'correspondence.json'))
    annotated=read(REPO/CHAPTER)
    if tex_markers(annotated,registry=manifest)[0]!=baseline:
        raise ValueError('Annotated chapter differs from its baseline after removing publication comments')
    main=git('rev-parse','main',check=False)
    on_main=main.returncode==0 and git('merge-base','--is-ancestor',base,main.stdout.strip(),check=False).returncode==0
    report={'status':'passed','base_commit':base,'chapter_sha256':digest(baseline),
            'annotation_only':True,'baseline_on_main':on_main,
            'baseline_kind':'main history' if on_main else 'separate authorial draft'}
    dump(BUILD/'annotation-verification.json',report)
    return report


if __name__=='__main__': print(json.dumps(check_annotations()))
