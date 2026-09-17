"""Install a validated generation while retaining the live preview and authored pages."""
from pathlib import Path
import os, shutil, tempfile
from authored_pages import AUTHORED_PAGES, require_authored_pages


def publish_generated_pages(stage, site, repository):
    repository=Path(repository).resolve()
    stage=Path(stage).resolve(); site=Path(site).resolve()
    if site != repository/'_site' or stage.parent != repository/'_build':
        raise ValueError('Unsafe publication directory')
    require_authored_pages(site)
    require_authored_pages(stage)
    # Check all paths before any write or removal, including linked parents.
    for root in (stage,site):
        for item in root.rglob('*'):
            if item.is_symlink() or root not in item.resolve().parents:
                raise ValueError('Linked publication path: '+str(item))
    files={p.relative_to(stage):p for p in stage.rglob('*') if p.is_file()}
    for relative,source in files.items():
        if relative.as_posix() in AUTHORED_PAGES: continue
        target=site/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.is_file() and target.read_bytes()==source.read_bytes(): continue
        # A request sees either the old complete file or the new complete file.
        handle,name=tempfile.mkstemp(prefix='.sct-publish-',dir=target.parent)
        os.close(handle)
        temporary=Path(name)
        try:
            shutil.copyfile(source,temporary)
            os.replace(temporary,target)
        finally:
            temporary.unlink(missing_ok=True)
    for old in site.rglob('*'):
        if old.is_file() and old.relative_to(site).as_posix() not in AUTHORED_PAGES and old.relative_to(site) not in files:
            old.unlink()
