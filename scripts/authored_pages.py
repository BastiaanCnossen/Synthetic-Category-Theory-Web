"""Protect the directly edited pages when regenerating the rest of the site."""
from pathlib import Path
import shutil

AUTHORED_PAGES = ('index.html', 'formalization.html', 'build-report.html')


def require_authored_pages(site):
    site = Path(site)
    missing = [name for name in AUTHORED_PAGES if not (site / name).is_file()]
    if missing:
        raise ValueError('Restore the editable pages before building: ' + ', '.join(missing))


def clear_generated_pages(site, repository):
    site = Path(site).resolve()
    if site.parent != Path(repository).resolve() or site.name != '_site':
        raise ValueError('Unsafe distribution directory')
    require_authored_pages(site)
    children = list(site.iterdir())
    # Check every target before removing anything. The authored files stay on
    # disk throughout the build, including when a compiler or converter fails.
    for child in children:
        if child.is_symlink() or child.resolve().parent != site:
            raise ValueError('Unexpected linked distribution entry: ' + str(child))
    for child in children:
        if child.name in AUTHORED_PAGES:
            continue
        if child.is_dir():
            shutil.rmtree(child)
        else:
            child.unlink()
