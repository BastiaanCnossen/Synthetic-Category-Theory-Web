"""Prepare, then export a committed chapter in isolation under the shared lock.

Preparation does not invoke Agda. Run --export only after the compiler owner
releases a slot. The output is a compiler bundle, not an installed website.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time
from chapter_publication import source_inventory

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


def committed_sources(repo, commit, development='production'):
    args = ['git', '-c', 'safe.directory='+repo.as_posix(), '-C', str(repo)]
    commit = subprocess.check_output(args+['rev-parse', '--verify', commit+'^{commit}'], text=True).strip()
    prefix = '' if development == 'production' else 'rebuild2/'
    archive = subprocess.check_output(args+['archive', '--format=tar', commit, prefix+'src'])
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        files = {p.name.removeprefix(prefix): bundle.extractfile(p).read() for p in bundle if p.isfile()
                 and (p.name.endswith('.agda') or p.name.endswith('.lagda.md'))}
    return commit, files


def prepare(repo, commit, selection, work, development='production', source_root=None):
    if work.exists():
        raise ValueError('Export directory already exists; preserve it and choose a new directory')
    if development not in ('production', 'rebuild2'):
        raise ValueError('Unknown source development')
    commit, committed = committed_sources(repo, commit, development)
    selected = selection['selected_modules']
    source_root = source_root or repo/('src' if development == 'production' else 'rebuild2/src')
    current = source_inventory(source_root)
    prepared = {}
    for name in selected:
        data = current[name]
        relative = 'src/'+data['source']
        raw = (source_root/data['source']).read_bytes()
        original = committed.get(relative)
        if original is None or raw.replace(b'\r\n', b'\n') != original.replace(b'\r\n', b'\n'):
            raise ValueError('Working source differs from commit: '+name)
        if sha(original) != selection['source_hashes'][name]:
            raise ValueError('Selection differs from committed source: '+name)
        if not data['imports'] <= set(selected):
            raise ValueError('Selection lacks prerequisites: '+name)
        prepared[name] = (relative, raw, original)
    work.mkdir(parents=True)
    record = {'commit': commit, 'development': development,
              'repository_source_root': 'src' if development == 'production' else 'rebuild2/src',
              'chapter': selection['chapter'], 'sources': {},
              'excluded_modules': selection['excluded_modules'],
              'note': 'Committed source text; checked checkout line endings retained for interface reuse.'}
    if development == 'rebuild2':
        axiom_path = 'rebuild2/AXIOMS.md'
        axioms = subprocess.check_output(['git','-c','safe.directory='+repo.as_posix(),'-C',str(repo),'show',commit+':'+axiom_path])
        (work/'AXIOMS.md').write_bytes(axioms)
        record['assumption_inventory'] = {'repository_path':axiom_path,'path':'AXIOMS.md','sha256':sha(axioms)}
    for name, (relative, raw, original) in prepared.items():
        target = work/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        record['sources'][name] = {'path': relative, 'sha256': sha(raw), 'commit_sha256': sha(original)}
    library = 'name: sct-web-export\ninclude: src\n'
    (work/'sct-web-export.agda-lib').write_text(library, encoding='utf-8')
    record['library_sha256'] = sha((work/'sct-web-export.agda-lib').read_bytes())
    aggregate = f'SCT.WebChapter{selection["chapter"]:02d}'
    record['aggregate'] = aggregate
    path = work/'src'/Path(*aggregate.split('.')).with_suffix('.agda')
    flags = '--safe --without-K' if development == 'production' else '--without-K'
    path.write_text('{-# OPTIONS '+flags+' #-}\nmodule '+aggregate+' where\n'+
                    ''.join('import '+n+'\n' for n in sorted(selected)), encoding='utf-8')
    record['aggregate_sha256'] = sha(path.read_bytes())
    save(work/'prepared.json', record)
    return record


def seed_versioned_interfaces(repo, work, record, version, seeds):
    """Call only under the shared compiler lock; these remain cache hints."""
    release = re.match(r'\d+(?:\.\d+)+', version)
    if not release:
        raise ValueError('Unrecognized Agda version: '+version)
    copied = {}
    for name, source in record['sources'].items():
        relative = Path(*name.split('.')).with_suffix('.agdai')
        project = repo if record.get('development', 'production') == 'production' else repo/'rebuild2'
        candidate = project/'_build'/release.group()/'agda/src'/relative
        current = project/source['path']
        if (not candidate.is_file() or not current.is_file()
                or sha(current.read_bytes()) != source['sha256']):
            candidate = None
        # The current publication check refreshes canonical interfaces. Older
        # profile hints can match the module text but predate dependency changes.
        if candidate is None and name in seeds:
            cached, source_hash, interface_hash = seeds[name]
            if (source_hash == source['sha256'] and cached.is_file()
                    and sha(cached.read_bytes()) == interface_hash):
                candidate = cached
        if candidate is None or not candidate.is_file():
            continue
        destination = work/'_build'/release.group()/'agda/src'/relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(candidate, destination)
        copied[name] = {'sha256': sha(destination.read_bytes()), 'origin': str(candidate)}
    return copied


def reuse_export_interfaces(previous, work, record, compiler_hash, version):
    """Resume only cache hints from an identical export, including failed runs."""
    previous=Path(previous).resolve()
    receipt_path=previous/'receipt.json'
    receipt=json.loads(receipt_path.read_text(encoding='utf8'))
    for key in ('sources','aggregate','aggregate_sha256','library_sha256','development','commit','assumption_inventory'):
        if receipt.get(key)!=record.get(key): raise ValueError('Prior export differs: '+key)
    if receipt['compiler_sha256']!=compiler_hash or receipt['agda_version']!=version:
        raise ValueError('Prior export compiler differs')
    files=[(s['path'],s['sha256']) for s in record['sources'].values()]
    files += [('src/'+record['aggregate'].replace('.','/')+'.agda',record['aggregate_sha256']),
              ('sct-web-export.agda-lib',record['library_sha256'])]
    if record.get('assumption_inventory'):
        a=record['assumption_inventory']; files.append((a['path'],a['sha256']))
    for path,expected in files:
        if sha((previous/path).read_bytes())!=expected: raise ValueError('Prior export source changed: '+path)
    release=re.match(r'\d+(?:\.\d+)+',version).group()
    copied={}
    for name in record['sources']:
        relative=Path('_build')/release/'agda/src'/Path(*name.split('.')).with_suffix('.agdai')
        source=previous/relative
        if not source.is_file(): continue
        target=work/relative; target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(source,target)
        copied[name]={'sha256':sha(target.read_bytes()),'origin':str(source)}
    return {'receipt_sha256':sha(receipt_path.read_bytes()),'previous_status':receipt['status'],
            'interfaces':copied,'note':'Cache hints only; prior failed export is not verification evidence.'}


def export(repo, work, executable, timeout, max_heap='4G', reuse_export=None):
    sys.path.insert(0, str(repo/'scripts'))
    from agda_lock import held, DEFAULT_PATH
    record = json.loads((work/'prepared.json').read_text(encoding='utf-8'))
    def validate_sources():
        if record.get('assumption_inventory'):
            inventory=record['assumption_inventory']
            if sha((work/inventory['path']).read_bytes()) != inventory['sha256']:
                raise ValueError('Prepared assumption inventory changed')
        for name, source in record['sources'].items():
            if sha((work/source['path']).read_bytes()) != source['sha256']:
                raise ValueError('Prepared source changed: '+name)
        if sha((work/'src'/Path(*record['aggregate'].split('.')).with_suffix('.agda')).read_bytes()) != record['aggregate_sha256']:
            raise ValueError('Prepared aggregate changed')
        if sha((work/'sct-web-export.agda-lib').read_bytes()) != record['library_sha256']:
            raise ValueError('Prepared library root changed')
    validate_sources()
    html = work/'html'
    if html.exists():
        raise ValueError('HTML attempt already exists; preserve evidence and prepare a new export')
    html.mkdir()
    development = record.get('development', 'production')
    flags = ['--safe'] if development == 'production' else []
    command = [executable, '--transliterate', '--no-libraries', *flags, '--without-K', '-i', 'src',
               '--html', '--html-highlight=all', '--html-dir='+str(html),
               'src/'+record['aggregate'].replace('.', '/')+'.agda', '+RTS', '-M'+max_heap, '-RTS']
    receipt = {**record, 'command': command, 'checked': False, 'status': 'running',
               'max_heap': max_heap, 'timeout_seconds': timeout,
               'started_utc': datetime.now(timezone.utc).isoformat()}
    with held('web-chapter-html', record['aggregate'], wait=False,
              path=DEFAULT_PATH) as lock:
        from profile_agda import seed_interfaces
        executable_path = shutil.which(executable)
        if not executable_path:
            raise ValueError('Agda executable not found: '+executable)
        receipt['compiler_sha256'] = sha(Path(executable_path).read_bytes())
        receipt['agda_version'] = subprocess.check_output([executable, '--numeric-version'], text=True).strip()
        receipt['interface_layout'] = 'versioned'
        cache = 'cache' if development == 'production' else 'cache-rebuild2'
        seeds = seed_interfaces(repo/'_build/agda-profile'/cache, receipt['compiler_sha256'])
        receipt['seeded_interfaces'] = seed_versioned_interfaces(repo, work, record, receipt['agda_version'], seeds)
        if reuse_export:
            receipt['reused_export'] = reuse_export_interfaces(reuse_export,work,record,receipt['compiler_sha256'],receipt['agda_version'])
        receipt['agda'] = subprocess.check_output([executable, '--version'], text=True).strip()
        save(work/'receipt.json', receipt)
        start = time.monotonic()
        with (work/'compiler.log').open('w', encoding='utf-8') as log:
            child = subprocess.Popen(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
            lock.set_child(child.pid)
            try:
                child.wait(timeout=timeout)
                receipt['status'] = 'passed' if child.returncode == 0 else 'failed'
                receipt['exit_code'] = child.returncode
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
                receipt['status'] = 'timeout'
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait()
                lock.set_child(None)
                receipt['elapsed_seconds'] = time.monotonic()-start
                log.flush()
                contents = (work/'compiler.log').read_text(encoding='utf-8', errors='replace')
                receipt['checked_modules'] = re.findall(r'Checking (SCT\.[\w.]+)', contents)
                receipt['finished_utc'] = datetime.now(timezone.utc).isoformat()
                save(work/'receipt.json', receipt)
        validate_sources()
        if receipt['status'] == 'passed':
            expected = set(record['sources']) | {record['aggregate']}
            actual = {p.stem for p in html.glob('SCT.*.html')}
            if actual != expected:
                raise ValueError('Compiler HTML inventory differs from selection')
            from common import parse
            for name, source in record['sources'].items():
                pre = next(parse((html/(name+'.html')).read_text(encoding='utf-8')).all('pre'))
                if pre.text() != (work/source['path']).read_text(encoding='utf-8'):
                    raise ValueError('Compiler HTML source mismatch: '+name)
            receipt['html_sha256'] = {p.name: sha(p.read_bytes()) for p in html.iterdir() if p.is_file()}
            receipt['checked'] = True
            save(work/'receipt.json', receipt)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--agda-repo', type=Path, default=ROOT.parent/'Agda')
    parser.add_argument('--commit')
    parser.add_argument('--development', choices=['production','rebuild2'], default='production')
    parser.add_argument('--source-root', type=Path, help='Exact committed extraction, independently checked against Git blobs.')
    parser.add_argument('--selection', type=Path)
    parser.add_argument('--work', required=True, type=Path)
    parser.add_argument('--export', action='store_true')
    parser.add_argument('--agda', default='agda')
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--max-heap', default='4G')
    parser.add_argument('--reuse-export', type=Path, help='Previous identical export, used only as compiler cache hints.')
    args = parser.parse_args()
    work = args.work.resolve()
    if (ROOT/'_build').resolve() not in work.parents or work.is_symlink():
        parser.error('Work directory must be a new directory within Web/_build')
    if args.export:
        result = export(args.agda_repo.resolve(), work, args.agda, args.timeout, args.max_heap, args.reuse_export)
        print(json.dumps({'status': result['status'], 'checked': result['checked']}))
        return 0 if result['checked'] else 1
    if not args.commit or not args.selection:
        parser.error('Preparation requires --commit and --selection')
    result = prepare(args.agda_repo.resolve(), args.commit,
                     json.loads(args.selection.read_text(encoding='utf-8')), work,
                     args.development, args.source_root)
    print(json.dumps({'prepared_sources': len(result['sources']), 'commit': result['commit'], 'agda_invoked': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
