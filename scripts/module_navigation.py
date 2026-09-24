"""One chapter/section hierarchy for the index and the side reader."""
import re
from module_layout import canonical_module

CHAPTER_TITLES = {('I', 1): 'The language of synthetic category theory',
                  ('I', 2): 'The internal structure of categories'}
SECTION_TITLES = {('I', 1, 1): 'The basic vocabulary',
                  ('I', 1, 2): 'Coherences',
                  ('I', 1, 3): 'Equivalences of categories',
                  ('I', 1, 4): 'Mapping animae',
                  ('I', 1, 5): 'Initial categories and coproducts',
                  ('I', 1, 6): 'Pullbacks of categories',
                  ('I', 1, 7): 'Functor categories',
                  ('I', 1, 8): 'Pushout squares',
                  ('I', 2, 1): 'Morphisms and diagrams',
                  ('I', 2, 2): 'The Segal axiom',
                  ('I', 2, 3): 'The Rezk axiom',
                  ('I', 2, 4): 'Groupoids',
                  ('I', 2, 5): 'Recognizing animae',
                  ('I', 2, 6): 'Exercises'}
BOOK_MODULE = re.compile(r'^SCT\.Volume([IVXLCDM]+)\.Chapter(\d+)(?:\.Section(\d+))?\.(.+)$')


def module_label(module):
    match = BOOK_MODULE.match(module)
    return match[4] if match else module.removeprefix('SCT.')


def natural_key(value):
    return [int(part) if part.isdigit() else part for part in re.split(r'(\d+)', value)]


def module_tree(modules, *, retained=False):
    names = sorted(set(modules), key=natural_key)
    volumes = {match[1] for name in names if (match := BOOK_MODULE.match(name))}
    root = {'key': '', 'label': '', 'modules': [], 'children': []}

    def child(parent, key, label):
        found = next((node for node in parent['children'] if node['key'] == key), None)
        if found is None:
            found = {'key': key, 'label': label, 'modules': [], 'children': []}
            parent['children'].append(found)
        return found

    for name in names:
        match = BOOK_MODULE.match(canonical_module(name) if retained else name)
        parent = root
        if match:
            volume, chapter, section = match[1], int(match[2]), int(match[3]) if match[3] else None
            if len(volumes) > 1:
                parent = child(parent, 'SCT.Volume'+volume, 'Volume '+volume)
            chapter_key = f'SCT.Volume{volume}.Chapter{chapter:02d}'
            title = CHAPTER_TITLES.get((volume, chapter))
            parent = child(parent, chapter_key, f'Chapter {chapter}' + (': '+title if title else ''))
            if section is not None:
                title = SECTION_TITLES.get((volume, chapter, section))
                parent = child(parent, f'{chapter_key}.Section{section:02d}',
                               f'{chapter}.{section}' + (' '+title if title else ''))
        parent['modules'].append(name)
    def sort_groups(node):
        node['children'].sort(key=lambda child:natural_key(child['key']))
        for child_node in node['children']: sort_groups(child_node)
    sort_groups(root)
    return root
