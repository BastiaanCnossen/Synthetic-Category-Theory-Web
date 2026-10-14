'use strict';
(() => {
  const nav = document.querySelector('.standalone-module-nav');
  const data = window.SCT_MODULE_NAVIGATION;
  if (!nav || !data) return;
  const browser = nav.querySelector('.module-browser');
  const summary = browser.querySelector('.module-picker');
  const current = nav.dataset.currentModule;
  function append(node, parent) {
    for (const name of node.modules) {
      const link = document.createElement('a');
      link.className = 'module-choice';
      link.href = data.hrefs?.[name] || name + '.html';
      link.textContent = data.labels[name];
      link.title = name;
      if (name === current) link.setAttribute('aria-current', 'page');
      parent.append(link);
    }
    for (const child of node.children) {
      const group = document.createElement('details');
      group.className = 'module-group';
      group.dataset.moduleGroup = child.key;
      const heading = document.createElement('summary');
      heading.textContent = child.label;
      const content = document.createElement('div');
      content.className = 'module-group-content';
      group.append(heading, content);
      parent.append(group);
      append(child, content);
      if (content.querySelector('[aria-current="page"]')) group.open = true;
    }
  }
  append(data.tree, browser.querySelector('.module-tree'));
  browser.hidden = false;
  browser.addEventListener('toggle', () => {
    if (browser.open) browser.querySelector('[aria-current="page"]')?.scrollIntoView({block: 'nearest'});
  });
  document.addEventListener('click', event => {
    if (!browser.contains(event.target)) browser.open = false;
  });
  browser.addEventListener('keydown', event => {
    if (event.key === 'Escape' && browser.open) {
      event.preventDefault(); browser.open = false; summary.focus();
    }
  });
})();
