'use strict';
const proofs = document.querySelector('#collapse-proofs');
const hideAgdaLinks=document.querySelector('#hide-agda-links');
if (window.matchMedia('(max-width: 850px)').matches) {
  const contents = document.querySelector('.reader-nav > details');
  if (contents) contents.open = false;
}
if (proofs) proofs.addEventListener('change', () => {
  document.querySelectorAll('.book-proof').forEach(panel => { panel.open = !proofs.checked; });
});
const data = window.SCT_AGDA;
let rail, activeTrigger, activeId, lastModule, moduleGroups;
let definitionHistory=[];
const exploredDefinitions=new Map();
const roles = {assumption:'Assumption, type checked', definition:'Definition, checked', derived:'Derivation, checked'};
if (data && document.querySelector('.agda-trigger')) {
  document.body.classList.add('side-reader-ready');
  rail = document.createElement('aside');
  rail.id = 'agda-reader'; rail.className = 'agda-reader'; rail.hidden = true;
  rail.setAttribute('aria-label', 'Agda code reader');
  rail.innerHTML = `<header class="agda-reader-header"><div><span class="eyebrow">Agda</span><h2 id="agda-reader-title"></h2></div><button class="reader-close" type="button" aria-label="Close Agda panel" title="Close (Escape)">×</button></header>
    <div class="reader-toolbar"><button class="reader-back" type="button" disabled>Back in code</button><span class="reader-role"></span><button type="button" class="reader-copy">Copy selection</button><a class="reader-module-link">Full module ↗</a></div>
    <details class="module-browser"><summary class="module-picker" aria-label="Choose Agda module">Choose module</summary><div class="module-menu"><div class="module-tree"></div></div></details>
    <div class="reader-location"></div><pre class="Agda reader-code" tabindex="0" aria-label="Agda source; relevant lines highlighted"></pre>
    <div class="reader-backlink"><span class="reader-message" role="status">Click a code line to find its book passage.</span><select class="book-picker" aria-label="Corresponding book passage" hidden></select><textarea class="reader-copy-fallback" aria-label="Selected Agda lines to copy" readonly hidden></textarea></div>
    <footer class="reader-bottom"><details><summary>Correspondence</summary><p class="reader-note"></p><p class="reader-check-note"></p></details></footer>`;
  document.body.append(rail);
  rail.querySelector('.reader-close').addEventListener('click', () => closeReader(true));
  rail.querySelector('.reader-back').addEventListener('click',()=> {
    const previous=definitionHistory.pop(); if (!previous) return;
    renderModule(previous.module,previous.definition);
    highlightLines(previous.focus);
    const code=rail.querySelector('.reader-code'); code.scrollTop=previous.top; code.scrollLeft=previous.left;
    rail.querySelector('.reader-back').disabled=!definitionHistory.length;
  });
  rail.querySelector('.module-tree').addEventListener('click', event => {
    const choice=event.target.closest('button[data-module]'); if (!choice) return;
    rememberCodeView();
    renderModule(choice.dataset.module);
    rail.querySelector('.reader-back').disabled=false;
    rail.querySelector('.module-browser').open=false;
    rail.querySelector('.module-picker').focus({preventScroll:true});
  });
  document.addEventListener('click', event => {
    if (!event.target.closest('.module-browser')) rail.querySelector('.module-browser').open=false;
  });
  rail.querySelector('.book-picker').addEventListener('change', event => {
    const code=rail.querySelector('.reader-code');
    navigateFromCode(lastModule,Number(event.target.dataset.line),event.target.value,code.scrollTop);
  });
  rail.querySelector('.reader-code').addEventListener('click',event=> {
    if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const symbol=event.target.closest('a[href]');
    if (symbol) {
      if (jumpToDefinition(symbol)) {
        event.preventDefault();
        if (event.detail===0) rail.querySelector('.reader-code').focus({preventScroll:true});
      }
      return;
    }
    const line=event.target.closest('.code-line'); if (!line) return;
    event.preventDefault();
    const number=Number(line.dataset.line), choices=reverseChoices(lastModule,number);
    if (choices.length) navigateFromCode(lastModule,number,choices[0].id,rail.querySelector('.reader-code').scrollTop);
    else {
      highlightLines([number]);
      rail.querySelector('.reader-message').textContent='No book passage assigned to this line.';
      rail.querySelector('.book-picker').hidden=true;
    }
  });
  rail.querySelector('.reader-copy').addEventListener('click', async event => {
    const text=[...rail.querySelectorAll('.code-line.is-relevant .line-text')].map(n=>n.textContent).join('\n');
    try { await navigator.clipboard.writeText(text); event.target.textContent='Copied'; }
    catch {
      const fallback=rail.querySelector('.reader-copy-fallback');
      fallback.value=text; fallback.hidden=false; fallback.focus({preventScroll:true}); fallback.select();
      event.target.textContent='Selected: Ctrl+C';
    }
    setTimeout(()=> { event.target.textContent='Copy selection'; },2000);
  });
  document.addEventListener('keydown',event=> {
    if (event.key==='Escape' && !rail.hidden) {
      event.preventDefault();
      const browser=rail.querySelector('.module-browser');
      if (browser.open) { browser.open=false; rail.querySelector('.module-picker').focus({preventScroll:true}); }
      else closeReader(true);
    }
  });
  document.querySelectorAll('.agda-trigger').forEach(trigger => {
    trigger.setAttribute('aria-controls','agda-reader'); trigger.setAttribute('aria-expanded','false');
    // Handle the link before MathJax's nested math explorer consumes clicks.
    trigger.addEventListener('click',event=> {
      if (hideAgdaLinks?.checked) { event.preventDefault(); return; }
      if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
      event.preventDefault();
      openReader(trigger.dataset.agda);
      history.pushState(null,'','#agda-'+trigger.dataset.agda);
      if (event.detail===0) rail.querySelector('.module-picker').focus({preventScroll:true});
    }, {capture:true});
  });
  document.querySelector('#open-code-browser')?.addEventListener('click',()=> {
    const first=document.querySelector('.agda-trigger');
    openReader(activeId || first.dataset.agda);
    rail.querySelector('.module-picker').focus({preventScroll:true});
  });
}
if (hideAgdaLinks) {
  const originalLinks=new Map([...document.querySelectorAll('.agda-trigger')].map(link=>[link,{href:link.getAttribute('href'),title:link.getAttribute('title')} ]));
  try { hideAgdaLinks.checked=localStorage.getItem('sct.hideAgdaLinks')==='true'; } catch {}
  const applyPreference=()=> {
    document.body.classList.toggle('hide-agda-links',hideAgdaLinks.checked);
    originalLinks.forEach((attributes,link)=> {
      if (hideAgdaLinks.checked) {
        link.removeAttribute('href'); link.removeAttribute('title'); link.setAttribute('tabindex','-1');
        link.removeAttribute('aria-controls'); link.removeAttribute('aria-expanded');
      } else {
        link.setAttribute('href',attributes.href); if (attributes.title) link.setAttribute('title',attributes.title);
        link.removeAttribute('tabindex'); link.setAttribute('aria-controls','agda-reader');
        link.setAttribute('aria-expanded',String(!rail?.hidden && link===activeTrigger));
      }
    });
  };
  hideAgdaLinks.addEventListener('change',()=> {
    applyPreference();
    try { localStorage.setItem('sct.hideAgdaLinks',String(hideAgdaLinks.checked)); } catch {}
  });
  applyPreference();
}
function visibleProseTarget(target) {
  if (!target || !hideAgdaLinks?.checked || !target.matches('.agda-point')) return target;
  const block=target.closest('p,li,dd,div') || target.parentElement;
  return block.getBoundingClientRect().height>1 ? block : block.previousElementSibling || block.nextElementSibling || block;
}
function preservePassage(action) {
  const before=visibleProseTarget(activeTrigger)?.getBoundingClientRect().top;
  action();
  if (before!==undefined) {
    const change=visibleProseTarget(activeTrigger).getBoundingClientRect().top-before;
    if (Math.abs(change)>.5) window.scrollBy({top:change,behavior:'instant'});
  }
}
function openReader(id) {
  const passage=data?.passages[id]; if (!passage || !rail) return;
  definitionHistory=[]; exploredDefinitions.clear();
  rail.querySelector('.reader-back').disabled=true;
  if (activeTrigger) { activeTrigger.classList.remove('is-active'); if (!hideAgdaLinks?.checked && activeTrigger.matches('.agda-trigger')) activeTrigger.setAttribute('aria-expanded','false'); }
  activeId=id; activeTrigger=document.getElementById('text-'+id);
  activeTrigger?.classList.add('is-active'); if (!hideAgdaLinks?.checked && activeTrigger?.matches('.agda-trigger')) activeTrigger.setAttribute('aria-expanded','true');
  preservePassage(()=> { rail.hidden=false; document.body.classList.add('agda-reader-open'); });
  rail.querySelector('h2').textContent=passage.title;
  rail.querySelector('.reader-note').textContent=passage.note || 'This passage is linked to the displayed declaration.';
  moduleGroups=new Map();
  passage.declarations.forEach(d=> { if (!moduleGroups.has(d.module)) moduleGroups.set(d.module,[]); moduleGroups.get(d.module).push(d); });
  buildModuleBrowser();
  rail.querySelector('.reader-message').textContent='Click a symbol for its definition; click a line number for its book passage.';
  rail.querySelector('.book-picker').hidden=true;
  rail.querySelector('.reader-copy-fallback').hidden=true;
  renderModule(moduleGroups.keys().next().value);
  if (window.matchMedia('(max-width: 1000px)').matches && activeTrigger) {
    const ceiling=Math.max(24,rail.getBoundingClientRect().top-160);
    const top=visibleProseTarget(activeTrigger).getBoundingClientRect().top;
    if (top>ceiling) window.scrollBy({top:top-ceiling,behavior:'instant'});
  }
}
let currentDefinition;
function buildModuleBrowser() {
  const tree=rail.querySelector('.module-tree'); tree.replaceChildren();
  function append(node,parent) {
    node.modules.forEach(module=> {
      const button=document.createElement('button'); button.type='button';
      button.className='module-choice'; button.dataset.module=module;
      button.textContent=data.modules[module].label; button.title=module;
      if (moduleGroups.has(module)) {
        const hint=document.createElement('span'); hint.className='module-related';
        hint.textContent='Related to passage'; button.append(hint);
      }
      parent.append(button);
    });
    node.children.forEach(child=> {
      const group=document.createElement('details'); group.className='module-group';
      const summary=document.createElement('summary'); summary.textContent=child.label;
      const contents=document.createElement('div'); contents.className='module-group-content';
      group.append(summary,contents); parent.append(group); append(child,contents);
    });
  }
  append(data.module_tree,tree);
  rail.querySelector('.module-menu').scrollTop=0;
}
function selectModuleInBrowser(module) {
  const picker=rail.querySelector('.module-picker');
  picker.textContent='Module: '+module.replace('SCT.VolumeI.Chapter01.','');
  picker.title=module;
  rail.querySelectorAll('.module-choice').forEach(button=> {
    const selected=button.dataset.module===module;
    button.setAttribute('aria-pressed',String(selected));
    if (selected) {
      for (let node=button.parentElement;node && !node.classList.contains('module-browser');node=node.parentElement) {
        if (node.tagName==='DETAILS') node.open=true;
      }
    }
  });
}
function renderModule(module,definition) {
  definition=definition || (!moduleGroups.has(module) ? exploredDefinitions.get(module) : undefined);
  if (!definition && !moduleGroups.has(module)) definition={moduleOnly:true,href:data.modules[module].href,label:module.replace('SCT.VolumeI.Chapter01.','')};
  currentDefinition=definition;
  const declarations=moduleGroups.get(module) || [];
  rail.querySelector('.book-picker').hidden=true;
  rail.querySelector('.book-picker').replaceChildren();
  rail.querySelector('.reader-message').textContent='Click a symbol for its definition; click a line number for its book passage.';
  rail.querySelector('.reader-copy-fallback').hidden=true;
  const code=rail.querySelector('.reader-code');
  selectModuleInBrowser(module);
  rail.querySelector('h2').textContent=definition ? (definition.moduleOnly ? '' : 'Definition: ')+definition.label : data.passages[activeId].title;
  const statusDeclarations=definition ? (definition.moduleOnly ? [] : Object.values(data.passages).flatMap(p=>p.declarations).filter(d=>d.module===module && d.name===definition.label && d.range.includes(definition.line))) : declarations;
  rail.querySelector('.reader-role').textContent=!data.modules[module].checked ? 'Source only, outside this check' : statusDeclarations.length ? [...new Set(statusDeclarations.map(d=>roles[d.role]))].join(' · ') : 'Checked source';
  rail.querySelector('.reader-check-note').textContent=data.modules[module].checked ? data.scope_note || 'Checked against the supplied interface. Contextual validity is explained in the Agda guide.' : 'This module was not included in the web edition aggregate check. Compiled definition links are unavailable.';
  rail.querySelector('.reader-note').textContent=definition ? 'Browsing '+module+'.' : data.passages[activeId].note;
  const link=rail.querySelector('.reader-module-link'); link.href=definition ? definition.href : declarations[0].href;
  rail.querySelector('.reader-location').textContent=definition ? module.replace('SCT.VolumeI.Chapter01.','')+(definition.moduleOnly ? '' : ' · line '+definition.line) : declarations.map(d=>d.qualified).join(' · ');
  rail.querySelector('.reader-location').title=module;
  if (lastModule!==module) {
    // Locally generated, validated compiler HTML only. No reader-supplied markup.
    code.innerHTML=data.modules[module].lines.map(line=>`<span class="code-line" data-line="${line.number}">${line.targets.length ? `<button type="button" class="line-number" aria-label="Find line ${line.number} in the book">${line.number}</button>` : `<span class="line-number" aria-hidden="true">${line.number}</span>`}<span class="line-text">${line.html}</span></span>`).join('');
    lastModule=module;
  }
  highlightLines(definition ? (definition.moduleOnly ? [] : [definition.line]) : declarations.flatMap(d=>d.focus));
  const first=code.querySelector('.is-relevant');
  if (first) {
    // Scroll only the code surface; the manuscript's scroll position stays put.
    const offset=first.getBoundingClientRect().top-code.getBoundingClientRect().top+code.scrollTop;
    code.scrollTop=Math.max(0,offset-Math.min(120,code.clientHeight*.25));
    code.scrollLeft=0;
  } else { code.scrollTop=0; code.scrollLeft=0; }
}
function rememberCodeView() {
  const code=rail.querySelector('.reader-code');
  definitionHistory.push({module:lastModule,definition:currentDefinition,
    focus:[...code.querySelectorAll('.is-relevant')].map(n=>Number(n.dataset.line)),top:code.scrollTop,left:code.scrollLeft});
}
function jumpToDefinition(symbol) {
  const url=new URL(symbol.getAttribute('href'),location.href);
  if (url.origin!==location.origin) return false;
  const module=decodeURIComponent(url.pathname.split('/').pop()).replace(/\.html$/,'');
  const payload=data.modules[module]; if (!payload) return false;
  const anchor=decodeURIComponent(url.hash.slice(1));
  const line=anchor ? payload.anchors[anchor] : payload.lines[0]?.number;
  if (!line) return false;
  rememberCodeView();
  const definition={line,href:symbol.getAttribute('href'),label:symbol.textContent};
  exploredDefinitions.set(module,definition);
  renderModule(module,definition);
  rail.querySelector('.reader-back').disabled=false;
  return true;
}
function highlightLines(lines) {
  const relevant=new Set(lines);
  rail.querySelectorAll('.code-line').forEach(line=>line.classList.toggle('is-relevant',relevant.has(Number(line.dataset.line))));
  rail.querySelector('.reader-copy').disabled=!rail.querySelector('.code-line.is-relevant');
}
function reverseChoices(module,number) {
  const line=data.modules[module].lines.find(line=>line.number===number);
  const ids=Object.keys(data.passages), active=ids.indexOf(activeId);
  const local=location.pathname.split('/').pop().replace('.html','');
  return [...line.targets].sort((a,b)=>a.rank[0]-b.rank[0] || a.rank[1]-b.rank[1] ||
    Number(data.passages[b.id].page===local)-Number(data.passages[a.id].page===local) ||
    Math.abs(ids.indexOf(a.id)-active)-Math.abs(ids.indexOf(b.id)-active) || ids.indexOf(a.id)-ids.indexOf(b.id));
}
function navigateFromCode(module,number,id,scrollTop,push=true) {
  const passage=data.passages[id];
  const fragment='code:'+module+':'+number+':'+id;
  if (!document.getElementById('text-'+id)) { location.href=passage.page+'.html#'+fragment; return; }
  const target=document.getElementById('text-'+id);
  for (let node=target;node;node=node.parentElement) if (node.tagName==='DETAILS') node.open=true;
  openReader(id); renderModule(module); highlightLines([number]);
  const code=rail.querySelector('.reader-code');
  if (scrollTop!==undefined) code.scrollTop=scrollTop;
  else { const line=code.querySelector(`[data-line="${number}"]`); code.scrollTop+=line.getBoundingClientRect().top-code.getBoundingClientRect().top-100; }
  visibleProseTarget(target).scrollIntoView({block:'center',behavior:'instant'});
  if (window.matchMedia('(max-width: 1000px)').matches) {
    const excess=visibleProseTarget(target).getBoundingClientRect().bottom-rail.getBoundingClientRect().top+40;
    if (excess>0) window.scrollBy({top:excess,behavior:'instant'});
  }
  const choices=reverseChoices(module,number), picker=rail.querySelector('.book-picker'); picker.replaceChildren();
  choices.forEach(choice=> { const option=document.createElement('option'); option.value=choice.id; option.textContent=data.passages[choice.id].title; picker.append(option); });
  picker.value=id; picker.dataset.line=number; picker.hidden=choices.length<2;
  rail.querySelector('.reader-message').textContent='Book: '+passage.title+(passage.reverse_only?' (explanatory passage)':'');
  if (push) history.pushState(null,'','#'+fragment);
}
function closeReader(restoreFocus) {
  if (!rail || rail.hidden) return;
  preservePassage(()=> { rail.hidden=true; document.body.classList.remove('agda-reader-open'); });
  activeTrigger?.classList.remove('is-active'); if (!hideAgdaLinks?.checked && activeTrigger?.matches('.agda-trigger')) activeTrigger.setAttribute('aria-expanded','false');
  if (restoreFocus) {
    const opener=hideAgdaLinks?.checked ? document.querySelector('#open-code-browser') : activeTrigger;
    const settings=opener?.closest('details'); if (settings) settings.open=true;
    opener?.focus({preventScroll:true});
    if (location.hash.startsWith('#agda-') || location.hash.startsWith('#code:')) history.replaceState(null,'','#text-'+activeId);
  }
}
function revealHash() {
  let id; try { id=decodeURIComponent(location.hash.slice(1)); } catch { return; }
  // Stable passage IDs survive manuscript moves, including old saved code links.
  const passageId=id.startsWith('code:') ? id.split(':')[3] :
    id.startsWith('agda-') || id.startsWith('text-') ? id.slice(5) : null;
  const destination=data?.passages[passageId]?.page;
  if (destination && location.pathname.split('/').pop()!==destination+'.html') {
    location.replace(destination+'.html'+location.hash); return;
  }
  if (rail && id.startsWith('code:')) {
    const [,module,line,pid]=id.split(':');
    if (data.modules[module]?.lines.some(x=>x.number===Number(line) && x.targets.some(t=>t.id===pid))) {
      navigateFromCode(module,Number(line),pid,undefined,false); return;
    }
  }
  if (rail && id.startsWith('agda-') && data.passages[id.slice(5)]) {
    const trigger=document.getElementById('text-'+id.slice(5));
    for (let node=trigger;node;node=node.parentElement) if (node.tagName==='DETAILS') node.open=true;
    visibleProseTarget(trigger)?.scrollIntoView({block:'center'}); openReader(id.slice(5)); return;
  }
  closeReader(false);
  const target=document.getElementById(id); if (!target) return;
  for (let node=target;node;node=node.parentElement) if (node.tagName==='DETAILS') node.open=true;
  visibleProseTarget(target).scrollIntoView({block:'start'});
}
window.addEventListener('hashchange',revealHash);
window.addEventListener('popstate',revealHash);
window.addEventListener('load',()=> (window.MathJax?.startup?.promise || Promise.resolve()).then(revealHash));
const codeSearch=document.querySelector('#code-search');
let searchDisclosureState;
if (codeSearch) codeSearch.addEventListener('input',()=> {
  const query=codeSearch.value.trim().toLocaleLowerCase(); let count=0;
  if (query && !searchDisclosureState) searchDisclosureState=new Map([...document.querySelectorAll('.module-group, .symbol-index')].map(group=>[group,group.open]));
  document.querySelectorAll('.code-index-entry, .symbol-entry').forEach(entry=> {
    let context=entry.textContent;
    for (let node=entry.parentElement;node;node=node.parentElement) if (node.dataset.label) context+=' '+node.dataset.label;
    entry.hidden=!context.toLocaleLowerCase().includes(query); if (!entry.hidden) count++;
  });
  document.querySelectorAll('.module-group').forEach(group=> {
    group.hidden=!!query && ![...group.querySelectorAll('.code-index-entry')].some(entry=>!entry.hidden);
    if (query && !group.hidden) group.open=true;
  });
  document.querySelector('#search-count').textContent=query ? `${count} matching modules or declarations` : '';
  if (query) document.querySelector('.symbol-index').open=true;
  else if (searchDisclosureState) { searchDisclosureState.forEach((open,group)=> { group.open=open; }); searchDisclosureState=undefined; }
});
