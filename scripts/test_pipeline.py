import unittest
from common import *
from assemble import code_range
from pilot_model import declaration_range,tex_markers
from reader_context import focused_lines,module_lines,compiler_anchors

class PipelineTests(unittest.TestCase):
    def test_contents_expands_only_current_chapter(self):
        from book_navigation import contents
        for page,expected in [('morphisms-and-diagrams','Chapter 2'),('coherences','Chapter 1'),('index',None)]:
            tree=parse(contents(page))
            groups=[n for n in tree.all('details') if 'open' in n.attrs]
            self.assertEqual([next(n.all('summary')).text().split('The')[0] for n in groups],[expected] if expected else [])
            self.assertEqual(len([a for a in tree.all('a') if a.attrs.get('aria-current')=='page']),1)

    def test_chapter_turns_skip_sections(self):
        from book_navigation import page_turns
        first=list(parse(page_turns('chapter-introduction')).all('a'))
        last=list(parse(page_turns('internal-structure-introduction')).all('a'))
        self.assertEqual([(a.attrs['rel'],a.attrs['href']) for a in first],[('prev','overview-of-the-axioms.html'),('next','internal-structure-introduction.html')])
        self.assertEqual([(a.attrs['rel'],a.attrs['href']) for a in last],[('prev','chapter-introduction.html')])
        section=list(parse(page_turns('coherences')).all('a'))
        self.assertEqual([a.attrs['href'] for a in section],['basic-vocabulary.html','equivalences.html'])
        self.assertEqual(page_turns('index'),'')

    def test_frontmatter_reading_order(self):
        from book_navigation import page_turns, contents
        self.assertEqual([a.attrs['href'] for a in parse(page_turns('introduction')).all('a')],
                         ['overview-of-the-axioms.html'])
        self.assertEqual([a.attrs['href'] for a in parse(page_turns('overview-of-the-axioms')).all('a')],
                         ['introduction.html','chapter-introduction.html'])
        current=[a for a in parse(contents('introduction')).all('a') if a.attrs.get('aria-current')]
        self.assertEqual([a.attrs['href'] for a in current],['introduction.html'])

    def test_external_chapter_numbers_follow_master_order(self):
        from unittest.mock import patch
        from tempfile import TemporaryDirectory
        from prepare import resolve_external_references
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            write(root/'intro.tex',r'\begin{document}\chapter*{Introduction}\end{document}')
            write(root/'8_later.tex',r'\begin{document}\chapter{First}\label[chapter]{chap:first}Private prose.\end{document}')
            write(root/'3_earlier.tex',r'\begin{document}\chapter{Second}\label[chapter]{chapter:Second chapter}Private prose.\end{document}')
            with patch('prepare.SNAP',root),patch('prepare.BUILD',root):
                body,records=resolve_external_references(r'\Cref{chapter:Second chapter}',
                    ['intro.tex','8_later.tex','3_earlier.tex'],r'\documentclass{book}\begin{document}')
            self.assertEqual(records[0]['reference_job'],'reference-chapter-2')
            self.assertIn(r'\EditionExternal{chapter:Second chapter}',body)
            self.assertEqual(external_anchor(records[0]['label']),'chapter:Second_chapter')
            job=read(root/'reference-chapter-2.tex')
            self.assertIn(r'\setcounter{chapter}{1}',job)
            self.assertNotIn('Private prose',job)

    def test_shared_agda_signature_keeps_individual_compiler_offsets(self):
        source='module M.Top where\nrecord Expression {C : CAT} : Set where\n  field\n    value : C\n\nf g : A\nf = x\ng = y\n\nh : Expression → (r : A) → A\nh e r = r\n'
        for name in ('f','g'):
            loc=declaration_range(source,name)
            self.assertEqual(source[loc['start']:loc['end']],'f g : A\nf = x\ng = y')
            self.assertEqual(source[loc['namepos']:loc['namepos']+len(name)],name)
        self.assertEqual(declaration_range(source,'Expression')['kind'],'record')
        with self.assertRaises(ValueError): declaration_range(source,'r')

    def test_tikz_row_spacing_does_not_open_a_math_passage(self):
        source='\\[\\begin{tikzcd} a & b \\\\[1.4em] c & d \\end{tikzcd}\\]\n%!% begin example\nText.\n%!% end example\n'
        plain,found=tex_markers(source,registry={'passages':[{'id':'example'}]})
        self.assertEqual(found,['example'])
        self.assertIn('Text.',plain)

    def test_partial_chapter_selection_stops_before_next_section(self):
        from unittest.mock import patch
        source=r'\begin{document}\chapter{Internal structure}\label[chapter]{chap:Groupoids}\section{Morphisms and diagrams}\label[section]{sec:Morphisms_and_Diagrams}Selected.\section{Segal axiom}\label[section]{sec:Segal_Axiom}Excluded.\end{document}'
        with patch('common.BOOK_CHAPTERS',[{'source':CHAPTER2,'sections':[
                ('morphisms-and-diagrams','Morphisms and diagrams','sec:Morphisms_and_Diagrams')]}]):
            selected=selected_source(source,CHAPTER2)
        self.assertIn('Selected.',selected)
        self.assertNotIn('Excluded.',selected)
        self.assertNotIn('Segal',selected)

    def test_complete_chapter_selection_labels_unlabelled_exercises_only_in_output(self):
        chapter=next(c for c in BOOK_CHAPTERS if c['source']==CHAPTER2)
        body=''.join(r'\section{'+title+'}'+(r'\label[section]{'+label+'}' if not label.startswith('web:') else '')+'Text.'
                     for _,title,label in chapter['sections'])
        source=r'\begin{document}'+body+r'\end{document}'
        selected=selected_source(source,CHAPTER2)
        self.assertIn(r'\section{Exercises}\label[section]{web:chapter02-exercises}Text.',selected)
        self.assertNotIn('web:chapter02-exercises',source)
        with self.assertRaises(ValueError):
            selected_source(source.replace('sec:Rezk_Axiom','wrong-label'),CHAPTER2)

    def test_numbered_diagram_uses_resolved_equation_counter(self):
        from assemble import insert_diagrams
        body=parse('<div data-diagram="square"></div>')
        insert_diagrams(body,[{'id':'square','equation_label':'eq:square'}],{'eq:square':'2.1.1'})
        self.assertEqual(next(body.all('figcaption')).text(),'(2.1.1)')

    def test_new_stage_reuses_checked_dvi_but_preamble_change_recompiles(self):
        import tempfile
        from unittest.mock import patch
        import build
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); calls=[]
            dump(root/'selection.json',{'diagrams':[{'id':'square'}]})
            write(root/'square.tex','Diagram input'); write(root/'preamble.tex','Macros')
            def run(args):
                calls.append(args[0])
                if args[0]=='latex': write(root/'square.dvi','Compiled DVI')
                if args[0]=='dvisvgm': write(next(a.split('=',1)[1] for a in args if a.startswith('--output=')),'SVG')
            with patch.multiple(build,BUILD=root,run=run):
                build.convert_diagrams(site=root/'first')
                self.assertEqual(calls,['latex','dvisvgm'])
                calls.clear(); build.convert_diagrams(site=root/'second')
                self.assertEqual(calls,['dvisvgm'])
                write(root/'preamble.tex','Changed macros')
                calls.clear(); build.convert_diagrams(site=root/'third')
                self.assertEqual(calls,['latex','dvisvgm'])

    def test_tex_log_font_bytes_do_not_hide_reference_errors(self):
        import tempfile
        from validate import validate_tex_log
        with tempfile.TemporaryDirectory() as temporary:
            log=Path(temporary)/'pilot.log'
            font_message=b'Overfull box: font glyph \xb9\n'
            log.write_bytes(font_message+b'Output written on pilot.pdf.\n')
            validate_tex_log(log)
            for warning in (b"LaTeX Warning: Reference `missing' undefined.",
                            b"LaTeX Warning: Citation `missing' undefined.",
                            b'LaTeX Warning: There were undefined references.'):
                log.write_bytes(font_message+warning+b'\n')
                with self.assertRaisesRegex(ValueError,'Unresolved LaTeX reference'):
                    validate_tex_log(log)

    def test_functor_section_reference_becomes_internal_when_selected(self):
        from prepare import chapter_external_references
        reference=r'See \Cref{sec:Functor_Categories}.'
        section=r'\section{Functor categories}\label[section]{sec:Functor_Categories}'
        body,records=chapter_external_references(reference,reference+section)
        self.assertIn(r'\EditionExternal{sec:Functor_Categories}',body)
        self.assertEqual([r['label'] for r in records],['sec:Functor_Categories'])
        body,records=chapter_external_references(reference+section,reference+section)
        self.assertEqual(body,reference+section)
        self.assertEqual(records,[])

    def test_later_functoriality_exercise_has_an_external_destination(self):
        from prepare import chapter_external_references
        reference=r'\begin{exercise}[\Cref{exercise:Functoriality_Postcomposition}]Task.\end{exercise}'
        for env in ('exercise','uexercise'):
            later=r'\begin{'+env+r'}\label[exercise]{exercise:Functoriality_Postcomposition}Laws.\end{'+env+'}'
            body,records=chapter_external_references(reference,reference+later)
            self.assertIn(r'\EditionExternal{exercise:Functoriality_Postcomposition}',body)
            self.assertEqual(records[0]['source'],later)
            body,records=chapter_external_references(reference+later,reference+later)
            self.assertEqual(body,reference+later)
            self.assertEqual(records,[])
        with self.assertRaisesRegex(ValueError,'Outside-selection exercise moved'):
            chapter_external_references(reference,reference)

    def test_local_annotations_override_only_copied_files(self):
        import tempfile
        from unittest.mock import patch
        import common
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); private=root/'private'; annotated=root/'Annotated tex-files'
            write(private/CHAPTER,'Main manuscript')
            write(annotated/CHAPTER,'Annotated manuscript')
            write(private/'preamble.tex','Shared macros')
            with patch.multiple(common,REPO=private,ANNOTATED=annotated):
                self.assertEqual(read(common.manuscript_input(CHAPTER)),'Annotated manuscript')
                self.assertEqual(read(common.manuscript_input('preamble.tex')),'Shared macros')
                with self.assertRaises(ValueError): common.manuscript_input('../outside.tex')

    def test_local_annotations_report_prose_differences_without_a_git_branch(self):
        import tempfile
        from unittest.mock import patch
        import check_preservation
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); private=root/'private'; annotated=root/'Annotated tex-files'
            write(private/CHAPTER,'Main prose.\n')
            write(annotated/CHAPTER,'%!% begin example\nWeb prose.\n%!% end example\n')
            dump(root/'correspondence.json',{'passages':[{'id':'example'}]})
            with patch.multiple(check_preservation,ROOT=root,REPO=private,ANNOTATED=annotated,BUILD=root/'build',BOOK_CHAPTERS=[{'source':CHAPTER}]), patch.object(check_preservation,'selected_source',lambda s,chapter=CHAPTER:s):
                report=check_preservation.check_annotations()
                self.assertEqual(report['status'],'passed')
                self.assertFalse(report['matches_private_manuscript'])
                self.assertEqual(report['passages'],1)
                write(annotated/CHAPTER,'Web prose without the required marker.\n')
                with self.assertRaisesRegex(ValueError,'passages do not match'): check_preservation.check_annotations()
                (annotated/CHAPTER).unlink()
                with self.assertRaisesRegex(ValueError,'Missing annotated chapter'): check_preservation.check_annotations()

    def test_module_alias_does_not_capture_later_declarations(self):
        source='module M.Top where\nf : A\nf = x\n  where\n  module Alias = SomeModule x\n\ng : A\ng = x\n  where\n  local = x\n\nmodule Nested where\n  module N = OtherModule\n  h : A\n  h = x\n'
        self.assertEqual(declaration_range(source,'g')['qualified'],'g')
        self.assertEqual(declaration_range(source,'h')['qualified'],'Nested.h')
    def test_repeated_empty_compiler_alias_uses_first_location(self):
        from assemble import unique_agda_ids
        pre=next(parse('<pre><a id="M.I"></a><a id="1">I</a>\n<a id="M.I"></a><a id="3">I</a></pre>').all('pre'))
        self.assertEqual(compiler_anchors(pre,{1,2})['M.I'],1)
        text=pre.text(); unique_agda_ids(pre)
        self.assertEqual(pre.text(),text)
        self.assertEqual(sum(a.attrs.get('id')=='M.I' for a in pre.all('a')),1)
        self.assertEqual(compiler_anchors(pre,{1,2}),{'M.I':1,'1':1,'3':2})
        duplicate=next(parse('<pre><a id="1">a</a><a id="1">b</a></pre>').all('pre'))
        with self.assertRaises(ValueError): unique_agda_ids(duplicate)
    def test_failed_agda_check_keeps_the_live_site(self):
        import tempfile
        from unittest.mock import patch
        import build
        from authored_pages import AUTHORED_PAGES
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); site=root/'_site'; output=root/'_build'; snapshot=output/'snapshot'
            snapshot.mkdir(parents=True); site.mkdir()
            for name in AUTHORED_PAGES: write(site/name,'Author text')
            write(site/'basic-vocabulary.html','Working preview')
            dump(snapshot/'inputs.json',{'files':{}})
            with patch.multiple(build,ROOT=root,SITE=site,BUILD=output,SNAP=snapshot), patch.object(build,'prepare'), patch.object(build,'run',side_effect=RuntimeError('Agda failed')):
                with self.assertRaisesRegex(RuntimeError,'Agda failed'): build.build()
            self.assertEqual(read(site/'basic-vocabulary.html'),'Working preview')
            for name in AUTHORED_PAGES: self.assertEqual(read(site/name),'Author text')

    def test_publish_preserves_late_author_edits_and_replaces_generated_files(self):
        import tempfile
        from publish_site import publish_generated_pages
        from authored_pages import AUTHORED_PAGES
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); site=root/'_site'; stage=root/'_build/site-stage-test'
            site.mkdir(); stage.mkdir(parents=True)
            for name in AUTHORED_PAGES:
                write(stage/name,'Earlier author text'); write(site/name,'Latest author text')
            write(site/'basic-vocabulary.html','Old preview'); write(site/'stale.html','Old page')
            write(stage/'basic-vocabulary.html','New preview'); write(stage/'assets/reader.js','New script')
            publish_generated_pages(stage,site,root)
            self.assertEqual(read(site/'basic-vocabulary.html'),'New preview')
            self.assertEqual(read(site/'assets/reader.js'),'New script')
            self.assertFalse((site/'stale.html').exists())
            for name in AUTHORED_PAGES: self.assertEqual(read(site/name),'Latest author text')
            with self.assertRaisesRegex(ValueError,'Unsafe publication'): publish_generated_pages(stage,root,root)

    def test_nested_module_continues_across_literate_prose(self):
        source='```agda\nmodule M.Top where\nmodule Nested where\n  f : A\n  f = a\n```\n\nExplanation between code blocks.\n\n```agda\n  g : A\n  g = f\n\nh : A\nh = a\n```\n'
        loc=declaration_range(source,'g','Nested.g')
        self.assertEqual(source[loc['start']:loc['end']],'  g : A\n  g = f')
        self.assertEqual(declaration_range(source,'h')['qualified'],'h')
        record='```agda\nmodule M.Top where\nrecord R : Set₁ where\n  field\n    value : Set\n```\n'
        loc=declaration_range(record,'R','R')
        self.assertEqual(record[loc['start']:loc['end']],'record R : Set₁ where\n  field\n    value : Set')
    def test_compiler_definition_anchors_include_binders_and_aliases(self):
        pre=next(parse('<pre>module M where\n<a id="f"></a><a id="16">f</a> : (<a id="21">α</a> : Set)\n  → α\nf x = x\n</pre>').all('pre'))
        self.assertEqual(compiler_anchors(pre,{1,2,3,4}),{'f':2,'16':2,'21':2})
        self.assertEqual(compiler_anchors(pre,{3,4}),{})
    def test_reverse_only_marker_preserves_prose_without_link(self):
        tex='%!% begin iteration\nThe same construction may be iterated.%!% end iteration\n'
        registry={'passages':[],'reverse_only':[{'id':'iteration'}]}
        self.assertEqual(tex_markers(tex)[0],'The same construction may be iterated.')
        html,ids=tex_markers(tex,True,registry)
        self.assertEqual(ids,['iteration'])
        self.assertIn('class="agda-book-anchor"',html)
        self.assertIn('tabindex="-1"',html)
        self.assertNotIn('href=',html)
        self.assertNotIn('data-agda=',html)
        with self.assertRaises(ValueError): tex_markers(tex+'%!% point iteration\n')
    def test_focus_uses_stable_region_after_binding_rename(self):
        source='f : A\nf =\n  let\n    --! begin first-comparison\n    renamed = step\n      argument\n    --! end first-comparison\n    other = result\n  in renamed\n'
        loc=declaration_range(source,'f')
        self.assertEqual(focused_lines(source,loc,{'regions':['first-comparison']}),[5,6])
        with self.assertRaises(ValueError): focused_lines(source,loc,{'regions':['missing']})
        with self.assertRaises(ValueError): focused_lines(source,loc,{'focus_note':'renamed'})
        with self.assertRaises(ValueError): focused_lines(source,loc,{'regions':[]})
    def test_disjoint_regions_and_declaration_containment(self):
        source='f : A\nf = pair-iso\n  --! begin first\n  (first (nested x)\n    y)\n  --! end first\n  --! begin second\n  (second z)\n  --! end second\ng : A\n--! begin outside\ng = a\n--! end outside\n'
        loc=declaration_range(source,'f')
        self.assertEqual(focused_lines(source,loc,{'regions':['first','second']}),[4,5,8])
        with self.assertRaises(ValueError): focused_lines(source,loc,{'regions':['outside']})
        with self.assertRaises(ValueError): focused_lines(source,loc,{'regions':['first','first']})
    def test_context_keeps_lines_and_links_without_duplicate_ids(self):
        source='```agda\n--! begin a-region\nα\nβ\n\n--! end a-region\n```\n'
        pre=next(parse('<pre>```agda\n--! begin a-region\n<a id="10" href="M.html#10" class="Function">α\nβ</a>\n\n--! end a-region\n```\n</pre>').all('pre'))
        result=module_lines(source,pre)
        self.assertEqual([x['number'] for x in result],[3,4,5])
        self.assertEqual([parse(x['html']).text() for x in result],['α','β',''])
        self.assertNotIn('id=',result[0]['html'])
        self.assertIn('href="agda/M.html#10"',result[1]['html'])
    def test_layout_signature_proof_and_unicode(self):
        text='```agda\nα : (A : Set)\n  → A → A\nα A a = a\n\nβ : Set₁\nβ = Set\n```\n'
        a,p,b=code_range(text,'α')
        self.assertEqual(text[a:p],'α : (A : Set)\n  → A → A\n')
        self.assertEqual(text[p:b],'α A a = a')
    def test_field_has_no_invented_proof(self):
        text='record R : Set₁ where\n  field\n    α : Set\n    β : α\n'
        a,p,b=code_range(text,'α'); self.assertIsNone(p); self.assertEqual(text[a:b],'    α : Set')
    def test_duplicate_signature_is_rejected(self):
        with self.assertRaises(ValueError): code_range('f : A\nf : B','f')
    def test_missing_signature_is_rejected(self):
        with self.assertRaises(ValueError): code_range('f : A','g')
    def test_html_preserves_source_text(self):
        source='α & β < γ\n'
        tree=parse('<pre>'+escape(source)+'</pre>')
        self.assertEqual(next(tree.all('pre')).text(),source)
        self.assertEqual(parse(tree.html()).text(),source)
    def test_comments_do_not_add_math_paragraphs(self):
        self.assertEqual(comments('a\n% hidden\n% second\nb'), 'a\nb')
    def test_qualified_field_and_record(self):
        source='module Test.Top where\nrecord R : Set₁ where\n  field\n    value : Set\nrecord S : Set₁ where\n  field\n    value : Set\n'
        with self.assertRaises(ValueError): declaration_range(source,'value')
        loc=declaration_range(source,'value','R.value')
        self.assertEqual(source[loc['start']:loc['end']],'    value : Set')
        loc=declaration_range(source,'R','R')
        self.assertIn('value : Set',source[loc['proof']:loc['end']])
        self.assertNotIn('record S',source[loc['start']:loc['end']])
    def test_named_arguments_in_module_parameters_preserve_scope(self):
        source='module Test.Top where\nmodule Outer (s : Cone (f {D = E})) where\n  module Lift (t : Cone (g {D = E})) where\n    abstract\n      comparison : A\n      comparison = a\n'
        loc=declaration_range(source,'comparison','Outer.Lift.comparison')
        self.assertEqual(source[loc['proof']:loc['end']],'      comparison = a')
    def test_parameterized_alias_does_not_capture_declarations(self):
        source='module Alias (a : A) = Existing a\nmodule Real where\n  comparison : A\n  comparison = a\n'
        loc=declaration_range(source,'comparison','Real.comparison')
        self.assertEqual(source[loc['proof']:loc['end']],'  comparison = a')
    def test_identical_diagram_occurrences_share_asset(self):
        from assemble import insert_diagrams
        body=parse('<div data-diagram="same"></div><p>Again:</p><div data-diagram="same"></div>')
        insert_diagrams(body,[{'id':'same'},{'id':'same'}])
        self.assertEqual([n.attrs['src'] for n in body.all('img')],['assets/diagrams/same.svg']*2)
        self.assertEqual(len(list(body.all('figure'))),2)
        for html in ('<div data-diagram="same"></div>', '<div data-diagram="same"></div><div data-diagram="other"></div>'):
            with self.assertRaisesRegex(ValueError,'Diagram marker mismatch'):
                insert_diagrams(parse(html),[{'id':'same'},{'id':'same'}])
    def test_mixfix_implementation(self):
        source='_∙_ : A → A → A\nβ ∙ α = compose β α\nother : A\nother = a\n'
        loc=declaration_range(source,'_∙_')
        self.assertEqual(source[loc['proof']:loc['end']],'β ∙ α = compose β α')
    def test_record_excludes_literate_fence_and_next_backlinks(self):
        source='record R : Set₁ where\n  field\n    value : Set\n\n-- @sct-link next pilot/tex/section-1-1.tex\nrecord S : Set₁ where\n  field\n    value : Set\n```\n'
        for name in ('R','S'):
            loc=declaration_range(source,name)
            text=source[loc['start']:loc['end']]
            self.assertNotIn('```',text)
            self.assertNotIn('@sct-link next',text)
    def test_marker_print_roundtrip(self):
        text='There are %!% begin categories\n'+r'\emph{categories}'+'%!% end categories\n.%!% point one\n'
        plain,ids=tex_markers(text)
        self.assertEqual(plain,r'There are \emph{categories}.')
        self.assertEqual(plain,comments(text))
        self.assertEqual(ids,['categories','one'])
        self.assertIn('id="text-categories"',tex_markers(text,True)[0])
        with self.assertRaises(ValueError): tex_markers(text+text)
        for opening,closing in [('$','$'),(r'\[',r'\]'),(r'\begin{equation}',r'\end{equation}')]:
            with self.subTest(opening=opening):
                with self.assertRaises(ValueError): tex_markers(opening+'%!% begin bad\nf%!% end bad\n'+closing)
                with self.assertRaises(ValueError): tex_markers('%!% begin bad\n'+opening+'f%!% end bad\n'+closing)
        self.assertEqual(tex_markers('%!% begin good\n$f$%!% end good\n')[0],'$f$')

    def test_comment_marker_validation_and_ordinary_comments(self):
        for source in ['%!% begin a\nx','%!% end a\n','%!% begin a\nx%!% end b\n',
                       '%!% begin a\nx%!% begin b\ny%!% end b\n%!% end a\n',
                       '%!% paragraph a\nx %!% point b\ny',
                       '%!% unknown a\n','%!% begin bad_id\n','%!% point a trailing text\n',
                       '%!% begin a\n%!% end a\n',r'\AgdaLink{a}{Old syntax}']:
            with self.subTest(source=source):
                with self.assertRaises(ValueError): tex_markers(source)
        with self.assertRaisesRegex(ValueError,'Unknown'):
            tex_markers('%!% point missing\n',registry={'passages':[]})
        source='% Ordinary comment mentioning %!% begin no-marker\nText.'
        self.assertEqual(tex_markers(source),(source,[]))
        for command in [r'\Cref{x}',r'\href{url}{text}',r'\url{url}']:
            with self.assertRaisesRegex(ValueError,'hyperlink'):
                tex_markers('%!% begin linked\n'+command+'%!% end linked\n')
        with self.assertRaisesRegex(ValueError,'hyperlink'):
            tex_markers(r'\href{url}{'+'%!% begin linked\ntext%!% end linked\n}')

    def test_paragraph_comment_and_label_backed_passages(self):
        source='%!% paragraph p\n\nA paragraph\nwith two lines.\n\nNext paragraph.'
        html,ids=tex_markers(source,True)
        self.assertEqual(ids,['p'])
        self.assertIn('A paragraph\nwith two lines.'+r'\HCode{</a>}'+'\n\nNext paragraph.',html)
        with self.assertRaises(ValueError): tex_markers('%!% paragraph empty\n\n')
        registry={'passages':[{'id':'equation','tex_label':'eq:one'},
                              {'id':'other-page','tex_label':'eq:two'}]}
        source=r'\begin{equation}\label{eq:one}1=1\end{equation}'
        self.assertEqual(tex_markers(source,True,registry),(source,['equation']))
        with self.assertRaisesRegex(ValueError,'Duplicate TeX label'):
            tex_markers(source+source,registry=registry)
        with self.assertRaisesRegex(ValueError,'both a label'):
            tex_markers('%!% point equation\n'+source,registry=registry)
        self.assertEqual(tex_markers('% '+source+'\n',registry=registry)[1],[])

    def test_comment_passages_stay_within_one_tex_block(self):
        for body in [r'\begin{definition}Text.\end{definition}',r'Text.\section{Next}',
                     r'First.\item Second.',r'First.\par Second.','First.\n\nSecond.',
                     r'\[f=g\]',r'$$f=g$$']:
            for kind in ('begin','paragraph'):
                # Paragraph markers stop at a blank line rather than crossing
                # it; every other structural token must be rejected.
                if kind=='paragraph' and '\n\n' in body: continue
                source='%!% '+kind+' p\n'+body+('%!% end p\n' if kind=='begin' else '')
                with self.subTest(kind=kind,body=body):
                    with self.assertRaisesRegex(ValueError,'block boundaries'): tex_markers(source)
        for body in ['$f=g$',r'\(f=g\)','First.\n% A normal author comment.\nSecond sentence.']:
            source='%!% begin p\n'+body+'%!% end p\n'
            self.assertEqual(comments(tex_markers(source)[0]),comments(source))
        source='Before.\n\n    %!% paragraph p\n  A paragraph.\n\nAfter.'
        plain,ids=tex_markers(source)
        self.assertEqual(plain,'Before.\n\n      A paragraph.\n\nAfter.')
        self.assertEqual(plain,comments(source))
        self.assertEqual(ids,['p'])

    def test_agda_publication_comments_do_not_break_scope(self):
        source='record R : Set₁ where\n--! begin fields\n  field\n    value : Set\n--! end fields\nrecord S : Set₁ where\n  field\n    value : Set\n'
        loc=declaration_range(source,'value','R.value')
        self.assertEqual(source[loc['start']:loc['end']].splitlines()[0],'    value : Set')
        loc=declaration_range(source,'R','R')
        self.assertIn('value : Set',source[loc['start']:loc['end']])
        self.assertNotIn('record S',source[loc['start']:loc['end']])

class ModuleNavigationTests(unittest.TestCase):
    def test_coherences_move_without_renaming_modules(self):
        from module_navigation import module_tree
        modules=['SCT.VolumeI.Chapter01.Section01.Vocabulary',
                 'SCT.VolumeI.Chapter01.Section01.Coherence',
                 'SCT.VolumeI.Chapter01.Section05.PullbackSquares']
        groups=module_tree(modules,retained=True)['children'][0]['children']
        self.assertEqual([g['label'] for g in groups],
                         ['1.1 The basic vocabulary','1.2 Coherences','1.6 Pullbacks of categories'])
        self.assertEqual(groups[1]['modules'],[modules[1]])

    def test_root_chapter_and_section_modules_each_appear_once(self):
        from module_navigation import module_tree, module_label
        modules=['SCT.WebEdition','Agda.Primitive','SCT.VolumeI.Chapter01.Everything',
                 'SCT.VolumeI.Chapter01.Section10.Example','SCT.VolumeI.Chapter01.Section02.Products',
                 'SCT.VolumeI.Chapter01.Section01.Vocabulary']
        tree=module_tree(reversed(modules))
        self.assertEqual(tree['modules'],['Agda.Primitive','SCT.WebEdition'])
        chapter=tree['children'][0]
        self.assertEqual(chapter['label'],'Chapter 1: The language of synthetic category theory')
        self.assertEqual(chapter['modules'],['SCT.VolumeI.Chapter01.Everything'])
        self.assertEqual([node['label'] for node in chapter['children']],
                         ['1.1 The basic vocabulary','1.2 Coherences','1.10'])
        def flatten(node): return node['modules']+[name for child in node['children'] for name in flatten(child)]
        self.assertCountEqual(flatten(tree),modules)
        self.assertEqual(module_label(modules[-1]),'Vocabulary')
        self.assertEqual(module_label('Agda.Primitive'),'Agda.Primitive')

    def test_multiple_volumes_keep_same_numbered_chapters_distinct(self):
        from module_navigation import module_tree
        tree=module_tree(['SCT.VolumeII.Chapter01.Section01.Example','SCT.VolumeI.Chapter01.Section01.Example'])
        self.assertEqual([node['label'] for node in tree['children']],['Volume I','Volume II'])
        self.assertNotEqual(tree['children'][0]['children'][0]['key'],tree['children'][1]['children'][0]['key'])

    def test_current_and_retained_section_numbers_do_not_get_confused(self):
        from module_navigation import module_tree
        module='SCT.VolumeI.Chapter01.Section03.Equivalences'
        group=module_tree([module])['children'][0]['children'][0]
        self.assertEqual(group['label'],'1.3 Equivalences of categories')
        old='SCT.VolumeI.Chapter01.Section09.Morphisms'
        chapter=module_tree([old],retained=True)['children'][0]
        self.assertEqual(chapter['label'],'Chapter 2: The internal structure of categories')
        self.assertEqual(chapter['children'][0]['label'],'2.1 Morphisms and diagrams')

    def test_split_declarations_resolve_to_the_checked_source(self):
        from module_layout import previous_module
        self.assertEqual(previous_module('SCT.VolumeI.Chapter01.Section02.Diagrams','NatIsoSquare'),
                         'SCT.VolumeI.Chapter01.Section01.Diagrams')
        self.assertEqual(previous_module('SCT.VolumeI.Chapter01.Section02.Coherence','VerticalCoherence'),
                         'SCT.VolumeI.Chapter01.Section01.Coherence')

class DistributionTests(unittest.TestCase):
    def test_separate_tex_footnote_keeps_text_and_bidirectional_links(self):
        import tempfile
        from assemble import join_footnotes
        with tempfile.TemporaryDirectory() as directory:
            body=parse('<body><p>Prose<a href="pilot2.html#fn1x1">1</a></p></body>')
            body=next(body.all('body'))
            write(Path(directory)/'pilot2.html','<body><div class="footnote-text"><a id="fn1x1"></a>Note <a href="pilot.html#definition">definition</a></div></body>')
            join_footnotes(body,Path(directory))
            self.assertIn('Note definition',body.text())
            links=[a.attrs.get('href') for a in body.all('a')]
            self.assertIn('#fn1x1',links)
            self.assertIn('#footnote-ref-fn1x1',links)
            self.assertIn('pilot.html#definition',links)
            self.assertNotIn('pilot2.html#fn1x1',links)

    def test_retained_check_rejects_changed_code_or_compiler_output(self):
        import tempfile
        from unittest.mock import patch
        import checked_code
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);snap=root/'snapshot';retained=root/'retained.json'
            write(snap/'agda/src/SCT.agda','module SCT where\n')
            write(root/'agda/SCT.html','<pre>module SCT where</pre>')
            original={'files':{'agda/src/SCT.agda':digest((snap/'agda/src/SCT.agda').read_bytes()),'chapter.tex':'old'}}
            dump(snap/'inputs.json',original)
            dump(root/'check.json',{'checked':True,'input_hash':digest(json.dumps(original['files'],sort_keys=True))})
            with patch.multiple(checked_code,BUILD=root,SNAP=snap,RETAINED=retained):
                checked_code.retain_checked_code()
                updated={'files':dict(original['files'],**{'chapter.tex':'new'})}
                self.assertIn('previously checked',checked_code.verify_checked_code(updated))
                write(root/'agda/SCT.html','Changed HTML')
                with self.assertRaisesRegex(ValueError,'compiler output changed'): checked_code.verify_checked_code(updated)
                write(root/'agda/SCT.html','<pre>module SCT where</pre>')
                write(snap/'agda/src/SCT.agda','Changed source')
                with self.assertRaisesRegex(ValueError,'source changed'): checked_code.verify_checked_code(updated)

    def test_build_cleanup_preserves_direct_edits_even_if_build_stops(self):
        import tempfile
        from authored_pages import AUTHORED_PAGES, clear_generated_pages
        with tempfile.TemporaryDirectory() as directory:
            site=Path(directory)/'_site'
            originals={name:('<p>Author edits: animae, α. '+name+'</p>\r\n').encode('utf-8') for name in AUTHORED_PAGES}
            site.mkdir()
            for name, data in originals.items(): (site/name).write_bytes(data)
            write(site/'agda/old.html','Generated code')
            write(site/'basic-vocabulary.html','Generated book text')
            clear_generated_pages(site,directory)
            self.assertEqual({p.name for p in site.iterdir()},set(originals))
            for name, data in originals.items(): self.assertEqual((site/name).read_bytes(),data)

    def test_missing_authored_page_aborts_cleanup_without_removing_files(self):
        import tempfile
        from authored_pages import clear_generated_pages
        with tempfile.TemporaryDirectory() as directory:
            site=Path(directory)/'_site'
            write(site/'index.html','My homepage')
            write(site/'basic-vocabulary.html','Existing generated page')
            with self.assertRaisesRegex(ValueError,'Restore the editable pages'):
                clear_generated_pages(site,directory)
            self.assertEqual(read(site/'index.html'),'My homepage')
            self.assertTrue((site/'basic-vocabulary.html').exists())

    def test_private_paths_and_unselected_modules_fail_closed(self):
        import tempfile
        from check_site_boundary import check
        with tempfile.TemporaryDirectory() as directory:
            site=Path(directory)
            write(site/'index.html','<meta name="robots" content="noindex,nofollow">Book')
            dump(site/'build-info.json',{'published_modules':['SCT.Selected']})
            write(site/'source-files/SCT/Selected.agda','module SCT.Selected where\n')
            self.assertEqual(check(site)['published_source_modules'],1)
            # A source-only module must remain outside the deployment artifact.
            extra=site/'source-files/SCT/Omitted.agda'
            write(extra,'module SCT.Omitted where\n')
            with self.assertRaisesRegex(ValueError,'Raw modules'): check(site)
            extra.unlink()
            dump(site/'build-info.json',{'published_modules':['SCT.Selected'],'source':'C:/Users/Example/private.tex'})
            with self.assertRaisesRegex(ValueError,'Private path'): check(site)
            dump(site/'build-info.json',{'published_modules':['SCT.Selected']})
            write(site/'README.md','Private notes')
            with self.assertRaisesRegex(ValueError,'allowlist'): check(site)
            (site/'README.md').unlink()
            write(site/'chapter.tex','Private manuscript')
            with self.assertRaisesRegex(ValueError,'Private source'): check(site)

    def test_selection_uses_complete_chapter_labels(self):
        source=r'\begin{document}'+'Opening.\n'
        for title,label in [('Vocabulary','sec:External_Theory'),('Coherences','sec:Coherences'),('Equivalences','sec:Equivalence_Of_Categories'),('Mapping animae','sec:Mapping_Animae'),('Initial categories','sec:Initial_Categories_And_Coproducts'),('Pullbacks','sec:Pullbacks_Of_Categories'),('Functor categories','sec:Functor_Categories'),('Pushouts','sec:Pushouts_Of_Categories')]:
            source+=r'\section{'+title+r'}\label[section]{'+label+'}\n'+title+' prose.\n'
        source+=r'\section{Exercises}'+'\nExercises prose.\n'+r'\end{document}'
        selected=selected_source(source)
        self.assertIn('Opening.',selected)
        self.assertIn('Equivalences prose.',selected)
        self.assertIn('Mapping animae prose.',selected)
        self.assertIn('Initial categories prose.',selected)
        self.assertIn('Pullbacks prose.',selected)
        self.assertIn('Functor categories prose.',selected)
        self.assertIn('Pushouts prose.',selected)
        self.assertNotIn('Exercises prose.',selected)
        with self.assertRaises(ValueError): selected_source(source.replace('sec:External_Theory','unexpected'))

if __name__=='__main__': unittest.main()
