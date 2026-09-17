import unittest
from common import *
from assemble import code_range
from pilot_model import declaration_range,tex_markers
from reader_context import focused_lines,module_lines,compiler_anchors

class PipelineTests(unittest.TestCase):
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

class DistributionTests(unittest.TestCase):
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
        for title,label in [('Vocabulary','sec:External_Theory'),('Equivalences','sec:Equivalence_Of_Categories'),('Mapping animae','sec:Mapping_Animae')]:
            source+=r'\section{'+title+r'}\label[section]{'+label+'}\n'+title+' prose.\n'
        source+=r'\end{document}'
        selected=selected_source(source)
        self.assertIn('Opening.',selected)
        self.assertIn('Equivalences prose.',selected)
        self.assertNotIn('Mapping animae',selected)
        with self.assertRaises(ValueError): selected_source(source.replace('sec:External_Theory','unexpected'))

if __name__=='__main__': unittest.main()
