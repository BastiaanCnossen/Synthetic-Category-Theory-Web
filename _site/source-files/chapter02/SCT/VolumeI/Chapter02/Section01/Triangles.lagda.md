# Triangles and prescribed short edges

A triangle family has two short-edge families with their specified common
vertex. The chosen pullback of target and source records this matching.
Restricting a triangle to its short edges gives a functor to that pullback,
and its beta is the whole cone comparison, including the junction square.

For a prescribed family of composable pairs, the category of completions
is the pullback of this restriction. It retains the parameter projection;
no contractibility is asserted for an arbitrary parameter category.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.Triangles where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames
  using (module PairedRestrictionImage; pair-action-image; paired-input-image; module PairedBaseImage)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; preWhisker-id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; post-triangle; unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; evAt-pre; evAt-cong)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₀; d₁; d₂; face-middle; vertex₀; vertex₁; vertex₂;
    d₂-zero; d₂-one; d₀-zero; d₀-one; d₁-zero; d₁-one)

module _ {Γ : Context} where
  Triangles : CAT Γ → CAT Γ
  Triangles C = Fun [2] C

  Triangle : CAT Γ → Set m
  Triangle C = MAP [2] C

  edge₀ edge₁ edge₂ : {C : CAT Γ} → MAP (Triangles C) (Ar C)
  edge₀ = funPre d₀
  edge₁ = funPre d₁
  edge₂ = funPre d₂

  Composable : CAT Γ → CAT Γ
  Composable C = Pullback (ev₁ {C = C}) ev₀

  triangle-cone : (C : CAT Γ) → Cone (ev₁ {C = C}) ev₀ (Triangles C)
  triangle-cone C = record
    { left = edge₂; right = edge₀
    ; match = (evAt-pre zero d₀) ⁻¹ ∙
        (evAt-cong (face-middle ⁻¹) ∙ evAt-pre one d₂) }

  short-edges : (C : CAT Γ) → MAP (Triangles C) (Composable C)
  short-edges C = pullback-factor (triangle-cone C)

  short-edges-image : (C : CAT Γ) → ConeIdentification₁
    (cone-restrict (short-edges C) (pullback-cone (ev₁ {C = C}) ev₀))
    (triangle-cone C)
  short-edges-image C = pullback-factor-β (triangle-cone C)

  Composites : {P C : CAT Γ} → MAP P (Composable C) → CAT Γ
  Composites {C = C} p = Pullback (short-edges C) p

  module Completions {P C : CAT Γ} (p : MAP P (Composable C)) where
    universal : Cone (short-edges C) p (Composites p)
    universal = pullback-cone (short-edges C) p
    triangle : MAP (Composites p) (Triangles C)
    triangle = Cone.left universal
    base : MAP (Composites p) P
    base = Cone.right universal
    boundary : (short-edges C ∘ triangle) =₁ (p ∘ base)
    boundary = Cone.match universal

    extension : {T : CAT Γ} (s : Cone (short-edges C) p T) → MAP T (Composites p)
    extension = pullback-factor
    extension-image : {T : CAT Γ} (s : Cone (short-edges C) p T)
      → ConeIdentification₁ (cone-restrict (extension s) universal) s
    extension-image = pullback-factor-β
```

Restriction retains all three vertices. Its underlying functor remains
the same chosen pullback factor; the base triangle uses its actual beta
and the face-to-vertex comparisons. The long edge lies over the first
and last vertex.

```agda
private
  module _ {Γ : Context} {A C T : CAT Γ} (source target : MAP A C)
    (s : Cone target source T)
    (v₀ v₁ v₂ : MAP T C)
    (first-source : (source ∘ Cone.left s) =₁ v₀)
    (first-target : (target ∘ Cone.left s) =₁ v₁)
    (second-target : (target ∘ Cone.right s) =₁ v₂) where

    vertex-restriction-over : FunctorOverBase
      (category-over T (pair (pair v₀ v₁) v₂))
      (category-over (Pullback target source)
        (pair (pair (source ∘ pullback₁) (target ∘ pullback₁)) (target ∘ pullback₂)))
    vertex-restriction-over = functor-over (pullback-factor s)
      (pair⁼ (pair⁼ first-image middle-image ∙
          pair-pre (source ∘ pullback₁) (target ∘ pullback₁) (pullback-factor s)) last-image ∙
        pair-pre (pair (source ∘ pullback₁) (target ∘ pullback₁))
          (target ∘ pullback₂) (pullback-factor s))
      where
        first-image : ((source ∘ pullback₁) ∘ pullback-factor s) =₁ v₀
        first-image = first-source ∙
          ((source ◁ ConeIdentification₁.left (pullback-factor-β s)) ∙
            comp-assoc (pullback-factor s) pullback₁ source)
        middle-image : ((target ∘ pullback₁) ∘ pullback-factor s) =₁ v₁
        middle-image = first-target ∙
          ((target ◁ ConeIdentification₁.left (pullback-factor-β s)) ∙
            comp-assoc (pullback-factor s) pullback₁ target)
        last-image : ((target ∘ pullback₂) ∘ pullback-factor s) =₁ v₂
        last-image = second-target ∙
          ((target ◁ ConeIdentification₁.right (pullback-factor-β s)) ∙
            comp-assoc (pullback-factor s) pullback₂ target)

module _ {Γ : Context} where
  Vertices : CAT Γ → CAT Γ
  Vertices C = (C × C) × C

  triangle-vertices : (C : CAT Γ) → MAP (Triangles C) (Vertices C)
  triangle-vertices C = pair (pair (evAt vertex₀) (evAt vertex₁)) (evAt vertex₂)

  pair-vertices : (C : CAT Γ) → MAP (Composable C) (Vertices C)
  pair-vertices C = pair (pair (ev₀ ∘ pullback₁) (ev₁ ∘ pullback₁)) (ev₁ ∘ pullback₂)

  triangles-over : (C : CAT Γ) → CategoryOverBase (Vertices C)
  triangles-over C = category-over (Triangles C) (triangle-vertices C)
  pairs-over : (C : CAT Γ) → CategoryOverBase (Vertices C)
  pairs-over C = category-over (Composable C) (pair-vertices C)

  short-edges-over : (C : CAT Γ) → FunctorOverBase (triangles-over C) (pairs-over C)
  short-edges-over C = vertex-restriction-over ev₀ ev₁ (triangle-cone C)
    (evAt vertex₀) (evAt vertex₁) (evAt vertex₂)
    (evAt-cong d₂-zero ∙ evAt-pre zero d₂)
    (evAt-cong d₂-one ∙ evAt-pre one d₂)
    (evAt-cong d₀-one ∙ evAt-pre one d₀)

  outer-vertices : {C : CAT Γ} → MAP (Vertices C) (C × C)
  outer-vertices = pair (pr₁ ∘ pr₁) pr₂

  arrows-over : (C : CAT Γ) → CategoryOverBase (C × C)
  arrows-over C = category-over (Ar C) (pair ev₀ ev₁)

  long-edge-over : (C : CAT Γ)
    → FunctorOverMap outer-vertices (triangles-over C) (arrows-over C)
  long-edge-over C = functor-over edge₁
    (outer-image ⁻¹ ∙
      (pair⁼ (evAt-cong d₁-zero ∙ evAt-pre zero d₁)
        (evAt-cong d₁-one ∙ evAt-pre one d₁) ∙ pair-pre ev₀ ev₁ edge₁))
    where
      module V = Triple (evAt {C = C} vertex₀) (evAt vertex₁) (evAt vertex₂)
      outer-image : (outer-vertices ∘ triangle-vertices C) =₁
        pair (evAt vertex₀) (evAt vertex₂)
      outer-image = pair⁼ V.first V.third ∙
        pair-pre (pr₁ ∘ pr₁) pr₂ (triangle-vertices C)
```

The source of the second short edge is the same middle vertex as the
target of the first short edge, through the actual chosen junction.
Evaluation preserves the specified composite through the named vertex;
the two laws used below follow from pairing and whiskering.

```agda
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationAction public
  using (evaluation-point-cong; evaluation-point-comp)

private
  module _ {Γ : Context} where
    middle-point-junction :
      (d₀-zero {Γ = Γ} ∙ (face-middle ⁻¹)) =₂ d₂-one
    middle-point-junction = cancel-right face-middle
      ((comp-inv-left d₂-one d₀-zero) ⁻¹ ∙ inv-comp-right d₀-zero face-middle)

module _ {Γ : Context} where
  triangle-junction-vertex : (C : CAT Γ)
    → ((evAt-cong d₀-zero ∙ evAt-pre zero d₀) ∙ Cone.match (triangle-cone C)) =₂
        (evAt-cong d₂-one ∙ evAt-pre one d₂)
  triangle-junction-vertex C = comp₌-cong evaluated (id₌ first-evaluation) ∙
    ((comp₌-assoc second-vertex junction-evaluation first-evaluation) ⁻¹ ∙
      (comp₌-cong (id₌ second-vertex)
        (comp-inv-left second-evaluation (junction-evaluation ∙ first-evaluation)) ∙
        comp₌-assoc second-vertex second-evaluation
          (second-evaluation ⁻¹ ∙ (junction-evaluation ∙ first-evaluation))))
    where
      second-vertex = evAt-cong {C = C} d₀-zero
      junction-evaluation = evAt-cong {C = C} (face-middle ⁻¹)
      first-evaluation = evAt-pre {C = C} one d₂
      second-evaluation = evAt-pre {C = C} zero d₀
      evaluated : (second-vertex ∙ junction-evaluation) =₂ evAt-cong {C = C} d₂-one
      evaluated = evaluation-point-cong middle-point-junction ∙
        (evaluation-point-comp d₀-zero (face-middle ⁻¹)) ⁻¹


  middle-vertices : {C : CAT Γ} → MAP (Vertices C) (C × C)
  middle-vertices = pair (pr₂ ∘ pr₁) pr₂

  private
    middle-image : {T C : CAT Γ} (u v w : MAP T C)
      → (middle-vertices ∘ pair (pair u v) w) =₁ pair v w
    middle-image u v w = pair⁼ V.second V.third ∙
      pair-pre (pr₂ ∘ pr₁) pr₂ (pair (pair u v) w)
      where module V = Triple u v w

  first-projection-over : (C : CAT Γ)
    → FunctorOverMap pr₁ (pairs-over C) (arrows-over C)
  first-projection-over C = functor-over pullback₁
    ((pair-β₁ (pair (ev₀ ∘ pullback₁) (ev₁ ∘ pullback₁)) (ev₁ ∘ pullback₂)) ⁻¹ ∙
      pair-pre ev₀ ev₁ pullback₁)

  second-projection-over : (C : CAT Γ)
    → FunctorOverMap middle-vertices (pairs-over C) (arrows-over C)
  second-projection-over C = functor-over pullback₂
    ((middle-image (ev₀ ∘ pullback₁) (ev₁ ∘ pullback₁) (ev₁ ∘ pullback₂)) ⁻¹ ∙
      (pair⁼ (pullback-match ⁻¹) (id₌ (ev₁ ∘ pullback₂)) ∙
        pair-pre ev₀ ev₁ pullback₂))

  first-edge-over : (C : CAT Γ)
    → FunctorOverMap pr₁ (triangles-over C) (arrows-over C)
  first-edge-over C = functor-over edge₂
    ((pair-β₁ (pair (evAt vertex₀) (evAt vertex₁)) (evAt vertex₂)) ⁻¹ ∙
      (pair⁼ (evAt-cong d₂-zero ∙ evAt-pre zero d₂)
        (evAt-cong d₂-one ∙ evAt-pre one d₂) ∙ pair-pre ev₀ ev₁ edge₂))

  second-edge-over : (C : CAT Γ)
    → FunctorOverMap middle-vertices (triangles-over C) (arrows-over C)
  second-edge-over C = functor-over edge₀
    ((middle-image (evAt vertex₀) (evAt vertex₁) (evAt vertex₂)) ⁻¹ ∙
      (pair⁼ (evAt-cong d₀-zero ∙ evAt-pre zero d₀)
        (evAt-cong d₀-one ∙ evAt-pre one d₀) ∙ pair-pre ev₀ ev₁ edge₀))

```

The relative short-edge beta laws retain these four selected relative maps.
Projection of the chosen three-vertex cell is normalized by the actual
pairing and nested-projection laws. The second source uses the whole cone
beta and the middle-vertex junction equation above. Neither beta component
is replaced by a reflected identification.

The following finite private calculations reuse the paired restriction and
projected-cell proofs. Pairing the two projected vertex squares retains the
specified old and new projection triangles. This includes the outer
associator in the actual comp-over-map cell.

```agda
private
  module ProjectedEdgeImage {Γ : Context} {P T A B S : CAT Γ}
    (baseP : MAP P S) (baseT : MAP T S) (k : MAP S B)
    (q : MAP T P) (π : MAP P A) (edge : MAP T A) (projection : MAP A B)
    {u : MAP P B} {v : MAP T B}
    (old : (k ∘ baseP) =₁ u) (new : (k ∘ baseT) =₁ v)
    (edgeP : (projection ∘ π) =₁ u) (edgeT : (projection ∘ edge) =₁ v)
    (base-cell : (baseP ∘ q) =₁ baseT) (δ : (π ∘ q) =₁ edge)
    (projected : (u ∘ q) =₁ v)
    (projected-square :
      (new ∙ ((k ◁ base-cell) ∙ comp-assoc q baseP k)) =₂
        (projected ∙ (old ▷ q)))
    (edge-square : (projected ∙ (edgeP ▷ q)) =₂
      ((edgeT ∙ (projection ◁ δ)) ∙ comp-assoc q π projection)) where
    private
      changed = k ◁ base-cell
      base-assoc = comp-assoc q baseP k
      old-restricted = old ▷ q
      edge-restricted = edgeP ▷ q
      edge-assoc = comp-assoc q π projection
      projection-restricted = ((old ⁻¹) ∙ edgeP) ▷ q
      native-cell = changed ∙
        (base-assoc ∙ (projection-restricted ∙ (edge-assoc ⁻¹)))
      triangle-cell = (new ⁻¹) ∙ edgeT
      action = projection ◁ δ

      restriction-image : projection-restricted =₂
        ((old-restricted ⁻¹) ∙ edge-restricted)
      restriction-image = comp₌-cong (preWhisker-inverse old q) (id₌ edge-restricted) ∙
        preWhisker-comp₌ (old ⁻¹) edgeP q

      projected-image : (new ∙ native-cell) =₂
        ((projected ∙ edge-restricted) ∙ (edge-assoc ⁻¹))
      projected-image = (comp₌-assoc projected edge-restricted (edge-assoc ⁻¹)) ⁻¹ ∙
        (comp₌-cong (id₌ projected)
          (comp-inv-left old-restricted (edge-restricted ∙ (edge-assoc ⁻¹))) ∙
          (comp₌-assoc projected old-restricted
            ((old-restricted ⁻¹) ∙ (edge-restricted ∙ (edge-assoc ⁻¹))) ∙
            (comp₌-cong (id₌ (projected ∙ old-restricted))
              (comp₌-assoc (old-restricted ⁻¹) edge-restricted (edge-assoc ⁻¹)) ∙
              (comp₌-cong projected-square
                (comp₌-cong restriction-image (id₌ (edge-assoc ⁻¹))) ∙
                ((comp₌-assoc new (changed ∙ base-assoc)
                  (projection-restricted ∙ (edge-assoc ⁻¹))) ⁻¹ ∙
                  comp₌-cong (id₌ new)
                    ((comp₌-assoc changed base-assoc
                      (projection-restricted ∙ (edge-assoc ⁻¹))) ⁻¹))))))

      native-image : (new ∙ native-cell) =₂ (edgeT ∙ action)
      native-image = comp-inv-right (edgeT ∙ action) edge-assoc ∙
        (comp₌-cong edge-square (id₌ (edge-assoc ⁻¹)) ∙ projected-image)

      triangle-image : (new ∙ (triangle-cell ∙ action)) =₂ (edgeT ∙ action)
      triangle-image = comp₌-cong (comp-inv-left new edgeT) (id₌ action) ∙
        ((comp₌-assoc new triangle-cell action) ⁻¹)

    compatible : CompatibleOver projection native-cell triangle-cell δ
    compatible = cancel-left new ((native-image ⁻¹) ∙ triangle-image)


private
  module NestedVertexImage {Γ : Context} {P T K E B : CAT Γ}
    (π : MAP E B) (baseP : MAP P K) (q : MAP T P) (baseT : MAP T K)
    (δ : (baseP ∘ q) =₁ baseT) (r : MAP K E)
    {u : MAP P E} {v : MAP T E} {x : MAP P B} {y : MAP T B}
    (old : (r ∘ baseP) =₁ u) (new : (r ∘ baseT) =₁ v)
    (edge : (u ∘ q) =₁ v)
    (old-inner : (π ∘ u) =₁ x) (new-inner : (π ∘ v) =₁ y)
    (inner : (x ∘ q) =₁ y)
    (outer-square : (new ∙ (r ◁ δ)) =₂ (edge ∙ restrict-triangle r baseP old q))
    (inner-square : (new-inner ∙ (π ◁ edge)) =₂
      (inner ∙ restrict-triangle π u old-inner q)) where
    private
      old-post = post-triangle π r baseP old
      new-post = post-triangle π r baseT new
      tail = ((π ∘ r) ◁ δ) ∙ comp-assoc q baseP (π ∘ r)
      A′ = comp-assoc q u π
      coordinate = post-triangle-change π r baseP q baseT δ old new edge outer-square
      projection = unrestrict-square π u q v edge old-inner new-inner inner inner-square

    image : ((new-inner ∙ new-post) ∙ tail) =₂ ((inner ∙ ((old-inner ∙ old-post) ▷ q)))
    image = comp₌-cong (id₌ inner) ((preWhisker-comp₌ old-inner old-post q) ⁻¹) ∙
      (comp₌-assoc inner (old-inner ▷ q) (old-post ▷ q) ∙
        (comp₌-cong projection (id₌ (old-post ▷ q)) ∙
          ((comp₌-assoc new-inner ((π ◁ edge) ∙ A′) (old-post ▷ q)) ⁻¹ ∙
            (comp₌-cong (id₌ new-inner) ((comp₌-assoc (π ◁ edge) A′ (old-post ▷ q)) ⁻¹) ∙
              (comp₌-cong (id₌ new-inner) coordinate ∙
                comp₌-assoc new-inner new-post tail)))))

  module ActualShortEdgeImages {Γ : Context} (C : CAT Γ) where
    private
      q = short-edges C
      baseP = pair-vertices C
      baseT = triangle-vertices C
      base-cell = FunctorOverBase.cell (short-edges-over C)
      δ₁ = ConeIdentification₁.left (short-edges-image C)
      δ₂ = ConeIdentification₁.right (short-edges-image C)
      src = ev₀ {C = C}
      tgt = ev₁ {C = C}
      s₁ = src ∘ pullback₁ {f = tgt} {g = src}
      t₁ = tgt ∘ pullback₁ {f = tgt} {g = src}
      t₂ = tgt ∘ pullback₂ {f = tgt} {g = src}
      v₀ = evAt {C = C} vertex₀
      v₁ = evAt {C = C} vertex₁
      v₂ = evAt {C = C} vertex₂
      a₁ = evAt-cong {C = C} d₂-zero ∙ evAt-pre zero d₂
      b₁ = evAt-cong {C = C} d₂-one ∙ evAt-pre one d₂
      a₂ = evAt-cong {C = C} d₀-zero ∙ evAt-pre zero d₀
      b₂ = evAt-cong {C = C} d₀-one ∙ evAt-pre one d₀
      first-frame = a₁ ∙ ((src ◁ δ₁) ∙ comp-assoc q pullback₁ src)
      middle-frame = b₁ ∙ ((tgt ◁ δ₁) ∙ comp-assoc q pullback₁ tgt)
      last-frame = b₂ ∙ ((tgt ◁ δ₂) ∙ comp-assoc q pullback₂ tgt)
      first-pair = pair⁼ first-frame middle-frame ∙ pair-pre s₁ t₁ q
      second-pair = pair⁼ middle-frame last-frame ∙ pair-pre t₁ t₂ q
      module Old = Triple s₁ t₁ t₂
      module New = Triple v₀ v₁ v₂
      old-first = pair-β₁ (pair s₁ t₁) t₂
      new-first = pair-β₁ (pair v₀ v₁) v₂
      outer-first = pair-evaluation-over₁-One (pair s₁ t₁) t₂ q first-pair last-frame
      outer-last = pair-evaluation-over₂-One (pair s₁ t₁) t₂ q first-pair last-frame

      first-base-square = unrestrict-square pr₁ baseP q baseT base-cell
        old-first new-first first-pair outer-first
      module Middle = NestedVertexImage pr₂ baseP q baseT base-cell pr₁
        old-first new-first first-pair (pair-β₂ s₁ t₁) (pair-β₂ v₀ v₁) middle-frame
        outer-first (pair-evaluation-over₂-One s₁ t₁ q first-frame middle-frame)
      last-base-square = unrestrict-square pr₂ baseP q baseT base-cell
        Old.third New.third last-frame outer-last
      module MiddlePair = PairedBaseImage (pr₂ ∘ pr₁) pr₂ baseP q baseT base-cell
        Old.second Old.third New.second New.third middle-frame last-frame
        Middle.image last-base-square

      endpoint₁ = pair⁼ a₁ b₁ ∙ pair-pre src tgt edge₂
      endpoint₂ = pair⁼ a₂ b₂ ∙ pair-pre src tgt edge₀
      module FirstRestriction = PairedRestrictionImage src tgt pullback₁ q edge₂ δ₁ a₁ b₁
      first-edge-square = comp₌-cong
        ((pair-action-image src tgt δ₁ a₁ b₁) ⁻¹)
        (id₌ (comp-assoc q pullback₁ (pair src tgt))) ∙ FirstRestriction.image

      junction = Cone.match (triangle-cone C)
      L = tgt ◁ δ₁
      R = src ◁ δ₂
      A₁ = comp-assoc q pullback₁ tgt
      A₂ = comp-assoc q pullback₂ src
      M = pullback-match {f = tgt} {g = src} ▷ q
      second-source = a₂ ∙ (R ∙ A₂)
      matching = A₂ ∙ (M ∙ (A₁ ⁻¹))
      full-square = ConeIdentification₁.compatible (short-edges-image C)
      left-normal : ((second-source ∙ M) ∙ (A₁ ⁻¹)) =₂ (b₁ ∙ L)
      left-normal = comp₌-cong (triangle-junction-vertex C) (id₌ L) ∙
        ((comp₌-assoc a₂ junction L) ⁻¹ ∙
          (comp₌-cong (id₌ a₂) (full-square ⁻¹) ∙
            (comp₌-cong (id₌ a₂) (comp₌-assoc R A₂ (M ∙ (A₁ ⁻¹))) ∙
              (comp₌-assoc a₂ (R ∙ A₂) (M ∙ (A₁ ⁻¹)) ∙
                comp₌-assoc second-source M (A₁ ⁻¹)))))
      right-normal : (middle-frame ∙ (A₁ ⁻¹)) =₂ (b₁ ∙ L)
      right-normal = comp₌-cong (id₌ b₁) (comp-inv-right L A₁) ∙
        comp₌-assoc b₁ (L ∙ A₁) (A₁ ⁻¹)
      source-through-junction : (second-source ∙ M) =₂ middle-frame
      source-through-junction = cancel-right (A₁ ⁻¹) ((right-normal ⁻¹) ∙ left-normal)
      source-frame-square : second-source =₂
        (middle-frame ∙ ((pullback-match {f = tgt} {g = src} ⁻¹) ▷ q))
      source-frame-square = comp₌-cong (id₌ middle-frame)
          ((preWhisker-inverse (pullback-match {f = tgt} {g = src}) q) ⁻¹) ∙
        (comp₌-cong source-through-junction (id₌ (M ⁻¹)) ∙
          ((comp-inv-right second-source M) ⁻¹))

      module SecondRestriction = PairedRestrictionImage src tgt pullback₂ q edge₀ δ₂ a₂ b₂
      junction-pair = pair⁼ (pullback-match {f = tgt} {g = src} ⁻¹) (id₌ t₂)
      target-frame-square : (last-frame ∙ (id₌ t₂ ▷ q)) =₂ last-frame
      target-frame-square = comp₌-unitʳ-One last-frame ∙
        comp₌-cong (id₌ last-frame) (preWhisker-id₌ t₂ q)
      second-pair-image = paired-input-image
        (pullback-match {f = tgt} {g = src} ⁻¹) (id₌ t₂) q
        second-source middle-frame last-frame last-frame (source-frame-square ⁻¹) target-frame-square
      second-edge-square = comp₌-cong
          ((pair-action-image src tgt δ₂ a₂ b₂) ⁻¹)
          (id₌ (comp-assoc q pullback₂ (pair src tgt))) ∙
        (SecondRestriction.image ∙
          (comp₌-cong second-pair-image (id₌ (pair-pre src tgt pullback₂ ▷ q)) ∙
            ((comp₌-assoc second-pair (junction-pair ▷ q) (pair-pre src tgt pullback₂ ▷ q)) ⁻¹ ∙
              comp₌-cong (id₌ second-pair)
                (preWhisker-comp₌ junction-pair (pair-pre src tgt pullback₂) q))))

      module First = ProjectedEdgeImage baseP baseT pr₁ q pullback₁ edge₂ (pair src tgt)
        old-first new-first (pair-pre src tgt pullback₁) endpoint₁ base-cell δ₁ first-pair
        first-base-square first-edge-square
      old-middle : (middle-vertices ∘ baseP) =₁ pair t₁ t₂
      old-middle = pair⁼ Old.second Old.third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ baseP
      new-middle : (middle-vertices ∘ baseT) =₁ pair v₁ v₂
      new-middle = pair⁼ New.second New.third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ baseT
      module Second = ProjectedEdgeImage baseP baseT middle-vertices q pullback₂ edge₀ (pair src tgt)
        old-middle new-middle
        (junction-pair ∙ pair-pre src tgt pullback₂) endpoint₂ base-cell δ₂ second-pair
        MiddlePair.image second-edge-square

    first : IdentificationOver {A = One}
      (comp-over-map pr₁ (first-projection-over C) (short-edges-over C)) (first-edge-over C)
    first = identification-over δ₁ (compatible-to-over First.compatible)

    second : IdentificationOver {A = One}
      (comp-over-map middle-vertices (second-projection-over C) (short-edges-over C)) (second-edge-over C)
    second = identification-over δ₂ (compatible-to-over Second.compatible)

module _ {Γ : Context} where
  first-relative-image : (C : CAT Γ) → IdentificationOver {A = One}
    (comp-over-map pr₁ (first-projection-over C) (short-edges-over C)) (first-edge-over C)
  first-relative-image = ActualShortEdgeImages.first

  second-relative-image : (C : CAT Γ) → IdentificationOver {A = One}
    (comp-over-map middle-vertices (second-projection-over C) (short-edges-over C)) (second-edge-over C)
  second-relative-image = ActualShortEdgeImages.second
```

The underlying first and second identifications are literally the two
components of short-edges-image. Their complete base compatibility is
proved here. No new assumption, Segal hypothesis or higher equality of
relative records is used.
