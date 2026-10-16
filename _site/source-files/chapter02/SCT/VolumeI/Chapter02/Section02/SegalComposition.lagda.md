# The boundary of a chosen completion

The Segal construction uses the inverse of the triangle comparison. Its
complete short-edge comparison follows from the whole cone beta and the
chosen right inverse law. In particular, the junction matching is retained.
The base triangle and its compatibility are supplied separately by the
relative inverse laws.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SegalComposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)

private
  module _ {Γ : Context} {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E} where
    inverse-cone-comparison : (s : Cone f g T) (e : IsPullback s)
      → ConeIdentification₁
          (cone-restrict (IsEquiv.inverse e) s) (pullback-cone f g)
    inverse-cone-comparison s e =
      cone-compose (cone-restrict-id (pullback-cone f g))
        (cone-compose
          (cone-action-One (pullback-cone f g) ((IsEquiv.right-inverse-law e) ⁻¹))
          (cone-compose
            (cone-restrict-assoc (IsEquiv.inverse e) (pullback-factor s) (pullback-cone f g))
            (cone-inverse
              (cone-identification-restrict-One (IsEquiv.inverse e) (pullback-factor-β s)))))
```

The Segal equivalence chooses completion over all three vertices. Its
right and left laws retain the base triangles. Passing to the long edge
gives composition over the outer two vertices. A prescribed triangle is
compared with this completion from a supplied complete short-edge
comparison over the three vertices.

This construction takes the exact Segal equivalence as input. It does
not postulate that equivalence or derive it from weaker data.

```agda
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section09.RelativeInverseLaws

open import SCT.VolumeI.Chapter02.Section01.Triangles
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; ev₀; ev₁)

private
  module PrescribedTriangle {Γ : Context} {S : CAT Γ}
    {triangles pairs family : CategoryOverBase S}
    (q : FunctorOverBase triangles pairs)
    (e : IsEquiv (FunctorOverBase.functor q))
    (σ : FunctorOverBase family triangles)
    (p : FunctorOverBase family pairs)
    (given : IdentificationOver {A = One} (comp-over q σ) p) where

    completion : FunctorOverBase family triangles
    completion = comp-over (inverse-over q e) p

    short-edge-image : IdentificationOver {A = One}
      (comp-over q completion) (comp-over q σ)
    short-edge-image = comp-identification-over
      (inverse-identification-over given)
      (comp-identification-over
        (identification-over (comp-unitˡ (FunctorOverBase.functor p))
          (identification-over-unitˡ p))
        (comp-identification-over
          (identification-over
            (IdentificationOver.identification (RelativeInverse.right-law q e) ▷
              FunctorOverBase.functor p)
            (identification-over-pre p
              (IdentificationOver.over (RelativeInverse.right-law q e))))
          (inverse-identification-over
            (identification-over
              (comp-assoc (FunctorOverBase.functor p)
                (IsEquiv.inverse e) (FunctorOverBase.functor q))
              (identification-over-assoc q (inverse-over q e) p)))))

    module Comparison = RelativeCancellation q e completion σ short-edge-image

    triangle : IdentificationOver {A = One} completion σ
    triangle = Comparison.value

    image : (FunctorOverBase.functor q ◁ IdentificationOver.identification triangle)
      =₂ IdentificationOver.identification short-edge-image
    image = Comparison.image

  long-edge-cell-image : {Γ : Context} {S B : CAT Γ}
    (k : MAP S B) {X Y : CategoryOverBase S} {Z : CategoryOverBase B}
    (H : FunctorOverMap k Y Z) (F : FunctorOverBase X Y)
    → FunctorOverBase.cell (comp-over H (postcompose-over k F)) =₂
        FunctorOverBase.cell (comp-over-map k H F)
  long-edge-cell-image k {Y = Y} {Z} H F =
    comp₌-assoc (k ◁ FunctorOverBase.cell F)
      (comp-assoc (FunctorOverBase.functor F) (CategoryOverBase.map Y) k)
      ((FunctorOverBase.cell H ▷ FunctorOverBase.functor F) ∙
        (comp-assoc (FunctorOverBase.functor F)
          (FunctorOverBase.functor H) (CategoryOverBase.map Z)) ⁻¹)

  module LongEdgeComparison {Γ : Context} {S B : CAT Γ}
    (k : MAP S B) {triangles family : CategoryOverBase S}
    {arrows : CategoryOverBase B}
    (long-edge : FunctorOverMap k triangles arrows)
    {U V : FunctorOverBase family triangles}
    (α : IdentificationOver {A = One} U V) where

    private
      ordinary : (F : FunctorOverBase family triangles)
        → FunctorOverBase (postcompose-base k family) arrows
      ordinary F = comp-over long-edge (postcompose-over k F)

      cell-image : (F : FunctorOverBase family triangles)
        → FunctorOverBase.cell (ordinary F) =₂
            FunctorOverBase.cell (comp-over-map k long-edge F)
      cell-image = long-edge-cell-image k {X = family} long-edge

      ordinary-over : IsIdentificationOver (ordinary U) (ordinary V)
        (FunctorOverBase.functor long-edge ◁ IdentificationOver.identification α)
      ordinary-over = identification-over-post long-edge
        (identification-over-postcompose k (IdentificationOver.over α))

    value : IdentificationOver {A = One}
      (comp-over-map k long-edge U) (comp-over-map k long-edge V)
    value = identification-over
      (FunctorOverBase.functor long-edge ◁ IdentificationOver.identification α)
      (compatible-to-over
        (cell-image U ∙
          (over-to-compatible ordinary-over ∙
            comp₌-cong ((cell-image V) ⁻¹)
              (id₌ (CategoryOverBase.map arrows ◁
                (FunctorOverBase.functor long-edge ◁ IdentificationOver.identification α))))))


  module LongEdgeAssociation {Γ : Context} {S B : CAT Γ}
    (k : MAP S B) {X Y Z : CategoryOverBase S} {W : CategoryOverBase B}
    (H : FunctorOverMap k Z W) (G : FunctorOverBase Y Z)
    (F : FunctorOverBase X Y) where
    private
      f = FunctorOverBase.functor F
      g = FunctorOverBase.functor G
      h = FunctorOverBase.functor H
      π = CategoryOverBase.map W
      F′ = postcompose-over k F
      G′ = postcompose-over k G
      HG = comp-over-map k H G

      left-cell : FunctorOverBase.cell (comp-over (comp-over H G′) F′) =₂
        FunctorOverBase.cell (comp-over-map k HG F)
      left-cell = long-edge-cell-image k HG F ∙
        comp₌-cong (id₌ (FunctorOverBase.cell F′))
          (comp₌-cong (preWhisker f ◁ long-edge-cell-image k H G)
            (id₌ ((comp-assoc f (h ∘ g) π) ⁻¹)))

      right-cell : FunctorOverBase.cell (comp-over H (comp-over G′ F′)) =₂
        FunctorOverBase.cell (comp-over-map k H (comp-over G F))
      right-cell = long-edge-cell-image k H (comp-over G F) ∙
        comp₌-cong
          (postcompose-compose k (CategoryOverBase.map Z) g f
            (FunctorOverBase.cell G) (FunctorOverBase.cell F))
          (id₌ ((FunctorOverBase.cell H ▷ (g ∘ f)) ∙
            ((comp-assoc (g ∘ f) h π) ⁻¹)))

    value : IdentificationOver {A = One}
      (comp-over-map k (comp-over-map k H G) F)
      (comp-over-map k H (comp-over G F))
    value = identification-over (comp-assoc f g h)
      (compatible-to-over
        (left-cell ∙
          (over-to-compatible (identification-over-assoc H G′ F′) ∙
            comp₌-cong (right-cell ⁻¹) (id₌ (π ◁ comp-assoc f g h)))))

  module CompositionFromTriangle {Γ : Context} {S B : CAT Γ}
    (k : MAP S B) {triangles pairs family : CategoryOverBase S}
    {arrows : CategoryOverBase B}
    (long-edge : FunctorOverMap k triangles arrows)
    (q : FunctorOverBase triangles pairs)
    (e : IsEquiv (FunctorOverBase.functor q))
    (σ : FunctorOverBase family triangles)
    (p : FunctorOverBase family pairs)
    (given : IdentificationOver {A = One} (comp-over q σ) p) where

    private
      module Chosen = PrescribedTriangle q e σ p given

    value : IdentificationOver {A = One}
      (comp-over-map k (comp-over-map k long-edge (inverse-over q e)) p)
      (comp-over-map k long-edge σ)
    value = comp-identification-over
      (LongEdgeComparison.value k long-edge Chosen.triangle)
      (LongEdgeAssociation.value k long-edge (inverse-over q e) p)


module ChosenComposition {Γ : Context} (C : CAT Γ)
  (segal : IsEquiv (short-edges C)) where

  completion-over : FunctorOverBase (pairs-over C) (triangles-over C)
  completion-over = inverse-over (short-edges-over C) segal
  completion : MAP (Composable C) (Triangles C)
  completion = FunctorOverBase.functor completion-over

  completion-image : ConeIdentification₁
    (cone-restrict completion (triangle-cone C)) (pullback-cone (ev₁ {C = C}) ev₀)
  completion-image = inverse-cone-comparison (triangle-cone C) segal

  completion-right-law : IdentificationOver {A = One}
    (comp-over (short-edges-over C) completion-over) (id-over (pairs-over C))
  completion-right-law = RelativeInverse.right-law (short-edges-over C) segal
  completion-left-law : IdentificationOver {A = One}
    (comp-over completion-over (short-edges-over C)) (id-over (triangles-over C))
  completion-left-law = RelativeInverse.left-law (short-edges-over C) segal

  composition-over : FunctorOverMap outer-vertices (pairs-over C) (arrows-over C)
  composition-over = comp-over-map outer-vertices (long-edge-over C) completion-over
  composition : MAP (Composable C) (Ar C)
  composition = FunctorOverBase.functor composition-over

  module PresentedTriangle {family : CategoryOverBase (Vertices C)}
    (σ : FunctorOverBase family (triangles-over C))
    (p : FunctorOverBase family (pairs-over C))
    (given : IdentificationOver {A = One} (comp-over (short-edges-over C) σ) p) where

    private
      module Chosen = PrescribedTriangle (short-edges-over C) segal σ p given

    triangle : IdentificationOver {A = One} (comp-over completion-over p) σ
    triangle = Chosen.triangle

    short-edge-image : IdentificationOver {A = One}
      (comp-over (short-edges-over C) (comp-over completion-over p))
      (comp-over (short-edges-over C) σ)
    short-edge-image = Chosen.short-edge-image

    image : (short-edges C ◁ IdentificationOver.identification triangle)
      =₂ IdentificationOver.identification short-edge-image
    image = Chosen.image

    composite : IdentificationOver {A = One}
      (comp-over-map outer-vertices composition-over p)
      (comp-over-map outer-vertices (long-edge-over C) σ)
    composite = CompositionFromTriangle.value outer-vertices (long-edge-over C)
      (short-edges-over C) segal σ p given
```

The image law identifies the actual whiskered identification terms. Both
comparisons separately retain their complete base laws; no higher equality
of the entire relative records is inferred. Units and preservation of
composition must supply the complete relative short-edge comparison,
including its base compatibility, before using PresentedTriangle.
