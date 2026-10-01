# Slices as one-sided endpoint pullbacks

The ordinary slices of Chapter 2 are pullbacks of target evaluation
along a point; coslices are pullbacks of source evaluation. The matching
is exactly the specified endpoint frame followed by constant substitution.
These absolute pullback presentations support the slice fibration theorem.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section06.Coordinates.PointProductSquares as Points

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; pullback-cone-invariant; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse)

module SliceEndpoint {C : CAT} (x : Obj-abs C) where
  module S = EndpointFiber (id C) (const x)
  module Graph = Points.Second 𝒯 P C x using (square; square-isPullback)
  module Paste = Pasting endpoints (pr₂ {C} {C}) x Graph.square Graph.square-isPullback
    using (module Paste; paste-isPullback)
  original = pullbackCone endpoints (pair (id C) (const x))
  pasted = Paste.Paste.flatten original
  normalized = changeLeft (pair-β₂ ev₀ ev₁) pasted

  square : Cone (ev₁ {C}) x (Slice C x)
  square = record { left = S.arrow ; right = terminate (Slice C x)
    ; match = const-pre x S.base ∙ S.target-frame }

  private
    q = S.base
    p = S.arrow
    A = comp-assoc q (terminate C) x
    U = project-pair₂ (id C) (const x) q
    δ = pr₂ ◁ pullbackMatch {f = endpoints} {g = pair (id C) (const x)}
    E = comp-assoc p endpoints pr₂
    t = pair-β₂ ev₀ ev₁ ▷ p
    r = terminal-iso (terminate C ∘ q) (terminate (Slice C x))

    abstract
      inverse-normal : ((t ∙ E ⁻¹) ⁻¹) =₂ (E ∙ t ⁻¹)
      inverse-normal = isoComp-cong (inverse-inverse E) (idIso (t ⁻¹)) ∙
        inverse-composite t (E ⁻¹)

      matching-normal : (Cone.match normalized) =₂ (A ∙ S.target-frame)
      matching-normal = isoComp-cong (idIso A)
        (isoComp-cong (idIso U)
          (isoComp-cong (idIso δ) (inverse-normal ⁻¹) ∙ isoComp-assoc-at δ E (t ⁻¹)) ∙
          isoComp-assoc-at U (δ ∙ E) (t ⁻¹)) ∙
        (isoComp-assoc-at A (U ∙ (δ ∙ E)) (t ⁻¹) ∙
          isoComp-cong (isoComp-assoc-at A U (δ ∙ E)) (idIso (t ⁻¹)))

  comparison : ConeIso normalized square
  comparison = record { leftIso = idIso S.arrow ; rightIso = r
    ; compatible = isoComp-cong (idIso (x ◁ r)) (matching-normal ⁻¹) ∙
        (isoComp-assoc-at (x ◁ r) A S.target-frame ∙
          (isoComp-unitʳ-at (Cone.match square) ∙
            isoComp-cong (idIso (Cone.match square)) (postWhisker-idIso ev₁ S.arrow))) }

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant comparison
    (ChangeLeft.preserve (pair-β₂ ev₀ ev₁) x pasted
      (Paste.paste-isPullback original
        (pullbackCone-isPullback endpoints (pair (id C) (const x)))))
module CosliceEndpoint {C : CAT} (x : Obj-abs C) where
  module S = EndpointFiber (const x) (id C)
  module Graph = Points.First 𝒯 P x C using (square; square-isPullback)
  module Paste = Pasting endpoints (pr₁ {C} {C}) x Graph.square Graph.square-isPullback
    using (module Paste; paste-isPullback)
  original = pullbackCone endpoints (pair (const x) (id C))
  pasted = Paste.Paste.flatten original
  normalized = changeLeft (pair-β₁ ev₀ ev₁) pasted

  square : Cone (ev₀ {C}) x (Coslice C x)
  square = record { left = S.arrow ; right = terminate (Coslice C x)
    ; match = const-pre x S.base ∙ S.source-frame }

  private
    q = S.base
    p = S.arrow
    A = comp-assoc q (terminate C) x
    U = project-pair₁ (const x) (id C) q
    δ = pr₁ ◁ pullbackMatch {f = endpoints} {g = pair (const x) (id C)}
    E = comp-assoc p endpoints pr₁
    t = pair-β₁ ev₀ ev₁ ▷ p
    r = terminal-iso (terminate C ∘ q) (terminate (Coslice C x))

    abstract
      inverse-normal : ((t ∙ E ⁻¹) ⁻¹) =₂ (E ∙ t ⁻¹)
      inverse-normal = isoComp-cong (inverse-inverse E) (idIso (t ⁻¹)) ∙
        inverse-composite t (E ⁻¹)

      matching-normal : (Cone.match normalized) =₂ (A ∙ S.source-frame)
      matching-normal = isoComp-cong (idIso A)
        (isoComp-cong (idIso U)
          (isoComp-cong (idIso δ) (inverse-normal ⁻¹) ∙ isoComp-assoc-at δ E (t ⁻¹)) ∙
          isoComp-assoc-at U (δ ∙ E) (t ⁻¹)) ∙
        (isoComp-assoc-at A (U ∙ (δ ∙ E)) (t ⁻¹) ∙
          isoComp-cong (isoComp-assoc-at A U (δ ∙ E)) (idIso (t ⁻¹)))

  comparison : ConeIso normalized square
  comparison = record { leftIso = idIso S.arrow ; rightIso = r
    ; compatible = isoComp-cong (idIso (x ◁ r)) (matching-normal ⁻¹) ∙
        (isoComp-assoc-at (x ◁ r) A S.source-frame ∙
          (isoComp-unitʳ-at (Cone.match square) ∙
            isoComp-cong (idIso (Cone.match square)) (postWhisker-idIso ev₀ S.arrow))) }

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant comparison
    (ChangeLeft.preserve (pair-β₁ ev₀ ev₁) x pasted
      (Paste.paste-isPullback original
        (pullbackCone-isPullback endpoints (pair (const x) (id C)))))
```
