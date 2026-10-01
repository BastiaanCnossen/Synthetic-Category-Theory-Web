# Functors between coslices

A functor together with an identification of the chosen source objects
induces a functor of coslices. Its construction uses the one-sided
endpoint pullbacks and retains the full comparison there. Evaluating the
other endpoint gives the displayed comparison of target projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.CosliceFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (ConeIso; conePre; module UniversalCone)

module At {C D : CAT} (F : MAP C D) (x : Obj-abs C) (y : Obj-abs D)
  (α : (F ∘ x) =₁ y) where
  private
    module Source = CosliceEndpoint x using (square)
    module Target = CosliceEndpoint y using (square; square-isPullback)
    module Universal = UniversalCone Target.square Target.square-isPullback
      using (factor; factor-β)
    module X = EndpointFiber (const x) (id C)
    module Y = EndpointFiber (const y) (id D)

  cospan : CospanMap (ev₀ {C}) x (ev₀ {D}) y
  cospan = record
    { left = funPost F ; right = id One ; base = F
    ; leftSquare = evaluate-post zero F
    ; rightSquare = α ⁻¹ ∙ comp-unitʳ y }

  image = CospanMap.mapCone cospan Source.square

  functor : MAP (Coslice C x) (Coslice D y)
  functor = Universal.factor image

  computation : ConeIso (conePre functor Target.square) image
  computation = Universal.factor-β image

  arrow-comparison : (Y.arrow ∘ functor) =₁ (funPost F ∘ X.arrow)
  arrow-comparison = ConeIso.leftIso computation

  projection : (coslice-projection y ∘ functor) =₁ (F ∘ coslice-projection x)
  projection = (F ◁ (comp-unitˡ X.base ∙ X.target-frame)) ∙
    (evaluate-post-at one F X.arrow ∙
    ((ev₁ ◁ arrow-comparison) ∙
    (comp-assoc functor Y.arrow ev₁ ∙
      ((comp-unitˡ Y.base ∙ Y.target-frame) ⁻¹ ▷ functor))))

module Image {C D : CAT} (F : MAP C D) (x : Obj-abs C) =
  At F x (F ∘ x) (idIso (F ∘ x))
```
