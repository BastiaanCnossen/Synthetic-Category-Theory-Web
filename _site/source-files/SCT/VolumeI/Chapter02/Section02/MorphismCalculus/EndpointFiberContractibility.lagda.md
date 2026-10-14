# Recognizing a universal endpoint family

A universal expression over the base, together with uniqueness of
expressions on arbitrary parameter categories, makes the endpoint
projection an equivalence. The inverse is the functor classified by the
universal expression. Its other inverse equation follows by applying
uniqueness to the entire endpoint pullback as parameter category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberContractibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts 𝒯 M ℱ P I public
open Laws.PullbackStructure P

module Recognition {B C : CAT} (u v : MAP B C) (universal : MorphismExpression u v)
  (unique : {Γ : CAT} (b : MAP Γ B)
    (f g : MorphismExpression (u ∘ b) (v ∘ b)) → ExpressionIso f g) where
  private
    module H = EndpointFiber u v
    module F = Fiber u v using (decode)
    module L = Lifts u v using (restrict; lift-restrict; lift-change; lift-universal)

    unit-expression : MorphismExpression (u ∘ id B) (v ∘ id B)
    unit-expression = retarget-expression universal ((comp-unitʳ u) ⁻¹) ((comp-unitʳ v) ⁻¹)

  section : MAP B H.category
  section = H.lift (id B) unit-expression

  abstract
    section-base : (H.base ∘ section) =₁ id B
    section-base = H.lift-base (id B) unit-expression

    section-projection : (section ∘ H.base) =₁ id H.category
    section-projection = L.lift-universal ∙
      L.lift-change (L.restrict (id B) unit-expression H.base)
        (F.decode (pullbackCone endpoints (pair u v))) (comp-unitˡ H.base)
        (unique H.base _ _) ∙ L.lift-restrict (id B) unit-expression H.base

  projection-isEquiv : IsEquiv H.base
  projection-isEquiv = record
    { inverse = section ; sectionIso = section-projection ⁻¹ ; retractionIso = section-base ⁻¹ }
```
