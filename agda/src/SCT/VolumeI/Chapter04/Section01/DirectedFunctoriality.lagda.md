# Functoriality of directed pullbacks

The functor in the second part of `cons:Directed_Pullback` is induced
by a map of the defining cospans. Both given commutativity identifications
enter this map. Its computation rule compares the entire pullback cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.DirectedFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedPullbacks 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)

module Change {A B C A′ B′ C′ : CAT}
  (f : MAP A C) (g : MAP B C) (f′ : MAP A′ C′) (g′ : MAP B′ C′)
  (α : MAP A A′) (β : MAP B B′) (γ : MAP C C′)
  (p : (f′ ∘ α) =₁ (γ ∘ f)) (q : (g′ ∘ β) =₁ (γ ∘ g)) where
  module Source = DirectedPullback f g
  module Target = DirectedPullback f′ g′

  cospan : CospanMap endpoints (productMap f g) endpoints (productMap f′ g′)
  cospan = record
    { left = funPost γ ; right = productMap α β ; base = productMap γ γ
    ; leftSquare = (productMap-pair γ γ ev₀ ev₁) ⁻¹ ∙
        (pair-cong (evaluate-post zero γ) (evaluate-post one γ) ∙
          pair-pre ev₀ ev₁ (funPost γ))
    ; rightSquare = (productMap-comp f γ g γ) ⁻¹ ∙
        (productMap-cong p q ∙ productMap-comp α f′ β g′) }

  map : MAP Source.category Target.category
  map = CospanMap.pullbackMap cospan

  map-β : ConeIso
    (conePre map (pullbackCone endpoints (productMap f′ g′)))
    (CospanMap.mapCone cospan (pullbackCone endpoints (productMap f g)))
  map-β = CospanMap.pullbackMap-β cospan
```

