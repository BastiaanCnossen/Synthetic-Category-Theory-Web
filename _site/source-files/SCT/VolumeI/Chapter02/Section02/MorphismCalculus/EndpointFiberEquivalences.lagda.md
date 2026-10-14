# Changing the endpoint functors of an endpoint pullback

Identifications of the two endpoint functors induce an equivalence of
endpoint pullbacks. The cospan map uses identity maps on both legs and
the common codomain, and retains the chosen endpoint identifications.
Its projection comparison keeps the base functor fixed. The general
family-change construction accepts a specified identification into the
product, without requiring either family to be a literal paired functor.
The existing two-endpoint construction remains unchanged.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointFibers 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (ConeIso)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)

module ChangeFamily {B C : CAT} {a a′ : MAP B (C × C)} (θ : a =₁ a′) where
  change : CospanMap endpoints a endpoints a′
  change = record
    { left = id (Ar C) ; right = id B ; base = id (C × C)
    ; leftSquare = (comp-unitˡ endpoints) ⁻¹ ∙ comp-unitʳ endpoints
    ; rightSquare = (comp-unitˡ a) ⁻¹ ∙ (θ ⁻¹ ∙ comp-unitʳ a′) }

  open CospanMap change public using () renaming (pullbackMap to map; pullbackMap-β to map-β)

  map-isEquiv : IsEquiv map
  map-isEquiv = CospanEquivalence.pullbackMap-isEquiv change
    (id-isEquiv (Ar C)) (id-isEquiv B) (id-isEquiv (C × C))

  arrow-projection : (Laws.PullbackStructure.pullback₁ P {f = endpoints} {g = a′} ∘ map) =₁
    Laws.PullbackStructure.pullback₁ P {f = endpoints} {g = a}
  arrow-projection = comp-unitˡ _ ∙ ConeIso.leftIso map-β

  base-projection : (Laws.PullbackStructure.pullback₂ P {f = endpoints} {g = a′} ∘ map) =₁
    Laws.PullbackStructure.pullback₂ P {f = endpoints} {g = a}
  base-projection = comp-unitˡ _ ∙ ConeIso.rightIso map-β

module ChangeEndpoints {B C : CAT} {u v u′ v′ : MAP B C}
  (α : u =₁ u′) (β : v =₁ v′) where
  change : CospanMap endpoints (pair u v) endpoints (pair u′ v′)
  change = record
    { left = id (Ar C) ; right = id B ; base = id (C × C)
    ; leftSquare = (comp-unitˡ endpoints) ⁻¹ ∙ comp-unitʳ endpoints
    ; rightSquare = (comp-unitˡ (pair u v)) ⁻¹ ∙
        ((pair-cong α β) ⁻¹ ∙ comp-unitʳ (pair u′ v′)) }

  open CospanMap change renaming (pullbackMap to map; pullbackMap-β to map-β) public

  map-isEquiv : IsEquiv map
  map-isEquiv = CospanEquivalence.pullbackMap-isEquiv change
    (id-isEquiv (Ar C)) (id-isEquiv B) (id-isEquiv (C × C))

  projection : (EndpointFiber.base u′ v′ ∘ map) =₁ EndpointFiber.base u v
  projection = comp-unitˡ (EndpointFiber.base u v) ∙ ConeIso.rightIso map-β

  projection-isEquiv : IsEquiv (EndpointFiber.base u v) → IsEquiv (EndpointFiber.base u′ v′)
  projection-isEquiv e = equiv-cancel-right map (EndpointFiber.base u′ v′) map-isEquiv
    (equiv-transport (projection ⁻¹) e)

```
