# Restricting a composite coordinate

The nested coordinate comparison commutes with associating the two outer
functors. Its square is the ordinary pentagon and whiskering naturality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionCompositeCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionChange as Change
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.NestedCoordinateNaturality as Coordinate

module At {A B C D : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) (h : MAP C D) where
  J : MAP (X × A) (X × B)
  J = productMap (id X) f
  β : (pr₂ ∘ J) =₁ (f ∘ pr₂)
  β = pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)
  θ = comp-assoc (pr₂ {X} {B}) g h
  κ = comp-assoc (f ∘ pr₂ {X} {A}) g h
  image-frame = h ◁ (g ◁ β)
  inner-assoc = h ◁ comp-assoc J pr₂ g
  c′ = comp-assoc J (g ∘ pr₂) h
  outer-assoc = comp-assoc J pr₂ (h ∘ g)
  σ : ((h ∘ (g ∘ pr₂)) ∘ J) =₁ (h ∘ (g ∘ (f ∘ pr₂)))
  σ = (h ◁ ((g ◁ β) ∙ comp-assoc J pr₂ g)) ∙ c′
  module Changed = Change.At 𝒯 M X f (h ∘ g) θ κ σ
  module Natural = Coordinate.At 𝒯 J pr₂ β g h

  abstract
    nested : σ =₂ (image-frame ∙ (inner-assoc ∙ c′))
    nested = Natural.normalization

    square : (σ ∙ (θ ▷ J)) =₂ (κ ∙ Changed.N.second)
    square = Natural.nested-square

    value : (Changed.normal ∙ (Changed.change ▷ J)) =₂
      (Changed.δ ∙ productRestriction-comp X f (h ∘ g))
    value = Changed.value square
```
