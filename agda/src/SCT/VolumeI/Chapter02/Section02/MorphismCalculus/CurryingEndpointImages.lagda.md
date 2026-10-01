# Uncurried images of the chosen currying frames

The retained image of a reflected endpoint can be simplified by cancelling
its final parameter-restriction comparison. This gives a useful normalized
form of the endpoint chosen by currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingEndpointImages
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {Γ X C : CAT} (f g : MAP Γ (Fun X C))
  (α : MorphismExpression (funUncurry f) (funUncurry g)) where
  module A = Currying.Curry 𝒯 M ℱ I f g α
    using (diagram; first-curry; original; permutation; module Endpoint)
  module Original = MorphismExpression α
    using (arrow)
  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (b : (evaluate z ∘ Original.arrow) =₁ funUncurry h) where
    module New = A.Endpoint z h b
      using (insertion-comparison; raw; reflected; reflected-image)
    i = insert {X = Γ} z
    s = productMap i (id X)
    ρ : funUncurry (A.first-curry ∘ i) =₁ (funUncurry A.first-curry ∘ s)
    ρ = funUncurry-restrict A.first-curry i
    front : (A.original ∘ insert z) =₁ funUncurry h
    front = b ∙ (evaluate-uncurry z Original.arrow) ⁻¹
    insertion : (A.original ∘ (A.permutation ∘ s)) =₁ (A.original ∘ insert z)
    insertion = A.original ◁ New.insertion-comparison
    associator = comp-assoc s A.permutation A.original
    B : (funUncurry A.first-curry ∘ s) =₁ (A.diagram ∘ s)
    B = funCurry-β A.diagram ▷ s
    output : (funUncurry A.first-curry ∘ s) =₁ funUncurry h
    output = (front ∙ (insertion ∙ associator)) ∙ B

    abstract
      raw-normalization : New.raw =₂ (output ∙ ρ)
      raw-normalization = (isoComp-assoc-at (front ∙ (insertion ∙ associator)) B ρ) ⁻¹ ∙
        (isoComp-assoc-at front (insertion ∙ associator) (B ∙ ρ)) ⁻¹ ∙
        isoComp-cong (idIso front) ((isoComp-assoc-at insertion associator (B ∙ ρ)) ⁻¹)

      comparison : (funUncurryIso New.reflected ∙ ρ ⁻¹) =₂ output
      comparison = cancel-right ρ output ∙
        isoComp-cong raw-normalization (idIso (ρ ⁻¹)) ∙
        isoComp-cong New.reflected-image (idIso (ρ ⁻¹))
```
