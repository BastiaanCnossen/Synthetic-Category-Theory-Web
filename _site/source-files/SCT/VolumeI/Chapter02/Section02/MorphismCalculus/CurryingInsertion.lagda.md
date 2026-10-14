# An insertion comparison with prescribed coordinate images

The two coordinates used by evaluation form an equivalence. Lifting the
desired coordinate comparisons through it chooses the insertion witness
for currying. Its images are retained, so both endpoint calculations can
use those comparisons directly. This changes only a chosen witness, not
the underlying coordinate permutation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingInsertion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates as Coordinates
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.NestedSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering using (substitution-square-projection)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

module At (Γ X : CAT) where
  module Coordinate = Coordinates.Coordinates 𝒯 M ℱ I Γ X
  permutation = Coordinate.permutation
  first-coordinate : MAP ((Γ × X) × [1]) (Γ × [1])
  first-coordinate = Coordinate.step
  second-coordinate : MAP ((Γ × X) × [1]) X
  second-coordinate = Coordinate.fixed ∘ pr₁
  joint : MAP ((Γ × X) × [1]) ((Γ × [1]) × X)
  joint = pair first-coordinate second-coordinate

  joint-comparison : joint =₁ Symmetry.exchange 𝒯 {Γ} {X} {[1]}
  joint-comparison = pair-cong
    (pair-cong (idIso (pr₁ ∘ pr₁)) (comp-unitˡ pr₂))
    (comp-unitˡ pr₂ ▷ pr₁)
  joint-isEquiv : IsEquiv joint
  joint-isEquiv = equiv-transport (joint-comparison ⁻¹) (Symmetry.exchange-isEquiv 𝒯 Γ X [1])

  module Endpoint (z : Obj-abs [1]) where
    i = insert {X = Γ} z
    j = insert {X = Γ × X} z
    substitution = productMap i (id X)
    before = permutation ∘ substitution
    module Product = Substitution.Coordinates 𝒯 M X (id (Γ × [1])) i

    first-pasting : ((first-coordinate ∘ permutation) ∘ substitution) =₁ (first-coordinate ∘ j)
    first-pasting = insert-natural pr₁ z ∙
      (pair-β₁ (i ∘ pr₁) (id X ∘ pr₂) ∙ (Coordinate.step-comparison ▷ substitution))
    second-pasting : ((second-coordinate ∘ permutation) ∘ substitution) =₁ (second-coordinate ∘ j)
    second-pasting = (identity-boundary z Coordinate.fixed) ⁻¹ ∙
      (Product.second ∙ (Coordinate.second ▷ substitution))
    first-image = first-pasting ∙ (comp-assoc substitution permutation first-coordinate) ⁻¹
    second-image = second-pasting ∙ (comp-assoc substitution permutation second-coordinate) ⁻¹

    first-frame : (u : MAP (Γ × X) ((Γ × X) × [1])) → (pr₁ ∘ (joint ∘ u)) =₁ (first-coordinate ∘ u)
    first-frame u = (pair-β₁ first-coordinate second-coordinate ▷ u) ∙ (comp-assoc u joint pr₁) ⁻¹
    second-frame : (u : MAP (Γ × X) ((Γ × X) × [1])) → (pr₂ ∘ (joint ∘ u)) =₁ (second-coordinate ∘ u)
    second-frame u = (pair-β₂ first-coordinate second-coordinate ▷ u) ∙ (comp-assoc u joint pr₂) ⁻¹
    first-lift = (first-frame j) ⁻¹ ∙ (first-image ∙ first-frame before)
    second-lift = (second-frame j) ⁻¹ ∙ (second-image ∙ second-frame before)
    paired = pair-iso first-lift second-lift
    lifted = postWhisker-lift joint joint-isEquiv paired
    abstract
      comparison : before =₁ j
      comparison = FunctorLift.lift lifted
      comparison-image : (joint ◁ comparison) =₂ paired
      comparison-image = FunctorLift.comparison lifted

    projection-image : {Y : CAT} (π : MAP ((Γ × [1]) × X) Y) (q : MAP ((Γ × X) × [1]) Y)
      (b : (π ∘ joint) =₁ q) (α : (q ∘ before) =₁ (q ∘ j)) →
      (π ◁ paired) =₂ (((b ▷ j) ∙ (comp-assoc j joint π) ⁻¹) ⁻¹ ∙
        (α ∙ ((b ▷ before) ∙ (comp-assoc before joint π) ⁻¹))) →
      (q ◁ comparison) =₂ α
    projection-image π q b α prescribed = cancel-right-reflect bh
      (cancel-inverse bk (α ∙ bh) ∙ isoComp-cong (idIso bk) prescribed ∙
        isoComp-cong (idIso bk) (postWhisker π ◁ comparison-image) ∙
        (substitution-square-projection π joint q b comparison) ⁻¹)
      where
      bh = (b ▷ before) ∙ (comp-assoc before joint π) ⁻¹
      bk = (b ▷ j) ∙ (comp-assoc j joint π) ⁻¹

    abstract
      first-prescribed : (first-coordinate ◁ comparison) =₂ first-image
      first-prescribed = projection-image pr₁ first-coordinate (pair-β₁ first-coordinate second-coordinate)
        first-image (pair-iso-β₁ first-lift second-lift)
      second-prescribed : (second-coordinate ◁ comparison) =₂ second-image
      second-prescribed = projection-image pr₂ second-coordinate (pair-β₂ first-coordinate second-coordinate)
        second-image (pair-iso-β₂ first-lift second-lift)

      first-square : ((first-coordinate ◁ comparison) ∙ comp-assoc substitution permutation first-coordinate) =₂ first-pasting
      first-square = cancel-inverse-tail first-pasting (comp-assoc substitution permutation first-coordinate) ∙
        isoComp-cong first-prescribed (idIso (comp-assoc substitution permutation first-coordinate))
      second-square : ((second-coordinate ◁ comparison) ∙ comp-assoc substitution permutation second-coordinate) =₂ second-pasting
      second-square = cancel-inverse-tail second-pasting (comp-assoc substitution permutation second-coordinate) ∙
        isoComp-cong second-prescribed (idIso (comp-assoc substitution permutation second-coordinate))
```
