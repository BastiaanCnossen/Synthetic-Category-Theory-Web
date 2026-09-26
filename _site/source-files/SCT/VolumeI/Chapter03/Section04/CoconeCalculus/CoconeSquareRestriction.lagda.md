# Comparing the cocones of a commutative cube

Four specified squares compare the two diagrams. Compatibility with
their full matching, expressed after restriction to the upper vertex,
then compares restriction of one cocone with postcomposition of the
other. No equality of the matchings is inferred from their boundaries.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSquareRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (transport-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Restriction)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module Cube {A B C A′ B′ C′ D D′ : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (s : Cocone u v D) (t : Cocone u′ v′ D′) (d : MAP D D′)
  (γ : (Cocone.left t ∘ j) =₁ (d ∘ Cocone.left s))
  (δ : (Cocone.right t ∘ k) =₁ (d ∘ Cocone.right s)) where
  module Restrict = Restriction u v u′ v′ i j k α β
  L = Restrict.Left.value (Cocone.left t)
  R = Restrict.Right.value (Cocone.right t)
  Ar = comp-assoc u (Cocone.left s) d
  Av = comp-assoc v (Cocone.right s) d
  σ = d ◁ Cocone.match s
  τ = Cocone.match t ▷ i
  left = Ar ∙ ((γ ▷ u) ∙ L ⁻¹)
  right = Av ∙ ((δ ▷ v) ∙ R ⁻¹)

  module Compatible (image : τ =₂ (right ⁻¹ ∙ (σ ∙ left))) where
    abstract
      middle : (σ ∙ left) =₂ (right ∙ τ)
      middle = isoComp-cong (idIso right) (image ⁻¹) ∙ (cancel-inverse right (σ ∙ left)) ⁻¹

      source-normal : (R ⁻¹ ∙ (τ ∙ (L ⁻¹) ⁻¹)) =₂ Cocone.match (Restrict.value t)
      source-normal = isoComp-cong (idIso (R ⁻¹)) (isoComp-cong (idIso τ) (inverse-inverse L))
      target-normal : (Av ⁻¹ ∙ (σ ∙ (Ar ⁻¹) ⁻¹)) =₂ Cocone.match (coconePost d s)
      target-normal = isoComp-cong (idIso (Av ⁻¹)) (isoComp-cong (idIso σ) (inverse-inverse Ar))

      matching : (Cocone.match (coconePost d s) ∙ (γ ▷ u)) =₂
        ((δ ▷ v) ∙ Cocone.match (Restrict.value t))
      matching = isoComp-cong (idIso (δ ▷ v)) source-normal ∙
        (transport-square (L ⁻¹) (Ar ⁻¹) (R ⁻¹) (Av ⁻¹) τ σ left right (γ ▷ u) (δ ▷ v)
          (cancel-left Ar ((γ ▷ u) ∙ L ⁻¹))
          (cancel-left Av ((δ ▷ v) ∙ R ⁻¹)) middle ∙
            isoComp-cong (target-normal ⁻¹) (idIso (γ ▷ u)))

    comparison : CoconeIso (Restrict.value t) (coconePost d s)
    comparison = record { leftIso = γ ; rightIso = δ ; compatible = matching }
```
