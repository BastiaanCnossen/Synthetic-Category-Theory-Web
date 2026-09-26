# Parameters commute with pullback pasting

The pasting equivalence between nested pullbacks also compares their
parameter cones. The product comparison determines the left leg. The
right leg is the triangle of that same pasting equivalence after
adjoining a parameter, followed by the source associator.

To verify the matching, project the left leg. Both projected cones then
compare to the original pasted cone restricted along the parameter
projection. Product projection computations recover the prescribed left
comparison, while the right computation retains its specified triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductComparisonProjections as Products
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter03.Section05.Currying.ParameterizedPullbackPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc; coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
  using (module PasteCones; compositeCone; compositeCone-pre; compositeCone-compatible)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (restriction-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones 𝒯 using (module Parameter)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositePasting 𝒯 using (module Pasting)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module Pasted {S T S′ T′ K : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (k : MAP K T′) (X : CAT) where
  h = Cone.left square
  p′ = Cone.right square
  module Nest = Nested k b p (coneSwap square) (pullback-swap square square-isPullback)
  N = Nest.N
  O = Nest.Outer
  e = Nest.flatten
  lN : MAP N K
  lN = pullback₁
  rN : MAP N S′
  rN = pullback₂
  lO : MAP O K
  lO = pullback₁
  rO : MAP O S
  rO = pullback₂
  πN : MAP (X × N) N
  πN = pr₂
  πO : MAP (X × O) O
  πO = pr₂
  πK : MAP (X × K) K
  πK = pr₂
  H = productMap (id X) e
  module PN = Parameter X (pullbackCone k p′)
  module PO = Parameter X (pullbackCone (b ∘ k) p)
  module Paste = PasteCones k b (coneSwap square)
  module Product = Products.Normalized 𝒯 (id X) (id X) e lO (comp-unitˡ (id X)) Nest.α
  A = comp-assoc πK k b
  target = conePre H PO.cone
  source = changeLeft (A ⁻¹) (PasteCones.flatten (k ∘ πK) b (coneSwap square) PN.cone)
  left = Product.value
  flatten-over : FunctorOver (h ∘ rN) rO
  flatten-over = record { lift = e ; comparison = Nest.β }
  module Arg = Argument flatten-over
  right = comp-assoc πN rN h ∙ FunctorLift.comparison (Arg.family X)

  outer₁ = coneIso-inverse (compositeCone-pre πK (b ∘ k) H PO.cone)
  outer₂ = coneIso-compose (coneIso-pre H PO.projection) outer₁
  outer₃ = coneIso-compose (conePre-assoc H πO (pullbackCone (b ∘ k) p)) outer₂
  outer₄ = coneIso-compose (cone-action (pullbackCone (b ∘ k) p) (restriction-base X e)) outer₃
  outer₅ = coneIso-compose (coneIso-inverse (conePre-assoc πN e (pullbackCone (b ∘ k) p))) outer₄
  outer = coneIso-compose (coneIso-pre πN (pullbackLift-β Nest.flatCone)) outer₅

  inner₁ = Pasting.comparison πK k b (coneSwap square) PN.cone
  inner₂ = coneIso-compose (Paste.flatten-iso PN.projection) inner₁
  inner = coneIso-compose (coneIso-inverse (Paste.flatten-pre πN (pullbackCone k p′))) inner₂
  projected = coneIso-compose (coneIso-inverse inner) outer

  private
    C = comp-assoc πN e lO
    D = comp-assoc H πO lO
    βH = restriction-base X e
    tail = (PO.β ▷ H) ∙ (comp-assoc H PO.R πK) ⁻¹
    γ = Nest.α ▷ πN
    θ = FunctorLift.comparison (Arg.family X)
    R = comp-assoc H πO rO
    J = comp-assoc πN rN h
    ε = (idIso (rO ∘ πO) ▷ H) ∙ (idIso ((rO ∘ πO) ∘ H)) ⁻¹

  abstract
    outer-left : ConeIso.leftIso outer =₂ (PN.β ∙ (πK ◁ left))
    outer-left = Product.projection₂ ⁻¹ ∙
      ((isoComp-assoc-at γ ((C ⁻¹) ∙ ((lO ◁ βH) ∙ D)) tail) ⁻¹ ∙
        (isoComp-cong (idIso γ) ((isoComp-assoc-at (C ⁻¹) ((lO ◁ βH) ∙ D) tail) ⁻¹) ∙
          isoComp-cong (idIso γ) (isoComp-cong (idIso (C ⁻¹)) ((isoComp-assoc-at (lO ◁ βH) D tail) ⁻¹))))

    inner-left : ConeIso.leftIso inner =₂ PN.β
    inner-left = isoComp-unitʳ-at PN.β ∙
      (isoComp-unitˡ-at (PN.β ∙ idIso (πK ∘ PN.R)) ∙
        isoComp-cong (inverse-identity (lN ∘ πN)) (idIso (PN.β ∙ idIso (πK ∘ PN.R))))

    left-image : ConeIso.leftIso projected =₂ (πK ◁ left)
    left-image = cancel-left PN.β (πK ◁ left) ∙
      isoComp-cong (＝-inv ◁ inner-left) outer-left

    units : ε =₂ idIso ((rO ∘ πO) ∘ H)
    units = isoComp-unitˡ-at (idIso ((rO ∘ πO) ∘ H)) ∙
      isoComp-cong (preWhisker-idIso (rO ∘ πO) H) (inverse-identity ((rO ∘ πO) ∘ H))

    outer-right : ConeIso.rightIso outer =₂ θ
    outer-right = isoComp-cong (idIso (Nest.β ▷ πN))
      (isoComp-cong (idIso ((comp-assoc πN e rO) ⁻¹))
        (isoComp-cong (idIso (rO ◁ βH))
          (isoComp-unitʳ-at R ∙ isoComp-cong (idIso R) units)))

    inner-right : ConeIso.rightIso inner =₂ (J ⁻¹)
    inner-right = isoComp-unitʳ-at (J ⁻¹) ∙
      isoComp-cong (idIso (J ⁻¹))
        (isoComp-unitˡ-at (idIso (h ∘ (rN ∘ πN))) ∙
          isoComp-cong (postWhisker-idIso h (rN ∘ πN)) (idIso (idIso (h ∘ (rN ∘ πN)))))

    right-image : ConeIso.rightIso projected =₂ right
    right-image = isoComp-cong (inverse-inverse J ∙ (＝-inv ◁ inner-right)) outer-right

  adjusted = coneIso-adjust projected (πK ◁ left) right left-image right-image
  comparison : ConeIso target source
  comparison = compositeCone-compatible πK (b ∘ k) target source left right (ConeIso.compatible adjusted)
```
