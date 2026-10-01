# Recognizing expressions in a product

The two projections jointly reflect an identification of morphism
expressions, including its source and target equations. The arrow
comparison is lifted through the functor-product equivalence with
both projected images prescribed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-boundary-normal; post-evaluation-natural)
import SCT.VolumeI.Chapter01.Section07.FunctorProducts as Products
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering using (substitution-square-projection)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
open PC vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ C D : CAT} {x y : MAP Γ (C × D)} (f g : MorphismExpression x y)
  (first : ExpressionIso (post-expression pr₁ f) (post-expression pr₁ g))
  (second : ExpressionIso (post-expression pr₂ f) (post-expression pr₂ g)) where
  module F = MorphismExpression f
    using (arrow; source-frame; target-frame)
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module A = ExpressionIso first
    using (comparison; source-compatible; target-compatible)
  module B = ExpressionIso second
  module Product = Products.ProductComparison 𝒯 M ℱ [1] C D
    using (forward; forward-isEquiv)
  h = F.arrow
  k = G.arrow
  l = Product.forward

  first-frame : (u : MAP Γ (Ar (C × D))) → (pr₁ ∘ (l ∘ u)) =₁ (funPost pr₁ ∘ u)
  first-frame u = (pair-β₁ (funPost pr₁) (funPost pr₂) ▷ u) ∙ (comp-assoc u l pr₁) ⁻¹
  second-frame : (u : MAP Γ (Ar (C × D))) → (pr₂ ∘ (l ∘ u)) =₁ (funPost pr₂ ∘ u)
  second-frame u = (pair-β₂ (funPost pr₁) (funPost pr₂) ▷ u) ∙ (comp-assoc u l pr₂) ⁻¹
  first-image = (first-frame k) ⁻¹ ∙ (A.comparison ∙ first-frame h)
  second-image = (second-frame k) ⁻¹ ∙ (B.comparison ∙ second-frame h)
  paired = pair-iso first-image second-image
  lifted = postWhisker-lift l Product.forward-isEquiv paired
  abstract
    comparison-arrow : h =₁ k
    comparison-arrow = FunctorLift.lift lifted
    image : (l ◁ comparison-arrow) =₂ paired
    image = FunctorLift.comparison lifted

  projection-image : {Y : CAT} (π : MAP (Ar C × Ar D) Y) (q : MAP (Ar (C × D)) Y)
    (b : (π ∘ l) =₁ q) (α : (q ∘ h) =₁ (q ∘ k)) →
    (π ◁ paired) =₂ (((b ▷ k) ∙ (comp-assoc k l π) ⁻¹) ⁻¹ ∙
      (α ∙ ((b ▷ h) ∙ (comp-assoc h l π) ⁻¹))) → (q ◁ comparison-arrow) =₂ α
  projection-image π q b α prescribed = cancel-right-reflect bh
    (cancel-inverse bk (α ∙ bh) ∙
      isoComp-cong (idIso bk) prescribed ∙
      isoComp-cong (idIso bk) (postWhisker π ◁ image) ∙
      (substitution-square-projection π l q b comparison-arrow) ⁻¹)
    where
    bh = (b ▷ h) ∙ (comp-assoc h l π) ⁻¹
    bk = (b ▷ k) ∙ (comp-assoc k l π) ⁻¹

  first-prescribed : (funPost pr₁ ◁ comparison-arrow) =₂ A.comparison
  first-prescribed = projection-image pr₁ (funPost pr₁) (pair-β₁ (funPost pr₁) (funPost pr₂))
    A.comparison (pair-iso-β₁ first-image second-image)
  second-prescribed : (funPost pr₂ ◁ comparison-arrow) =₂ B.comparison
  second-prescribed = projection-image pr₂ (funPost pr₂) (pair-β₂ (funPost pr₁) (funPost pr₂))
    B.comparison (pair-iso-β₂ first-image second-image)

  module Endpoint {Y : CAT} (π : MAP (C × D) Y) (v : Obj-abs [1]) {z : MAP Γ (C × D)}
    (p : (evaluate v ∘ h) =₁ z) (q : (evaluate v ∘ k) =₁ z)
    (α : (funPost π ∘ h) =₁ (funPost π ∘ k))
    (prescribed : (funPost π ◁ comparison-arrow) =₂ α)
    (same : (post-boundary v π k q ∙ (evaluate v ◁ α)) =₂ post-boundary v π h p) where
    Rh = evaluate-post-at v π h
    Rk = evaluate-post-at v π k
    δ = evaluate v ◁ comparison-arrow
    d = evaluate v ◁ (funPost π ◁ comparison-arrow)
    abstract
      normalized : (((π ◁ q) ∙ Rk) ∙ d) =₂ ((π ◁ p) ∙ Rh)
      normalized = post-boundary-normal v π h p ∙ same ∙
        isoComp-cong (idIso (post-boundary v π k q)) (postWhisker (evaluate v) ◁ prescribed) ∙
        isoComp-cong ((post-boundary-normal v π k q) ⁻¹) (idIso d)
      compatible : (π ◁ (q ∙ δ)) =₂ (π ◁ p)
      compatible = cancel-right-reflect Rh
        (normalized ∙ (isoComp-assoc-at (π ◁ q) Rk d) ⁻¹ ∙
          isoComp-cong (idIso (π ◁ q)) ((post-evaluation-natural v π comparison-arrow) ⁻¹) ∙
          isoComp-assoc-at (π ◁ q) (π ◁ δ) Rh) ∙
        postWhisker-isoComp-at π q δ

  comparison : ExpressionIso f g
  comparison = record { comparison = comparison-arrow
    ; source-compatible = pair-iso-extensionality
        (Endpoint.compatible pr₁ zero F.source-frame G.source-frame A.comparison first-prescribed A.source-compatible)
        (Endpoint.compatible pr₂ zero F.source-frame G.source-frame B.comparison second-prescribed B.source-compatible)
    ; target-compatible = pair-iso-extensionality
        (Endpoint.compatible pr₁ one F.target-frame G.target-frame A.comparison first-prescribed A.target-compatible)
        (Endpoint.compatible pr₂ one F.target-frame G.target-frame B.comparison second-prescribed B.target-compatible) }

product-expression-reflect : {Γ C D : CAT} {x y : MAP Γ (C × D)}
  {f g : MorphismExpression x y} →
  ExpressionIso (post-expression pr₁ f) (post-expression pr₁ g) →
  ExpressionIso (post-expression pr₂ f) (post-expression pr₂ g) → ExpressionIso f g
product-expression-reflect {f = f} {g} = At.comparison f g
```
