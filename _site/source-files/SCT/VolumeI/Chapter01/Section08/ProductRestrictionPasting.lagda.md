# Product restriction preserves specified square pasting

The comparisons use the existing normalized compositor of `X × -`.
Naturality and associativity are assembled for the five factors of the
specified outer matching; no extra coherence assumption is introduced.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ProductRestrictionPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 using (Cocone; CoconeIso)
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯
  using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconePasting 𝒯 using (module PasteCocones)
open import SCT.VolumeI.Chapter01.Section08.CoconePastingPostcomposition 𝒯 M
  using (module PastedPostcomposition)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 using (coconeIso-compose)
open import SCT.VolumeI.Chapter01.Section08.PrecompositionCongruence 𝒯 M
  using (product-comparison-square; identity-source-square)
open import SCT.VolumeI.Chapter01.Section08.ProductRestrictionAssociativity 𝒯 M
  using (restriction-assoc)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-left; cancel-right; cancel-left-reflect)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

module Action (X : CAT) where
  I = id X
  i = idIso I
  λI = comp-unitˡ I
  L = productRestriction X
  κ = productRestriction-comp X
  R : {A B : CAT} {f g : MAP A B} → f =₁ g → (L f) =₁ (L g)
  R α = productMap-cong i α

  R₂ : {A B : CAT} {f g : MAP A B} {α β : f =₁ g} → α =₂ β → (R α) =₂ (R β)
  R₂ p = productMap-cong-Iso₂ (idIso i) p

  R-comp : {A B : CAT} {f g h : MAP A B} (β : g =₁ h) (α : f =₁ g) →
    (R (β ∙ α)) =₂ (R β ∙ R α)
  R-comp β α = productMap-cong-comp i i β α ∙
    productMap-cong-Iso₂ ((isoComp-unitˡ-at i) ⁻¹) (idIso (β ∙ α))

  R-id : {A B : CAT} (f : MAP A B) → (R (idIso f)) =₂ (idIso (L f))
  R-id f = productMap-cong-id I f

  R-inverse : {A B : CAT} {f g : MAP A B} (α : f =₁ g) →
    (R (α ⁻¹)) =₂ ((R α) ⁻¹)
  R-inverse {f = f} α = cancel-right-reflect (R α)
    ((isoComp-inverseˡ-at (R α)) ⁻¹ ∙
      (R-id f ∙ (R₂ (isoComp-inverseˡ-at α) ∙ (R-comp (α ⁻¹) α) ⁻¹)))

  normalization-square : {A B : CAT} {f g : MAP A B} (α : f =₁ g)
    (u : (I ∘ I) =₁ (I ∘ I)) → u =₂ (idIso (I ∘ I)) →
    (productMap-cong λI (idIso g) ∙ productMap-cong u α) =₂
      (R α ∙ productMap-cong λI (idIso f))
  normalization-square {f = f} {g} α u p = product-comparison-square
    λI λI (idIso f) (idIso g) u i α α
    (identity-source-square λI u p)
    ((isoComp-unitʳ-at α) ⁻¹ ∙ isoComp-unitˡ-at α)

  outer-natural : {A B C : CAT} (f : MAP A B) {g h : MAP B C} (α : g =₁ h) →
    (κ f h ∙ (R α ▷ L f)) =₂ (R (α ▷ f) ∙ κ f g)
  outer-natural f {g} {h} α = paste-squares
    (productMap-comp I I f g) (productMap-comp I I f h)
    (productMap-cong λI (idIso (g ∘ f))) (productMap-cong λI (idIso (h ∘ f)))
    (R α ▷ L f) (productMap-cong (i ▷ I) (α ▷ f)) (R (α ▷ f))
    (productMap-comp-natural-outer I f i α)
    (normalization-square (α ▷ f) (i ▷ I) (preWhisker-idIso I I))

  inner-natural : {A B C : CAT} {f g : MAP A B} (α : f =₁ g) (h : MAP B C) →
    (κ g h ∙ (L h ◁ R α)) =₂ (R (h ◁ α) ∙ κ f h)
  inner-natural {f = f} {g} α h = paste-squares
    (productMap-comp I I f h) (productMap-comp I I g h)
    (productMap-cong λI (idIso (h ∘ f))) (productMap-cong λI (idIso (h ∘ g)))
    (L h ◁ R α) (productMap-cong (I ◁ i) (h ◁ α)) (R (h ◁ α))
    (productMap-comp-natural-inner i α I h)
    (normalization-square (h ◁ α) (I ◁ i) (postWhisker-idIso I I))

  image-square : {A B C D : CAT}
    {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
    Square u l r v → Square (L u) (L l) (L r) (L v)
  image-square s = record { commute = Cocone.match (productCocone X s) }

  triangle : {A B C D : CAT}
    {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
    (s : Square u l r v) →
    (κ l v ∙ Square.commute (image-square s)) =₂
      (R (Square.commute s) ∙ κ u r)
  triangle {u = u} {l} {r} {v} s = cancel-inverse (κ l v) (R (Square.commute s) ∙ κ u r)

  associativity : {A B C D : CAT} (f : MAP A B) (g : MAP B C) (h : MAP C D) →
    ((κ (g ∘ f) h ∙ (L h ◁ κ f g)) ∙ comp-assoc (L f) (L g) (L h)) =₂
    (R (comp-assoc f g h) ∙ (κ f (h ∘ g) ∙ (κ g h ▷ L f)))
  associativity f g h = restriction-assoc X h g f ∙
    isoComp-assoc-at (κ (g ∘ f) h) (L h ◁ κ f g) (comp-assoc (L f) (L g) (L h))

  inverse-assoc : {A B C D : CAT} (f : MAP A B) (g : MAP B C) (h : MAP C D) →
    ((κ f (h ∘ g) ∙ (κ g h ▷ L f)) ∙ (comp-assoc (L f) (L g) (L h)) ⁻¹) =₂
    (R ((comp-assoc f g h) ⁻¹) ∙ (κ (g ∘ f) h ∙ (L h ◁ κ f g)))
  inverse-assoc f g h = isoComp-cong ((R-inverse (comp-assoc f g h)) ⁻¹) (idIso _) ∙
    (move-square (R (comp-assoc f g h)) (κ f (h ∘ g) ∙ (κ g h ▷ L f))
      (κ (g ∘ f) h ∙ (L h ◁ κ f g)) (comp-assoc (L f) (L g) (L h))
      ((associativity f g h) ⁻¹)) ⁻¹

  module Pasting {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
    {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
    {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
    {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
    (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) where
    α = Square.commute left
    β = Square.commute right
    outer = PastedSquare.outer left right
    Ω = Square.commute outer
    α′ = Square.commute (image-square left)
    β′ = Square.commute (image-square right)
    pasted = Square.commute (PastedSquare.outer (image-square left) (image-square right))
    d₀ = (comp-assoc (L g₁) (L g₂) (L f₃)) ⁻¹
    d₁ = β′ ▷ L g₁
    d₂ = comp-assoc (L g₁) (L f₂) (L h₂)
    d₃ = L h₂ ◁ α′
    d₄ = (comp-assoc (L f₁) (L h₁) (L h₂)) ⁻¹
    a₀ = (comp-assoc g₁ g₂ f₃) ⁻¹
    a₁ = β ▷ g₁
    a₂ = comp-assoc g₁ f₂ h₂
    a₃ = h₂ ◁ α
    a₄ = (comp-assoc f₁ h₁ h₂) ⁻¹
    ρ₀ = κ (g₂ ∘ g₁) f₃ ∙ (L f₃ ◁ κ g₁ g₂)
    ρ₁ = κ g₁ (f₃ ∘ g₂) ∙ (κ g₂ f₃ ▷ L g₁)
    ρ₂ = κ g₁ (h₂ ∘ f₂) ∙ (κ f₂ h₂ ▷ L g₁)
    ρ₃ = κ (f₂ ∘ g₁) h₂ ∙ (L h₂ ◁ κ g₁ f₂)
    ρ₄ = κ (h₁ ∘ f₁) h₂ ∙ (L h₂ ◁ κ f₁ h₁)
    ρ₅ = κ f₁ (h₂ ∘ h₁) ∙ (κ h₁ h₂ ▷ L f₁)

    abstract
      step₀ : (ρ₁ ∙ d₀) =₂ (R a₀ ∙ ρ₀)
      step₀ = inverse-assoc g₁ g₂ f₃

      step₁ : (ρ₂ ∙ d₁) =₂ (R a₁ ∙ ρ₁)
      step₁ = paste-squares
        (κ g₂ f₃ ▷ L g₁) (κ f₂ h₂ ▷ L g₁)
        (κ g₁ (f₃ ∘ g₂)) (κ g₁ (h₂ ∘ f₂)) d₁ (R β ▷ L g₁) (R a₁)
        (preWhisker-isoComp-at (R β) (κ g₂ f₃) (L g₁) ∙
          ((preWhisker (L g₁) ◁ triangle right) ∙
            (preWhisker-isoComp-at (κ f₂ h₂) β′ (L g₁)) ⁻¹))
        (outer-natural g₁ β)

      step₂ : (ρ₃ ∙ d₂) =₂ (R a₂ ∙ ρ₂)
      step₂ = associativity g₁ f₂ h₂

      step₃ : (ρ₄ ∙ d₃) =₂ (R a₃ ∙ ρ₃)
      step₃ = paste-squares
        (L h₂ ◁ κ g₁ f₂) (L h₂ ◁ κ f₁ h₁)
        (κ (f₂ ∘ g₁) h₂) (κ (h₁ ∘ f₁) h₂) d₃ (L h₂ ◁ R α) (R a₃)
        (postWhisker-isoComp-at (L h₂) (R α) (κ g₁ f₂) ∙
          ((postWhisker (L h₂) ◁ triangle left) ∙
            (postWhisker-isoComp-at (L h₂) (κ f₁ h₁) α′) ⁻¹))
        (inner-natural α h₂)

      step₄ : (ρ₅ ∙ d₄) =₂ (R a₄ ∙ ρ₄)
      step₄ = inverse-assoc f₁ h₁ h₂

      expand : (R Ω) =₂ (R a₄ ∙ (R a₃ ∙ (R a₂ ∙ (R a₁ ∙ R a₀))))
      expand = isoComp-cong (idIso (R a₄))
        (isoComp-cong (idIso (R a₃))
          (isoComp-cong (idIso (R a₂)) (R-comp a₁ a₀) ∙ R-comp a₂ (a₁ ∙ a₀)) ∙
          R-comp a₃ (a₂ ∙ (a₁ ∙ a₀))) ∙ R-comp a₄ (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀)))

      whole : (R Ω ∙ ρ₀) =₂ (ρ₅ ∙ pasted)
      whole = paste-squares (d₃ ∙ (d₂ ∙ (d₁ ∙ d₀)))
        (R a₃ ∙ (R a₂ ∙ (R a₁ ∙ R a₀))) d₄ (R a₄) ρ₀ ρ₄ ρ₅
        (paste-squares (d₂ ∙ (d₁ ∙ d₀)) (R a₂ ∙ (R a₁ ∙ R a₀)) d₃ (R a₃) ρ₀ ρ₃ ρ₄
          (paste-squares (d₁ ∙ d₀) (R a₁ ∙ R a₀) d₂ (R a₂) ρ₀ ρ₂ ρ₃
            (paste-squares d₀ (R a₀) d₁ (R a₁) ρ₀ ρ₁ ρ₂ (step₀ ⁻¹) (step₁ ⁻¹))
            (step₂ ⁻¹)) (step₃ ⁻¹)) (step₄ ⁻¹) ∙ isoComp-cong expand (idIso ρ₀)

      matching :
        (Square.commute (image-square outer) ∙ (L f₃ ◁ κ g₁ g₂)) =₂
        ((κ h₁ h₂ ▷ L f₁) ∙ pasted)
      matching = cancel-left-reflect (κ f₁ (h₂ ∘ h₁))
        (isoComp-assoc-at (κ f₁ (h₂ ∘ h₁)) (κ h₁ h₂ ▷ L f₁) pasted ∙
        (whole ∙
        (isoComp-assoc-at (R Ω) (κ (g₂ ∘ g₁) f₃) (L f₃ ◁ κ g₁ g₂) ∙
        (isoComp-cong (triangle outer) (idIso (L f₃ ◁ κ g₁ g₂)) ∙
          (isoComp-assoc-at (κ f₁ (h₂ ∘ h₁)) (Square.commute (image-square outer))
            (L f₃ ◁ κ g₁ g₂)) ⁻¹))))

    -- Both cocones now have the same outer span. The first compositor
    -- changes the upper edge; the second is the right leg comparison.
    adjustedOuter : Cocone (L g₂ ∘ L g₁) (L f₁) (X × B₃)
    adjustedOuter = record
      { left = L f₃ ; right = L (h₂ ∘ h₁)
      ; match = Square.commute (image-square outer) ∙ (L f₃ ◁ κ g₁ g₂) }

    pastedCocone : Cocone (L g₂ ∘ L g₁) (L f₁) (X × B₃)
    pastedCocone = squareCocone (PastedSquare.outer (image-square left) (image-square right))

    comparison : CoconeIso pastedCocone adjustedOuter
    comparison = record
      { leftIso = idIso (L f₃) ; rightIso = κ h₁ h₂
      ; compatible = matching ∙
          (isoComp-unitʳ-at (Cocone.match adjustedOuter) ∙
            isoComp-cong (idIso (Cocone.match adjustedOuter))
              (preWhisker-idIso (L f₃) (L g₂ ∘ L g₁))) }

    module Paste = PasteCocones (L g₁) (L g₂) (image-square left)

    postcomparison : {E : CAT} (z : MAP (X × B₃) E) →
      CoconeIso (Paste.flatten (coconePost z (productCocone X right)))
        (coconePost z adjustedOuter)
    postcomparison z = coconeIso-compose (coconeIso-post z comparison)
      (PastedPostcomposition.comparison (image-square left) (image-square right) z)
```
