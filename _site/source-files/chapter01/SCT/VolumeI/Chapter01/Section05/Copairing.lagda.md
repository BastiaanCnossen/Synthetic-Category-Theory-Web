# Copairing functors

The inverse of coproduct restriction combines two mapping-anima-valued
terms with any common parameter. Its factorization triangle computes the
whole pair of restrictions. Naming two structural functors and decoding
their copair then gives the chosen external copair, with both beta triangles.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section05.Copairing where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus using (pair₌; project-pair₁; project-pair₂)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (factor-through-postWhisker)
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points
  using (name; decode; name-decode; name⁼; name-reflect)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre-name)
open import SCT.VolumeI.Chapter01.Section05.Coproducts

module _ {Γ : Context} where
  copairing : (C D E : CAT Γ)
    → MAP (Map C E × Map D E) (Map (C ⊔ D) E)
  copairing C D E = IsEquiv.inverse (coproductRestriction-isEquiv C D E)

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    copairing-action : {C D E : CAT Γ}
      → Term (Map C E) → Term (Map D E) → Term (Map (C ⊔ D) E)
    copairing-action {C} {D} {E} x y = copairing C D E ∘ pair x y

    copairing-β : {C D E : CAT Γ} (x : Term (Map C E)) (y : Term (Map D E))
      → (coproductRestriction C D E ∘ copairing-action x y) =₁ pair x y
    copairing-β {C} {D} {E} x y =
      triangle (factor-through-equiv (coproductRestriction-isEquiv C D E) (pair x y))

  private
    copairName : {C D E : CAT Γ} → MAP C E → MAP D E → MAP One (Map (C ⊔ D) E)
    copairName f g = copairing-action (name f) (name g)

    copairName-β : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
      → (coproductRestriction C D E ∘ copairName f g) =₁ pair (name f) (name g)
    copairName-β f g = copairing-β (name f) (name g)

  copair : {C D E : CAT Γ} → MAP C E → MAP D E → MAP (C ⊔ D) E
  copair f g = decode (copairName f g)

  copair-β₁ : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → (copair f g ∘ in₁) =₁ f
  copair-β₁ f g = name-reflect (copair f g ∘ in₁) f
    (pair-β₁ (name f) (name g) ∙
      ((pr₁ ◁ copairName-β f g) ∙
        ((project-pair₁ (mapPre in₁) (mapPre in₂) (copairName f g)) ⁻¹ ∙
          ((mapPre in₁ ◁ name-decode (copairName f g)) ∙
            (mapPre-name in₁ (copair f g)) ⁻¹))))

  copair-β₂ : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → (copair f g ∘ in₂) =₁ g
  copair-β₂ f g = name-reflect (copair f g ∘ in₂) g
    (pair-β₂ (name f) (name g) ∙
      ((pr₂ ◁ copairName-β f g) ∙
        ((project-pair₂ (mapPre in₁) (mapPre in₂) (copairName f g)) ⁻¹ ∙
          ((mapPre in₂ ◁ name-decode (copairName f g)) ∙
            (mapPre-name in₂ (copair f g)) ⁻¹))))
```

## Recovery and action

Restriction detects identification families between external functors.
This preliminary reflection suffices for eta and action laws. The later
full identification-restriction equivalence will construct a recovered
identification with its prescribed restriction equations. No such equations
for this preliminary reflected choice are asserted here.

```agda
  private
    restrict-name₁ : {C D E : CAT Γ} (h : MAP (C ⊔ D) E)
      → (pr₁ ∘ (coproductRestriction C D E ∘ name h)) =₁ name (h ∘ in₁)
    restrict-name₁ h = mapPre-name in₁ h ∙
      project-pair₁ (mapPre in₁) (mapPre in₂) (name h)

    restrict-name₂ : {C D E : CAT Γ} (h : MAP (C ⊔ D) E)
      → (pr₂ ∘ (coproductRestriction C D E ∘ name h)) =₁ name (h ∘ in₂)
    restrict-name₂ h = mapPre-name in₂ h ∙
      project-pair₂ (mapPre in₁) (mapPre in₂) (name h)

    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      coproduct-reflect : {C D E : CAT Γ} (h k : MAP (C ⊔ D) E)
        → (h ∘ in₁) ＝ (k ∘ in₁) → (h ∘ in₂) ＝ (k ∘ in₂) → h ＝ k
      coproduct-reflect {C} {D} {E} h k α β = name-reflect h k
        (factor (factor-through-postWhisker (coproductRestriction C D E)
          (coproductRestriction-isEquiv C D E)
          (pair₌
            (const ((restrict-name₁ k) ⁻¹) ∙ (name⁼ α ∙ const (restrict-name₁ h)))
            (const ((restrict-name₂ k) ⁻¹) ∙ (name⁼ β ∙ const (restrict-name₂ h))))))

  copair-η : {C D E : CAT Γ} (h : MAP (C ⊔ D) E)
    → copair (h ∘ in₁) (h ∘ in₂) =₁ h
  copair-η h = coproduct-reflect _ h
    (copair-β₁ (h ∘ in₁) (h ∘ in₂)) (copair-β₂ (h ∘ in₁) (h ∘ in₂))

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    copair-cong : {C D E : CAT Γ} {f f′ : MAP C E} {g g′ : MAP D E}
      → f ＝ f′ → g ＝ g′ → copair f g ＝ copair f′ g′
    copair-cong {f = f} {f′} {g} {g′} α β = coproduct-reflect _ _
      (const ((copair-β₁ f′ g′) ⁻¹) ∙ (α ∙ const (copair-β₁ f g)))
      (const ((copair-β₂ f′ g′) ⁻¹) ∙ (β ∙ const (copair-β₂ f g)))

  copair-post : {C D E F : CAT Γ} (f : MAP C E) (g : MAP D E) (h : MAP E F)
    → (h ∘ copair f g) =₁ copair (h ∘ f) (h ∘ g)
  copair-post f g h = coproduct-reflect _ _
    ((copair-β₁ (h ∘ f) (h ∘ g)) ⁻¹ ∙
      ((h ◁ copair-β₁ f g) ∙ comp-assoc in₁ (copair f g) h))
    ((copair-β₂ (h ∘ f) (h ∘ g)) ⁻¹ ∙
      ((h ◁ copair-β₂ f g) ∙ comp-assoc in₂ (copair f g) h))
```

## Restriction along summands

Further restriction of a beta triangle retains the associator of the
three functors. Copairing the two inclusions recovers the identity.

```agda
  copair-pre₁ : {X C D E : CAT Γ} (f : MAP C E) (g : MAP D E) (h : MAP X C)
    → (copair f g ∘ (in₁ ∘ h)) =₁ (f ∘ h)
  copair-pre₁ f g h = (copair-β₁ f g ▷ h) ∙ (comp-assoc h in₁ (copair f g)) ⁻¹

  copair-pre₂ : {X C D E : CAT Γ} (f : MAP C E) (g : MAP D E) (h : MAP X D)
    → (copair f g ∘ (in₂ ∘ h)) =₁ (g ∘ h)
  copair-pre₂ f g h = (copair-β₂ f g ▷ h) ∙ (comp-assoc h in₂ (copair f g)) ⁻¹

  copair-inclusions : (C D : CAT Γ)
    → copair (in₁ {C = C} {D = D}) in₂ =₁ id (C ⊔ D)
  copair-inclusions C D = coproduct-reflect _ _
    ((comp-unitˡ in₁) ⁻¹ ∙ copair-β₁ in₁ in₂)
    ((comp-unitˡ in₂) ⁻¹ ∙ copair-β₂ in₁ in₂)
```
