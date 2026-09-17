# Functors out of a coproduct

For `lem:Functors_Out_Of_Coproduct`, the inverse curries the copair of the
two evaluations, transported through distributivity. Both restriction
comparisons are retained. Uncurrying, distributivity, and coproduct
uniqueness show that these restrictions detect natural isomorphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.CoproductDomain
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section04.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.Distributivity 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section06.Functoriality 𝒯 M F

module ProductDomain (T C D : CAT) where
  open Distributivity T C D
  left = productMap (id T) (in₁ {C} {D})
  right = productMap (id T) (in₂ {C} {D})
  inverse = IsEquiv.inverse distribute-isEquiv

  inverse-left : =₁ (inverse ∘ left) in₁
  inverse-left = equiv-reflect distribute-isEquiv _ _
    (invIso (copair-β₁ left right) ∙ FunctorLift.comparison (equiv-lift distribute-isEquiv left))
  inverse-right : =₁ (inverse ∘ right) in₂
  inverse-right = equiv-reflect distribute-isEquiv _ _
    (invIso (copair-β₂ left right) ∙ FunctorLift.comparison (equiv-lift distribute-isEquiv right))

  join : {E : CAT} → MAP (T × C) E → MAP (T × D) E → MAP (T × (C ⊔ D)) E
  join f g = copair f g ∘ inverse
  join-left : {E : CAT} (f : MAP (T × C) E) (g : MAP (T × D) E) → =₁ (join f g ∘ left) f
  join-left f g = copair-β₁ f g ∙ ((copair f g ◁ inverse-left) ∙ comp-assoc left inverse (copair f g))
  join-right : {E : CAT} (f : MAP (T × C) E) (g : MAP (T × D) E) → =₁ (join f g ∘ right) g
  join-right f g = copair-β₂ f g ∙ ((copair f g ◁ inverse-right) ∙ comp-assoc right inverse (copair f g))

  reflect : {E : CAT} (f g : MAP (T × (C ⊔ D)) E) →
    =₁ (f ∘ left) (g ∘ left) → =₁ (f ∘ right) (g ∘ right) → =₁ f g
  reflect f g α β = FunctorLift.lift (preWhisker-lift distribute distribute-isEquiv
    (coproduct-reflect _ _
      (invIso (comp-assoc in₁ distribute g) ∙
        ((g ◁ invIso (copair-β₁ left right)) ∙ (α ∙
        ((f ◁ copair-β₁ left right) ∙ comp-assoc in₁ distribute f))))
      (invIso (comp-assoc in₂ distribute g) ∙
        ((g ◁ invIso (copair-β₂ left right)) ∙ (β ∙
        ((f ◁ copair-β₂ left right) ∙ comp-assoc in₂ distribute f))))))

module CoproductDomain (C D E : CAT) where
  Source = Fun (C ⊔ D) E
  Target = Fun C E × Fun D E
  left = funPre {D = E} (in₁ {C} {D})
  right = funPre {D = E} (in₂ {C} {D})

  forward : MAP Source Target
  forward = pair left right

  module Domain = ProductDomain Target C D
  backward : MAP Target Source
  backward = funCurry (Domain.join (funUncurry pr₁) (funUncurry pr₂))

  backward-left : =₁ (left ∘ backward) pr₁
  backward-left = funReflect _ _ (Domain.join-left (funUncurry pr₁) (funUncurry pr₂) ∙
    ((funCurry-β (Domain.join (funUncurry pr₁) (funUncurry pr₂)) ▷ Domain.left) ∙ funPre-uncurry in₁ backward))
  backward-right : =₁ (right ∘ backward) pr₂
  backward-right = funReflect _ _ (Domain.join-right (funUncurry pr₁) (funUncurry pr₂) ∙
    ((funCurry-β (Domain.join (funUncurry pr₁) (funUncurry pr₂)) ▷ Domain.right) ∙ funPre-uncurry in₂ backward))

  restrict-reflect : {T : CAT} (f g : MAP T Source) →
    =₁ (left ∘ f) (left ∘ g) → =₁ (right ∘ f) (right ∘ g) → =₁ f g
  restrict-reflect {T} f g α β = funReflect f g (ProductDomain.reflect T C D _ _
    (funPre-uncurry in₁ g ∙ (funUncurry-cong α ∙ invIso (funPre-uncurry in₁ f)))
    (funPre-uncurry in₂ g ∙ (funUncurry-cong β ∙ invIso (funPre-uncurry in₂ f))))

  forward-backward : =₁ (forward ∘ backward) (id Target)
  forward-backward = pair-iso
    (invIso (comp-unitʳ pr₁) ∙ (backward-left ∙ project-pair₁ left right backward))
    (invIso (comp-unitʳ pr₂) ∙ (backward-right ∙ project-pair₂ left right backward))

  backward-forward : =₁ (backward ∘ forward) (id Source)
  backward-forward = restrict-reflect _ _
    (invIso (comp-unitʳ left) ∙
      (pair-β₁ left right ∙ ((backward-left ▷ forward) ∙ invIso (comp-assoc forward backward left))))
    (invIso (comp-unitʳ right) ∙
      (pair-β₂ left right ∙ ((backward-right ▷ forward) ∙ invIso (comp-assoc forward backward right))))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward ; sectionIso = invIso backward-forward ; retractionIso = invIso forward-backward }
```
