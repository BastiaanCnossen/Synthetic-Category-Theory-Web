# Coordinates for the join pushout

An equivalence with the fiber product replaces its interval boundary by
two copies of the parameter category. The two projection comparisons
identify the attaching maps. Comparison of universal cocones then gives
an equivalence with the chosen join, retaining its boundary and cylinder
comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroℕ)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpanCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (pair-after; productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutExtensions 𝒯 M P using (pushout-extension-property)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.SpanEquivalence 𝒯 M ℱ P using (module Transfer; module RestrictUniversal)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J using (JoinOver; mapping-out)

insert : {V : CAT} → Obj-abs [1] → MAP V (V × [1])
insert {V} endpoint = pair (id V) (const endpoint)

module Coordinates {C D Γ V : CAT} (p : MAP C Γ) (q : MAP D Γ) (Γ-isAn : isAn Γ)
  (e : MAP V (Pullback p q)) (ee : IsEquiv e)
  (h₀ : MAP V C) (h₁ : MAP V D)
  (β₀ : (pullback₁ ∘ e) =₁ h₀) (β₁ : (pullback₂ ∘ e) =₁ h₁) where
  module Original = Span p q
    using (W; top; left; left-distribute; distributed-left; left-component; right-component)
  -- `Distributivity` and the `JoinPushout` record module are used through
  -- direct calls rather than local module instantiations.
  private
    pushout-cocone = JoinPushout.cocone (mapping-out p q Γ-isAn)
    pushout-extensions = pushout-extension-property (JoinPushout.square (mapping-out p q Γ-isAn))
      (JoinPushout.universal (mapping-out p q Γ-isAn))
  top : MAP (V ⊔ V) (V × [1])
  top = copair (insert {V} zero) (insert {V} one)
  bottom = copair (in₁ ∘ h₀) (in₂ ∘ h₁)
  point = pair e (terminate V)
  doubled = coproductMap point point
  boundary-change = Distributivity.distribute Original.W One One ∘ doubled
  cylinder-change = productMap e (id [1])
  abstract
    point-isEquiv : IsEquiv point
    point-isEquiv = equiv-cancel-left point pr₁ (product-unitʳ-isEquiv Original.W)
      (equiv-transport ((pair-β₁ e (terminate V)) ⁻¹) ee)
    boundary-isEquiv : IsEquiv boundary-change
    boundary-isEquiv = equiv-compose doubled (Distributivity.distribute Original.W One One)
      (coproductMap-isEquiv point point point-isEquiv point-isEquiv)
      (Distributivity.distribute-isEquiv Original.W One One)
    cylinder-isEquiv : IsEquiv cylinder-change
    cylinder-isEquiv = productMap-isEquiv e (id [1]) ee (id-isEquiv [1])

    distribute-change : boundary-change =₁
      copair (productMap (id Original.W) in₁ ∘ point) (productMap (id Original.W) in₂ ∘ point)
    distribute-change = copair-cong
      (copair-pre₁ (productMap (id Original.W) in₁) (productMap (id Original.W) in₂) point)
      (copair-pre₂ (productMap (id Original.W) in₁) (productMap (id Original.W) in₂) point) ∙
      copair-post (in₁ ∘ point) (in₂ ∘ point) (Distributivity.distribute Original.W One One)

    endpoint-top : (i : MAP One ∂[1]) (endpoint : Obj-abs [1]) → (boundary ∘ i) =₁ endpoint →
      (Original.top ∘ (productMap (id Original.W) i ∘ point)) =₁
      (cylinder-change ∘ insert endpoint)
    endpoint-top i endpoint β =
      (pair-cong (comp-unitʳ e) (comp-unitˡ (const endpoint)) ∙
        pair-after e (id [1]) (id V) (const endpoint)) ⁻¹ ∙
      (pair-cong (comp-unitˡ e)
        ((β ▷ terminate V) ∙ (comp-assoc (terminate V) i boundary) ⁻¹) ∙
        (pair-after (id Original.W) boundary e (i ∘ terminate V) ∙
          ((Original.top ◁ (pair-cong (comp-unitˡ e) (idIso (i ∘ terminate V)) ∙
            pair-after (id Original.W) i e (terminate V))))))

    top-comparison : (Original.top ∘ boundary-change) =₁ (cylinder-change ∘ top)
    top-comparison = (copair-post (insert zero) (insert one) cylinder-change) ⁻¹ ∙
      (copair-cong (endpoint-top in₁ zero (copair-β₁ zero one))
        (endpoint-top in₂ one (copair-β₂ zero one)) ∙
        (copair-post (productMap (id Original.W) in₁ ∘ point)
          (productMap (id Original.W) in₂ ∘ point) Original.top ∙
          (Original.top ◁ distribute-change)))

    cancel-distribution : (Original.left ∘ Distributivity.distribute Original.W One One) =₁
      Original.distributed-left
    cancel-distribution = Original.left-distribute

    leg-comparison : {A : CAT} (h : MAP Original.W A) (h′ : MAP V A)
      (β : (h ∘ e) =₁ h′) (j : MAP A (C ⊔ D)) →
      ((j ∘ (h ∘ pr₁)) ∘ point) =₁ (j ∘ h′)
    leg-comparison h h′ β j = (j ◁ (β ∙ ((h ◁ pair-β₁ e (terminate V)) ∙
      comp-assoc point pr₁ h))) ∙ comp-assoc point (h ∘ pr₁) j

    bottom-comparison : (Original.left ∘ boundary-change) =₁ (id (C ⊔ D) ∘ bottom)
    bottom-comparison = (comp-unitˡ bottom) ⁻¹ ∙
      (copair-cong (leg-comparison pullback₁ h₀ β₀ in₁) (leg-comparison pullback₂ h₁ β₁ in₂) ∙
        (copair-cong (copair-pre₁ Original.left-component Original.right-component point)
          (copair-pre₂ Original.left-component Original.right-component point) ∙
          (copair-post (in₁ ∘ point) (in₂ ∘ point) Original.distributed-left ∙
            ((cancel-distribution ▷ doubled) ∙
              (comp-assoc doubled (Distributivity.distribute Original.W One One) Original.left) ⁻¹))))

  module Universal = RestrictUniversal top bottom Original.top Original.left boundary-change cylinder-change
    (id (C ⊔ D)) top-comparison bottom-comparison boundary-isEquiv cylinder-isEquiv
    (id-isEquiv (C ⊔ D)) pushout-cocone pushout-extensions using (cocone; extensions)

  module Compare {E : CAT} (s : Cocone top bottom E) (universal : CoconeExtensionProperty s) where
    forward = Transfer.Into.forward top bottom Original.top Original.left boundary-change cylinder-change
      (id (C ⊔ D)) top-comparison bottom-comparison boundary-isEquiv cylinder-isEquiv
      (id-isEquiv (C ⊔ D)) s universal pushout-cocone pushout-extensions
    isEquiv = Transfer.Into.isEquiv top bottom Original.top Original.left boundary-change cylinder-change
      (id (C ⊔ D)) top-comparison bottom-comparison boundary-isEquiv cylinder-isEquiv
      (id-isEquiv (C ⊔ D)) s universal pushout-cocone pushout-extensions
    comparison = Transfer.Into.comparison top bottom Original.top Original.left boundary-change cylinder-change
      (id (C ⊔ D)) top-comparison bottom-comparison boundary-isEquiv cylinder-isEquiv
      (id-isEquiv (C ⊔ D)) s universal pushout-cocone pushout-extensions
```
