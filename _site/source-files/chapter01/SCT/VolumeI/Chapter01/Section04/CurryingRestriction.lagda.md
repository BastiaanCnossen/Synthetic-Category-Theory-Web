# Restriction of currying and recovery

Currying before and after substitution compares through the actual evaluation
betas. Restricting a recovered family computes at every categorical Q; only
comparison with a new recovery requires Q to be an anima. The family parameter
X is independent of the term source and substitution source.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CurryingRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (inverse-unique)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (changeEndpoints)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction

module _ {Γ : Context} where
  curry-restrict-uncurried : {P Q C D : CAT Γ} (pAn : isAn P) (qAn : isAn Q)
    (h : MAP (P × C) D) (σ : MAP Q P)
    → uncurry (mapCurry pAn h ∘ σ) =₁ uncurry (mapCurry qAn (h ∘ productMap σ (id C)))
  curry-restrict-uncurried {C = C} pAn qAn h σ =
    (mapCurry-β qAn (h ∘ productMap σ (id C))) ⁻¹ ∙
      ((mapCurry-β pAn h ▷ productMap σ (id C)) ∙ uncurry-restrict (mapCurry pAn h) σ)

  curry-restrict : {P Q C D : CAT Γ} (pAn : isAn P) (qAn : isAn Q)
    (h : MAP (P × C) D) (σ : MAP Q P)
    → (mapCurry pAn h ∘ σ) =₁ mapCurry qAn (h ∘ productMap σ (id C))
  curry-restrict pAn qAn h σ = uncurry-reflect qAn _ _ (curry-restrict-uncurried pAn qAn h σ)

  curry-restrict-β : {P Q C D : CAT Γ} (pAn : isAn P) (qAn : isAn Q)
    (h : MAP (P × C) D) (σ : MAP Q P)
    → uncurry⁼ (curry-restrict pAn qAn h σ) =₂ curry-restrict-uncurried pAn qAn h σ
  curry-restrict-β pAn qAn h σ = uncurry-reflect-β qAn _ _ (curry-restrict-uncurried pAn qAn h σ)

  module _ {X P Q C D : CAT Γ} where
    open Terms.InContext P using (Term)
    open Terms.Equalities X using (_＝_)

    restrict-uncurried : (f g : Term (Map C D))
      → uncurry f ＝ uncurry g → (σ : MAP Q P)
      → uncurry (f ∘ σ) ＝ uncurry (g ∘ σ)
    restrict-uncurried f g α σ = (const (uncurry-restrict g σ)) ⁻¹ ∙
      ((α ▷ productMap σ (id C)) ∙ const (uncurry-restrict f σ))

    uncurry-reflect-restrict-β : (pAn : isAn P) (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      → uncurry⁼ (uncurry-reflect pAn f g α ▷ σ) =₁ restrict-uncurried f g α σ
    uncurry-reflect-restrict-β pAn f g α σ =
      comp₌-cong (id₌ ((const (uncurry-restrict g σ)) ⁻¹))
        (comp₌-cong (preWhisker (productMap σ (id C)) ◁ uncurry-reflect-β pAn f g α)
          (id₌ (const (uncurry-restrict f σ))) ∙
          uncurry-restrict-inputs (uncurry-reflect pAn f g α) σ) ∙
        (inv-comp-left (const (uncurry-restrict g σ))
          (uncurry⁼ (uncurry-reflect pAn f g α ▷ σ))) ⁻¹

    uncurry-reflect-restrict : (pAn : isAn P) (qAn : isAn Q)
      (f g : Term (Map C D)) (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      → (uncurry-reflect pAn f g α ▷ σ) =₁
          uncurry-reflect qAn (f ∘ σ) (g ∘ σ) (restrict-uncurried f g α σ)
    uncurry-reflect-restrict pAn qAn f g α σ = uncurry⁼-reflect qAn _ _
      ((uncurry-reflect-β qAn (f ∘ σ) (g ∘ σ) (restrict-uncurried f g α σ)) ⁻¹ ∙
        uncurry-reflect-restrict-β pAn f g α σ)
```


## Specified endpoint changes

Both endpoint changes are supplied families over X. Specialization is the
existing endpoint transport operation applied to the restricted recovery.
Its actual uncurried image computes without Q being an anima. Comparing
with a fresh recovery at the new endpoints adds that hypothesis explicitly.

```agda
    private
      uncurry-inverse : {f g : MAP Q (Map C D)} (δ : f ＝ g)
        → uncurry⁼ (δ ⁻¹) =₁ (uncurry⁼ δ) ⁻¹
      uncurry-inverse {f} δ =
        (inverse-unique (uncurry⁼ δ) (uncurry⁼ (δ ⁻¹))
          (uncurry⁼-identity f ∙
            (uncurry⁼-cong (comp₌-inverseˡ δ) ∙
              (uncurry⁼-composition (δ ⁻¹) δ) ⁻¹))) ⁻¹

    specialize-uncurried : (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      {f′ g′ : MAP Q (Map C D)} → (f ∘ σ) ＝ f′ → (g ∘ σ) ＝ g′
      → uncurry f′ ＝ uncurry g′
    specialize-uncurried f g α σ left right =
      changeEndpoints (uncurry⁼ left) (uncurry⁼ right) (restrict-uncurried f g α σ)

    specialize-recovery : (pAn : isAn P) (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      {f′ g′ : MAP Q (Map C D)} → (f ∘ σ) ＝ f′ → (g ∘ σ) ＝ g′ → f′ ＝ g′
    specialize-recovery pAn f g α σ left right =
      changeEndpoints left right (uncurry-reflect pAn f g α ▷ σ)

    specialize-recovery-β : (pAn : isAn P) (f g : Term (Map C D))
      (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      {f′ g′ : MAP Q (Map C D)} (left : (f ∘ σ) ＝ f′) (right : (g ∘ σ) ＝ g′)
      → uncurry⁼ (specialize-recovery pAn f g α σ left right) =₁
          specialize-uncurried f g α σ left right
    specialize-recovery-β pAn f g α σ left right =
      comp₌-cong (id₌ (uncurry⁼ right))
        (comp₌-cong (uncurry-reflect-restrict-β pAn f g α σ) (uncurry-inverse left)) ∙
        (comp₌-cong (id₌ (uncurry⁼ right))
            (uncurry⁼-composition (uncurry-reflect pAn f g α ▷ σ) (left ⁻¹)) ∙
          uncurry⁼-composition right ((uncurry-reflect pAn f g α ▷ σ) ∙ left ⁻¹))

    specialize-recovery-fresh : (pAn : isAn P) (qAn : isAn Q)
      (f g : Term (Map C D)) (α : uncurry f ＝ uncurry g) (σ : MAP Q P)
      {f′ g′ : MAP Q (Map C D)} (left : (f ∘ σ) ＝ f′) (right : (g ∘ σ) ＝ g′)
      → specialize-recovery pAn f g α σ left right =₁
          uncurry-reflect qAn f′ g′ (specialize-uncurried f g α σ left right)
    specialize-recovery-fresh pAn qAn f g α σ {f′} {g′} left right = uncurry⁼-reflect qAn _ _
      ((uncurry-reflect-β qAn f′ g′ (specialize-uncurried f g α σ left right)) ⁻¹ ∙
        specialize-recovery-β pAn f g α σ left right)
```
