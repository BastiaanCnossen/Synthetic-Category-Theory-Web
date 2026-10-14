# Evaluation by a supplied functor

For `e : F × C → D`, evaluation sends `g : T → F` to
`e ∘ productMap g (id C)`. Its action on identification families has an
independent parameter. The evaluation-induced functor between mapping animae
is obtained by currying at `Map T F`; neither `T` nor `F` must be an anima.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.Evaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as Reassociation
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Mapping
open import SCT.VolumeI.Chapter01.Section04.Points
open import SCT.VolumeI.Chapter01.Section04.MappingSpecialization

module _ {Γ : Context} {F C D : CAT Γ} (e : MAP (F × C) D) where
  evaluate : {T : CAT Γ} → MAP T F → MAP (T × C) D
  evaluate g = e ∘ productMap g (id C)

  evaluate-cong : {T : CAT Γ} {f g : MAP T F} → f =₁ g → evaluate f =₁ evaluate g
  evaluate-cong α = e ◁ productMap-cong α (id₌ (id C))

  evaluation-action : {T : CAT Γ} (f g : MAP T F)
    → MAP (Equal f g) (Equal (evaluate f) (evaluate g))
  evaluation-action f g = postWhisker e ∘
    productMap-cong (id (Equal f g)) (const (id₌ (id C)))

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    evaluate⁼ : {T : CAT Γ} {f g : MAP T F} → f ＝ g → evaluate f ＝ evaluate g
    evaluate⁼ α = e ◁ productMap-cong α (const (id₌ (id C)))

    evaluate⁼-cong : {T : CAT Γ} {f g : MAP T F} {α β : f ＝ g}
      → α =₁ β → evaluate⁼ α =₁ evaluate⁼ β
    evaluate⁼-cong p = postWhisker e ◁ productMap-cong₂ p (id₌ (const (id₌ (id C))))

    evaluation-action-evaluate : {T : CAT Γ} {f g : MAP T F} (α : f ＝ g)
      → (evaluation-action f g ∘ α) =₁ evaluate⁼ α
    evaluation-action-evaluate {f = f} {g} α =
      (postWhisker e ◁
        (productMap-cong₂ (comp-unitˡ α) (const-pre (id₌ (id C)) α) ∙
          productMap-cong-pre (id (Equal f g)) (const (id₌ (id C))) α)) ∙
        comp-assoc α (productMap-cong (id (Equal f g)) (const (id₌ (id C)))) (postWhisker e)

    evaluate⁼-constant : {T : CAT Γ} {f g : MAP T F} (α : f =₁ g)
      → evaluate⁼ (const {P = X} α) =₁ const (evaluate-cong α)
    evaluate⁼-constant α = post-constant e (productMap-cong α (id₌ (id C))) ∙
      (postWhisker e ◁ productMap-cong-constant α (id₌ (id C)))

    evaluate⁼-identity : {T : CAT Γ} (f : MAP T F)
      → evaluate⁼ (const {P = X} (id₌ f)) =₁ const (id₌ (evaluate f))
    evaluate⁼-identity f = const-cong (postWhisker-id₌ e (productMap f (id C))) ∙
      (post-constant e (id₌ (productMap f (id C))) ∙
        (postWhisker e ◁ productMap-cong-id f (id C)))

    evaluate⁼-composition : {T : CAT Γ} {f g h : MAP T F}
      (β : g ＝ h) (α : f ＝ g) → evaluate⁼ (β ∙ α) =₁ (evaluate⁼ β ∙ evaluate⁼ α)
    evaluate⁼-composition β α =
      let identity = const {P = X} (id₌ (id C))
      in postWhisker-comp₌ e (productMap-cong β identity) (productMap-cong α identity) ∙
        (postWhisker e ◁ (productMap-cong-comp β α identity identity ∙
          productMap-cong₂ (id₌ (β ∙ α)) ((comp₌-unitˡ identity) ⁻¹)))

  evaluate⁼-restrict : {X Y T : CAT Γ} {f g : MAP T F}
    (α : MAP X (Equal f g)) (r : MAP Y X) → (evaluate⁼ α ∘ r) =₁ evaluate⁼ (α ∘ r)
  evaluate⁼-restrict α r =
    (postWhisker e ◁
      (productMap-cong₂ (id₌ (α ∘ r)) (const-pre (id₌ (id C)) r) ∙
        productMap-cong-pre α (const (id₌ (id C))) r)) ∙
      postWhisker-pre e (productMap-cong α (const (id₌ (id C)))) r

  evaluate⁼-absolute : {T : CAT Γ} {f g : MAP T F} (α : f =₁ g)
    → evaluate⁼ α =₂ evaluate-cong α
  evaluate⁼-absolute α = postWhisker e ◁
    productMap-cong₂ (id₌ α) (const-One (id₌ (id C)))

  evaluate-restrict : {S T : CAT Γ} (g : MAP T F) (r : MAP S T)
    → evaluate (g ∘ r) =₁ (evaluate g ∘ productMap r (id C))
  evaluate-restrict g r =
    (comp-assoc (productMap r (id C)) (productMap g (id C)) e) ⁻¹ ∙
      (e ◁ (productMap-first-comp g r) ⁻¹)

  evaluate-id : evaluate (id F) =₁ e
  evaluate-id = comp-unitʳ e ∙ (e ◁ productMap-id F C)
```

## The evaluation-induced functor

Reassociate the universal evaluation of a `T`-indexed functor and then
curry at its mapping anima. The comparison below computes this functor
on arbitrary families of such functors. Decoding at the terminal category
gives its specialization comparison, with the same chosen evaluation.

```agda
  module _ (T : CAT Γ) where
    evaluation-universal : MAP (Map T F × (T × C)) D
    evaluation-universal = evaluate mapEval ∘ Associativity.backward (Map T F) T C

    evaluation-forward : MAP (Map T F) (Map (T × C) D)
    evaluation-forward = mapCurry (map-isAn T F) evaluation-universal

    evaluation-represents : {P : CAT Γ} (g : MAP P (Map T F))
      → uncurry (evaluation-forward ∘ g) =₁
          (evaluate (uncurry g) ∘ Associativity.backward P T C)
    evaluation-represents {P} g =
      ((evaluate-restrict mapEval (productMap g (id T))) ⁻¹ ▷ Associativity.backward P T C) ∙
        ((comp-assoc (Associativity.backward P T C)
          (productMap (productMap g (id T)) (id C)) (evaluate mapEval)) ⁻¹ ∙
          (((evaluate mapEval) ◁ Reassociation.backward-natural g) ∙
            (comp-assoc (productMap g (id (T × C)))
              (Associativity.backward (Map T F) T C) (evaluate mapEval) ∙
              ((mapCurry-β (map-isAn T F) evaluation-universal ▷ productMap g (id (T × C))) ∙
                Mapping.uncurry-restrict evaluation-forward g))))

    evaluation-terminal-regroup :
        (Associativity.backward One T C ∘ product-unitˡ-inverse (T × C)) =₁
          productMap (product-unitˡ-inverse T) (id C)
    evaluation-terminal-regroup = pair⁼
        ((pair-pre (terminate T) (id T) pr₁) ⁻¹ ∙
          pair⁼ (terminal-identification _ _)
            ((comp-unitˡ pr₁) ⁻¹ ∙ comp-unitʳ pr₁ ∙
              ((pr₁ ◁ product-unitˡ-pr₂-inverse (T × C)) ∙
                comp-assoc (product-unitˡ-inverse (T × C)) (pr₂ {C = One} {D = T × C}) (pr₁ {C = T} {D = C}))) ∙
          pair-pre pr₁ (pr₁ ∘ pr₂) (product-unitˡ-inverse (T × C)))
        ((comp-unitˡ pr₂) ⁻¹ ∙ comp-unitʳ pr₂ ∙
          ((pr₂ ◁ product-unitˡ-pr₂-inverse (T × C)) ∙
            comp-assoc (product-unitˡ-inverse (T × C)) (pr₂ {C = One} {D = T × C}) (pr₂ {C = T} {D = C}))) ∙
        pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (product-unitˡ-inverse (T × C))

    evaluation-decode : (p : MAP One (Map T F))
      → decode (evaluation-forward ∘ p) =₁ evaluate (decode p)
    evaluation-decode p = (evaluate-restrict (uncurry p) (product-unitˡ-inverse T)) ⁻¹ ∙
      (((evaluate (uncurry p)) ◁ evaluation-terminal-regroup) ∙
        (comp-assoc (product-unitˡ-inverse (T × C)) (Associativity.backward One T C) (evaluate (uncurry p)) ∙
          (evaluation-represents p ▷ product-unitˡ-inverse (T × C))))

    evaluation-specialize : (g : MAP T F)
      → specialize-map evaluation-forward g =₁ evaluate g
    evaluation-specialize g = evaluate-cong (decode-name g) ∙ evaluation-decode (name g)
```
