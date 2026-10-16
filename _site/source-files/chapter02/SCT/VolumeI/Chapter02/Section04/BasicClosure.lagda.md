# Constant diagrams and elementary groupoid closure

Uncurrying a constant diagram restricted to an object family gives that
family after the projection which forgets the diagram variable. Comparing
these representations shows that constant diagrams commute with
postcomposition, for the specified constant-arrow and functor-category maps.

This single comparison identifies constants in a product through its two
projections and transports the groupoid condition along an equivalence.
Functors into the terminal category give the terminal-groupoid result.
These are structural groupoid statements, with no anima-recognition clause.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.BasicClosure where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport; equiv-cancel-left; equiv-cancel-right; equiv-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Equivalences using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPost; funPost-uncurry; funPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.FunctorProducts using (module ProductComparison)
open import SCT.VolumeI.Chapter01.Section07.FunctorProperties using (funTerminal-isEquiv)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; constantArrow; constantArrow-image; identityArrow; ev₀)
open import SCT.VolumeI.Chapter02.Section04.Groupoids using (IsGroupoid; groupoid-from-source-equivalence)

module _ {Γ : Context} where
  constant-evaluation : (I C : CAT Γ) {P : CAT Γ} (f : MAP P C)
    → funUncurry {C = I} {D = C} (constantArrow I C ∘ f) =₁ (f ∘ (pr₁ {C = P} {D = I}))
  constant-evaluation I C f = pair-β₁ (f ∘ pr₁) (id I ∘ pr₂) ∙
    ((constantArrow-image I C ▷ productMap f (id I)) ∙
      evaluate-restrict (funEval {C = I} {D = C}) (constantArrow I C) f)

  constant-natural : (I : CAT Γ) {C D : CAT Γ} (F : MAP C D)
    → (funPost {C = I} F ∘ constantArrow I C) =₁ (constantArrow I D ∘ F)
  constant-natural I {C} {D} F = reflect (funEval {C = I} {D = D}) (funUniversal I D)
    (funPost {C = I} F ∘ constantArrow I C) (constantArrow I D ∘ F)
    (right ⁻¹ ∙ left)
    where
      left : funUncurry {C = I} {D = D} (funPost {C = I} F ∘ constantArrow I C)
        =₁ (F ∘ (pr₁ {C = C} {D = I}))
      left = (F ◁ constantArrow-image I C) ∙
        funPost-uncurry {C = I} F (constantArrow I C)
      right : funUncurry {C = I} {D = D} (constantArrow I D ∘ F)
        =₁ (F ∘ (pr₁ {C = C} {D = I}))
      right = constant-evaluation I D F

  constant-product : (I C D : CAT Γ)
    → (ProductComparison.forward I C D ∘ constantArrow I (C × D))
        =₁ productMap (constantArrow I C) (constantArrow I D)
  constant-product I C D = pair⁼
    (constant-natural I {C = C × D} {D = C} pr₁)
    (constant-natural I {C = C × D} {D = D} pr₂) ∙
    pair-pre (funPost {C = I} (pr₁ {C = C} {D = D}))
      (funPost {C = I} (pr₂ {C = C} {D = D})) (constantArrow I (C × D))

  product-isGroupoid : {C D : CAT Γ} → IsGroupoid C → IsGroupoid D → IsGroupoid (C × D)
  product-isGroupoid {C} {D} left right =
    equiv-cancel-left (identityArrow {C = C × D}) (ProductComparison.forward [1] C D)
      (ProductComparison.forward-isEquiv [1] C D)
      (equiv-transport ((constant-product [1] C D) ⁻¹)
        (productMap-isEquiv (identityArrow {C = C}) (identityArrow {C = D}) left right))

  equivalence-preserves-groupoid : {C D : CAT Γ} (F : MAP C D)
    → IsEquiv F → IsGroupoid C → IsGroupoid D
  equivalence-preserves-groupoid {C} {D} F e given =
    equiv-cancel-right F (identityArrow {C = D}) e
      (equiv-transport (constant-natural [1] {C = C} {D = D} F)
        (equiv-compose (identityArrow {C = C}) (funPost {C = [1]} F) given
          (funPost-isEquiv {A = [1]} F e)))

  equivalence-reflects-groupoid : {C D : CAT Γ} (F : MAP C D)
    → IsEquiv F → IsGroupoid D → IsGroupoid C
  equivalence-reflects-groupoid {C} {D} F e =
    equivalence-preserves-groupoid {C = D} {D = C} (IsEquiv.inverse e) (equiv-inverse e)

  terminal-isGroupoid : IsGroupoid (One {Γ = Γ})
  terminal-isGroupoid = groupoid-from-source-equivalence {C = One {Γ = Γ}}
    (equiv-transport
      (terminal-identification (terminate (Ar (One {Γ = Γ}))) (ev₀ {C = One {Γ = Γ}}))
      (funTerminal-isEquiv ([1] {Γ = Γ})))
```
