# Application and composition of mapping terms

A term of Map C D applies to a term of C by evaluation. Composition of
mapping terms is represented by currying double evaluation. These operations
use arbitrary categorical term contexts; only the representing construction
uses the anima property of the product of mapping animae.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Composition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae

module _ {Γ : Context} where
  module _ {P : CAT Γ} where
    open Terms.InContext P using (Term)

    apply-map : {C D : CAT Γ} → Term (Map C D) → Term C → Term D
    apply-map = Binary.binary-apply mapEval

  doubleEvaluation : {C D E : CAT Γ} → MAP ((Map D E × Map C D) × C) E
  doubleEvaluation = apply-map (pr₁ ∘ pr₁) (apply-map (pr₂ ∘ pr₁) pr₂)

  mapComp : {C D E : CAT Γ} → MAP (Map D E × Map C D) (Map C E)
  mapComp {C} {D} {E} =
    mapCurry (product-isAn (map-isAn D E) (map-isAn C D)) doubleEvaluation

  mapComp-β : {C D E : CAT Γ} → uncurry (mapComp {C} {D} {E}) =₁ doubleEvaluation
  mapComp-β {C} {D} {E} =
    mapCurry-β (product-isAn (map-isAn D E) (map-isAn C D)) doubleEvaluation

  mapId : (C : CAT Γ) → MAP (One {Γ}) (Map C C)
  mapId C = mapCurry one-isAn pr₂

  mapId-β : (C : CAT Γ) → uncurry (mapId C) =₁ pr₂
  mapId-β C = mapCurry-β one-isAn pr₂

  module _ {P : CAT Γ} where
    open Terms.InContext P using (Term)

    compose : {C D E : CAT Γ} → Term (Map D E) → Term (Map C D) → Term (Map C E)
    compose = Binary.binary-apply mapComp

    identity-map : (C : CAT Γ) → Term (Map C C)
    identity-map C = const (mapId C)

  module _ {P : CAT Γ} where
    open Terms.InContext P using (Term)

    apply-map-pre : {Q C D : CAT Γ} (x : Term (Map C D)) (y : Term C) (r : MAP Q P)
      → (apply-map x y ∘ r) =₁ apply-map {P = Q} (x ∘ r) (y ∘ r)
    apply-map-pre = Binary.binary-pre mapEval

    compose-pre : {Q C D E : CAT Γ} (y : Term (Map D E)) (x : Term (Map C D)) (r : MAP Q P)
      → (compose y x ∘ r) =₁ compose {P = Q} (y ∘ r) (x ∘ r)
    compose-pre = Binary.binary-pre mapComp

    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      apply-map⁼ : {C D : CAT Γ} {x x′ : Term (Map C D)} {y y′ : Term C}
        → x ＝ x′ → y ＝ y′ → apply-map x y ＝ apply-map x′ y′
      apply-map⁼ = Binary.binary-cong mapEval

      compose⁼ : {C D E : CAT Γ} {y y′ : Term (Map D E)} {x x′ : Term (Map C D)}
        → y ＝ y′ → x ＝ x′ → compose y x ＝ compose y′ x′
      compose⁼ = Binary.binary-cong mapComp

      compose⁼-composition : {C D E : CAT Γ}
        {z z′ z″ : Term (Map D E)} {x x′ x″ : Term (Map C D)}
        (β : z′ ＝ z″) (α : z ＝ z′) (δ : x′ ＝ x″) (γ : x ＝ x′)
        → compose⁼ (β ∙ α) (δ ∙ γ) =₁ (compose⁼ β δ ∙ compose⁼ α γ)
      compose⁼-composition = Binary.binary-cong-comp mapComp

  uncurry-at : {R X C D : CAT Γ}
    (f : MAP X (Map C D)) (p : MAP R X) (x : MAP R C)
    → (uncurry f ∘ pair p x) =₁ (apply-map (f ∘ p) x)
  uncurry-at {C = C} f p x =
    (mapEval ◁ (pair⁼ (id₌ (f ∘ p)) (comp-unitˡ x) ∙
      productMap-pair f (id C) p x)) ∙
      comp-assoc (pair p x) (productMap f (id C)) mapEval

  uncurry-as-apply : {X C D : CAT Γ} (f : MAP X (Map C D))
    → (uncurry f) =₁ (apply-map (f ∘ pr₁) pr₂)
  uncurry-as-apply f = mapEval ◁ pair⁼ (id₌ (f ∘ pr₁)) (comp-unitˡ pr₂)

  apply-map-compose : {X C D E : CAT Γ}
    (y : MAP X (Map D E)) (x : MAP X (Map C D)) (z : MAP X C)
    → (apply-map (compose y x) z) =₁ (apply-map y (apply-map x z))
  apply-map-compose {X} {C} {D} {E} y x z =
    let triple : MAP X ((Map D E × Map C D) × C)
        triple = pair (pair y x) z
        first : ((pr₁ ∘ pr₁) ∘ triple) =₁ y
        first = pair-β₁ y x ∙
          ((pr₁ ◁ pair-β₁ (pair y x) z) ∙ comp-assoc triple pr₁ pr₁)
        second : ((pr₂ ∘ pr₁) ∘ triple) =₁ x
        second = pair-β₂ y x ∙
          ((pr₂ ◁ pair-β₁ (pair y x) z) ∙ comp-assoc triple pr₁ pr₂)
        third : (pr₂ ∘ triple) =₁ z
        third = pair-β₂ (pair y x) z
        inner : (apply-map (pr₂ ∘ pr₁) pr₂ ∘ triple) =₁ apply-map x z
        inner = apply-map⁼ second third ∙ apply-map-pre (pr₂ ∘ pr₁) pr₂ triple
        outer : (doubleEvaluation ∘ triple) =₁ apply-map y (apply-map x z)
        outer = apply-map⁼ first inner ∙
          apply-map-pre (pr₁ ∘ pr₁) (apply-map (pr₂ ∘ pr₁) pr₂) triple
    in outer ∙ ((mapComp-β ▷ triple) ∙ (uncurry-at mapComp (pair y x) z) ⁻¹)

  apply-map-identity : {X C : CAT Γ} (z : MAP X C)
    → (apply-map (identity-map C) z) =₁ z
  apply-map-identity {X} {C} z = pair-β₂ (terminate X) z ∙
    ((mapId-β C ▷ pair (terminate X) z) ∙
      (uncurry-at (mapId C) (terminate X) z) ⁻¹)
```
