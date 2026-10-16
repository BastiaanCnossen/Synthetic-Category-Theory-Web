# Uncurrying and the exponential equivalence

Double uncurrying is represented by an actual functor for any first factor
X. Its inverse and the equivalence proof require X to be an anima. The
construction curries double evaluation; the inverse curries evaluation twice.
Product reassociation and both inverse calculations remain explicit.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Uncurrying where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as Reassociation
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying

module _ {Γ : Context} where
  module ExponentialLaw (X C D : CAT Γ) where
    Nested : CAT Γ
    Nested = Map X (Map C D)

    Flat : CAT Γ
    Flat = Map (X × C) D

    doubleUncurry : {Z : CAT Γ} → MAP Z Nested → MAP ((Z × X) × C) D
    doubleUncurry f = uncurry (uncurry f)

    doubleEvaluation : MAP ((Nested × X) × C) D
    doubleEvaluation = uncurry (mapEval {C = X} {D = Map C D})

    forwardEvaluation : MAP (Nested × (X × C)) D
    forwardEvaluation = doubleEvaluation ∘ Associativity.backward Nested X C

    forward : MAP Nested Flat
    forward = mapCurry (map-isAn X (Map C D)) forwardEvaluation

    forward-β : (uncurry forward) =₁ forwardEvaluation
    forward-β = mapCurry-β (map-isAn X (Map C D)) forwardEvaluation

    doubleUncurry-restrict : {R Z : CAT Γ} (f : MAP Z Nested) (σ : MAP R Z)
      → (doubleUncurry (f ∘ σ)) =₁
          (doubleUncurry f ∘ productMap (productMap σ (id X)) (id C))
    doubleUncurry-restrict f σ = uncurry-restrict (uncurry f) (productMap σ (id X)) ∙
      uncurry⁼ (uncurry-restrict f σ)

    doubleUncurry-id : (doubleUncurry (id Nested)) =₁ doubleEvaluation
    doubleUncurry-id = uncurry⁼ (uncurry-id X (Map C D))

    forward-represents : {Z : CAT Γ} (f : MAP Z Nested)
      → (uncurry (forward ∘ f)) =₁
          (doubleUncurry f ∘ Associativity.backward Z X C)
    forward-represents {Z} f =
      let changePair : MAP (Z × (X × C)) (Nested × (X × C))
          changePair = productMap f (id (X × C))
          changeTriple : MAP ((Z × X) × C) ((Nested × X) × C)
          changeTriple = productMap (productMap f (id X)) (id C)
          regroup : MAP (Z × (X × C)) ((Z × X) × C)
          regroup = Associativity.backward Z X C

          substitute : (uncurry (forward ∘ f)) =₁ (forwardEvaluation ∘ changePair)
          substitute = (forward-β ▷ changePair) ∙ uncurry-restrict forward f

          regroupParameters : (forwardEvaluation ∘ changePair) =₁
            ((doubleEvaluation ∘ changeTriple) ∘ regroup)
          regroupParameters = (comp-assoc regroup changeTriple doubleEvaluation) ⁻¹ ∙
            ((doubleEvaluation ◁ Reassociation.backward-natural f) ∙
              comp-assoc changePair (Associativity.backward Nested X C) doubleEvaluation)

          evaluate : (doubleEvaluation ∘ changeTriple) =₁ (doubleUncurry f)
          evaluate = (uncurry-restrict (mapEval {C = X} {D = Map C D}) (productMap f (id X))) ⁻¹
      in (evaluate ▷ regroup) ∙ (regroupParameters ∙ substitute)
```

The inverse requires currying on a product with X. Its anima witness also
supplies the second reflection used in the inverse proofs.

```agda
    module _ (xAn : isAn X) where
      backwardEvaluation : MAP ((Flat × X) × C) D
      backwardEvaluation = mapEval ∘ Associativity.forward Flat X C

      backwardFirstCurry : MAP (Flat × X) (Map C D)
      backwardFirstCurry = mapCurry (product-isAn (map-isAn (X × C) D) xAn) backwardEvaluation

      backward : MAP Flat Nested
      backward = mapCurry (map-isAn (X × C) D) backwardFirstCurry

      backward-β : (doubleUncurry backward) =₁ backwardEvaluation
      backward-β = mapCurry-β (product-isAn (map-isAn (X × C) D) xAn) backwardEvaluation ∙
        uncurry⁼ (mapCurry-β (map-isAn (X × C) D) backwardFirstCurry)

      doubleUncurry-reflect : {Z : CAT Γ} (zAn : isAn Z) (f g : MAP Z Nested)
        → (doubleUncurry f) =₁ (doubleUncurry g) → f =₁ g
      doubleUncurry-reflect zAn f g α = uncurry-reflect zAn f g
        (uncurry-reflect (product-isAn zAn xAn) (uncurry f) (uncurry g) α)

      backward-represents : {Z : CAT Γ} (f : MAP Z Flat)
        → (doubleUncurry (backward ∘ f)) =₁
            (uncurry f ∘ Associativity.forward Z X C)
      backward-represents {Z} f =
        let changePair : MAP (Z × (X × C)) (Flat × (X × C))
            changePair = productMap f (id (X × C))
            changeTriple : MAP ((Z × X) × C) ((Flat × X) × C)
            changeTriple = productMap (productMap f (id X)) (id C)
            regroup : MAP ((Z × X) × C) (Z × (X × C))
            regroup = Associativity.forward Z X C

            substitute : (doubleUncurry (backward ∘ f)) =₁ (backwardEvaluation ∘ changeTriple)
            substitute = (backward-β ▷ changeTriple) ∙ doubleUncurry-restrict backward f

            regroupParameters : (backwardEvaluation ∘ changeTriple) =₁
              (uncurry f ∘ regroup)
            regroupParameters = (comp-assoc regroup changePair mapEval) ⁻¹ ∙
              ((mapEval ◁ Reassociation.forward-natural f) ∙
                comp-assoc changeTriple (Associativity.forward Flat X C) mapEval)
        in regroupParameters ∙ substitute

      forward-backward : (forward ∘ backward) =₁ (id Flat)
      forward-backward =
        let regroup : MAP (Flat × (X × C)) ((Flat × X) × C)
            regroup = Associativity.backward Flat X C
            uncurried-equation : (uncurry (forward ∘ backward)) =₁
              (uncurry (id Flat))
            uncurried-equation = (uncurry-id (X × C) D) ⁻¹ ∙
              (comp-unitʳ mapEval ∙
              ((mapEval ◁ Associativity.forward-backward Flat X C) ∙
              (comp-assoc regroup (Associativity.forward Flat X C) mapEval ∙
              ((backward-β ▷ regroup) ∙ forward-represents backward))))
        in uncurry-reflect (map-isAn (X × C) D) (forward ∘ backward) (id Flat) uncurried-equation

      backward-forward : (backward ∘ forward) =₁ (id Nested)
      backward-forward =
        let regroup : MAP ((Nested × X) × C) (Nested × (X × C))
            regroup = Associativity.forward Nested X C
            uncurried-equation : (doubleUncurry (backward ∘ forward)) =₁
              (doubleUncurry (id Nested))
            uncurried-equation = doubleUncurry-id ⁻¹ ∙
              (comp-unitʳ doubleEvaluation ∙
              ((doubleEvaluation ◁ Associativity.backward-forward Nested X C) ∙
              (comp-assoc regroup (Associativity.backward Nested X C) doubleEvaluation ∙
              ((forward-β ▷ regroup) ∙ backward-represents forward))))
        in doubleUncurry-reflect (map-isAn X (Map C D)) (backward ∘ forward) (id Nested) uncurried-equation

      forward-isEquiv : IsEquiv forward
      forward-isEquiv = record
        { inverse = backward
        ; left-inverse-law = backward-forward ⁻¹
        ; right-inverse-law = forward-backward ⁻¹ }
```

The forward functor has no anima hypothesis on X; its equivalence does.

```agda
module _ {Γ : Context} where
  mapUncurrying : (X C D : CAT Γ)
    → MAP (Map X (Map C D)) (Map (X × C) D)
  mapUncurrying X C D = ExponentialLaw.forward X C D

  mapUncurrying-isEquiv : (X C D : CAT Γ) (xAn : isAn X)
    → IsEquiv (mapUncurrying X C D)
  mapUncurrying-isEquiv X C D xAn = ExponentialLaw.forward-isEquiv X C D xAn
```
