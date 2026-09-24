# Uncurrying is represented by an equivalence

This follows the book's two constructions: curry double evaluation for the
forward functor, and curry evaluation twice for its inverse. Product
reassociation is explicit throughout. Both maps are actual synthetic
functors; no functoriality of the host operation `mapCurry` is assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying

module SCT.VolumeI.Chapter01.Section04.Uncurrying
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M

productMap-pair : {R C C′ D D′ : CAT}
  (f : MAP C C′) (g : MAP D D′) (u : MAP R C) (v : MAP R D)
  → (productMap f g ∘ pair u v) =₁ (pair (f ∘ u) (g ∘ v))
productMap-pair f g u v = pair-cong
  ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
  ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g) ∙
  pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

product-first : {R C C′ D D′ : CAT}
  (f : MAP C C′) (g : MAP D D′) (u : MAP R (C × D))
  → (pr₁ ∘ (productMap f g ∘ u)) =₁ (f ∘ (pr₁ ∘ u))
product-first f g u = comp-assoc u pr₁ f ∙
  ((pair-β₁ (f ∘ pr₁) (g ∘ pr₂) ▷ u) ∙ (comp-assoc u (productMap f g) pr₁) ⁻¹)

product-second : {R C C′ D D′ : CAT}
  (f : MAP C C′) (g : MAP D D′) (u : MAP R (C × D))
  → (pr₂ ∘ (productMap f g ∘ u)) =₁ (g ∘ (pr₂ ∘ u))
product-second f g u = comp-assoc u pr₂ g ∙
  ((pair-β₂ (f ∘ pr₁) (g ∘ pr₂) ▷ u) ∙ (comp-assoc u (productMap f g) pr₂) ⁻¹)
```

The next two comparisons express naturality of the chosen product
reassociation when the first factor changes. Their proofs reduce both
routes to the same three projections.

```agda
module Reassociation {R Y X C : CAT} (σ : MAP R Y) where
  private
    leftChange = productMap (productMap σ (id X)) (id C)
    rightChange = productMap σ (id (X × C))

  forward-natural :
    (Associativity.forward Y X C ∘ leftChange) =₁
    (rightChange ∘ Associativity.forward R X C)
  forward-natural =
    let first = product-first σ (id X) pr₁ ∙
          ((pr₁ ◁ pair-β₁ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)) ∙
            comp-assoc leftChange pr₁ pr₁)
        second = comp-unitˡ (pr₂ ∘ pr₁) ∙
          (product-second σ (id X) pr₁ ∙
          ((pr₂ ◁ pair-β₁ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)) ∙
            comp-assoc leftChange pr₁ pr₂))
        third = comp-unitˡ pr₂ ∙ pair-β₂ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)
        left-normal = pair-cong first
          (pair-cong second third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ leftChange) ∙
          pair-pre (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂) leftChange
        right-normal = pair-cong (idIso (σ ∘ (pr₁ ∘ pr₁)))
          (comp-unitˡ (pair (pr₂ ∘ pr₁) pr₂)) ∙
          productMap-pair σ (id (X × C)) (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)
    in right-normal ⁻¹ ∙ left-normal

  backward-natural :
    (Associativity.backward Y X C ∘ rightChange) =₁
    (leftChange ∘ Associativity.backward R X C)
  backward-natural =
    let first = pair-β₁ (σ ∘ pr₁) (id (X × C) ∘ pr₂)
        secondProjection = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id (X × C) ∘ pr₂)
        second = (pr₁ ◁ secondProjection) ∙ comp-assoc rightChange pr₂ pr₁
        third = (pr₂ ◁ secondProjection) ∙ comp-assoc rightChange pr₂ pr₂
        left-normal = pair-cong
          (pair-cong first second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) rightChange)
          third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) rightChange
        right-normal = pair-cong
          (pair-cong (idIso (σ ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)) ∙
            productMap-pair σ (id X) pr₁ (pr₁ ∘ pr₂))
          (comp-unitˡ (pr₂ ∘ pr₂)) ∙
          productMap-pair (productMap σ (id X)) (id C) (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)
    in right-normal ⁻¹ ∙ left-normal
```

For the remainder, fix the anima `X` and categories `C,D`. The product
`X × C` need not be an anima: only the parameters used for currying must be.

```agda
module ExponentialLaw (X C D : CAT) (xAn : isAn X) where
  Nested : CAT
  Nested = Map X (Map C D)

  Flat : CAT
  Flat = Map (X × C) D

  doubleUncurry : {Z : CAT} → MAP Z Nested → MAP ((Z × X) × C) D
  doubleUncurry f = mapUncurry (mapUncurry f)

  doubleEvaluation : MAP ((Nested × X) × C) D
  doubleEvaluation = mapUncurry (mapEval {X} {Map C D})

  forwardEvaluation : MAP (Nested × (X × C)) D
  forwardEvaluation = doubleEvaluation ∘ Associativity.backward Nested X C

  forward : MAP Nested Flat
  forward = mapCurry (map-isAn X (Map C D)) forwardEvaluation

  backwardEvaluation : MAP ((Flat × X) × C) D
  backwardEvaluation = mapEval ∘ Associativity.forward Flat X C

  backwardFirstCurry : MAP (Flat × X) (Map C D)
  backwardFirstCurry = mapCurry (product-isAn (map-isAn (X × C) D) xAn) backwardEvaluation

  backward : MAP Flat Nested
  backward = mapCurry (map-isAn (X × C) D) backwardFirstCurry

  forward-β : (mapUncurry forward) =₁ forwardEvaluation
  forward-β = mapCurry-β (map-isAn X (Map C D)) forwardEvaluation

  backward-β : (doubleUncurry backward) =₁ backwardEvaluation
  backward-β = mapCurry-β (product-isAn (map-isAn (X × C) D) xAn) backwardEvaluation ∙
    mapUncurry-cong (mapCurry-β (map-isAn (X × C) D) backwardFirstCurry)

  doubleUncurry-restrict : {R Z : CAT} (f : MAP Z Nested) (σ : MAP R Z)
    → (doubleUncurry (f ∘ σ)) =₁
        (doubleUncurry f ∘ productMap (productMap σ (id X)) (id C))
  doubleUncurry-restrict f σ = mapUncurry-restrict (mapUncurry f) (productMap σ (id X)) ∙
    mapUncurry-cong (mapUncurry-restrict f σ)

  doubleReflect : {Z : CAT} (zAn : isAn Z) (f g : MAP Z Nested)
    → (doubleUncurry f) =₁ (doubleUncurry g) → f =₁ g
  doubleReflect zAn f g α = mapReflect zAn f g
    (mapReflect (product-isAn zAn xAn) (mapUncurry f) (mapUncurry g) α)

  doubleUncurry-id : (doubleUncurry (id Nested)) =₁ doubleEvaluation
  doubleUncurry-id = mapUncurry-cong (mapUncurry-id X (Map C D))
```

Substitution into the two constructions gives their representing formulas.
Each proof separates beta reduction from reassociation of the three factors.

```agda
  forward-represents : {Z : CAT} (f : MAP Z Nested)
    → (mapUncurry (forward ∘ f)) =₁
        (doubleUncurry f ∘ Associativity.backward Z X C)
  forward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.backward Z X C

        substitute : (mapUncurry (forward ∘ f)) =₁ (forwardEvaluation ∘ changePair)
        substitute = (forward-β ▷ changePair) ∙ mapUncurry-restrict forward f

        regroupParameters : (forwardEvaluation ∘ changePair) =₁
          ((doubleEvaluation ∘ changeTriple) ∘ regroup)
        regroupParameters = (comp-assoc regroup changeTriple doubleEvaluation) ⁻¹ ∙
          ((doubleEvaluation ◁ Reassociation.backward-natural f) ∙
            comp-assoc changePair (Associativity.backward Nested X C) doubleEvaluation)

        evaluate : (doubleEvaluation ∘ changeTriple) =₁ (doubleUncurry f)
        evaluate = (mapUncurry-restrict (mapEval {X} {Map C D}) (productMap f (id X))) ⁻¹
    in (evaluate ▷ regroup) ∙ (regroupParameters ∙ substitute)

  backward-represents : {Z : CAT} (f : MAP Z Flat)
    → (doubleUncurry (backward ∘ f)) =₁
        (mapUncurry f ∘ Associativity.forward Z X C)
  backward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.forward Z X C

        substitute : (doubleUncurry (backward ∘ f)) =₁ (backwardEvaluation ∘ changeTriple)
        substitute = (backward-β ▷ changeTriple) ∙ doubleUncurry-restrict backward f

        regroupParameters : (backwardEvaluation ∘ changeTriple) =₁
          (mapUncurry f ∘ regroup)
        regroupParameters = (comp-assoc regroup changePair mapEval) ⁻¹ ∙
          ((mapEval ◁ Reassociation.forward-natural f) ∙
            comp-assoc changeTriple (Associativity.forward Flat X C) mapEval)
    in regroupParameters ∙ substitute
```

The inverse comparisons are obtained after one or two uncurrying steps,
exactly as in the book. Reflection uses only anima parameters: `Flat`,
`Nested`, and `Nested × X`.

```agda
  forward-backward : (forward ∘ backward) =₁ (id Flat)
  forward-backward =
    let regroup = Associativity.backward Flat X C
        uncurriedComparison : (mapUncurry (forward ∘ backward)) =₁
          (mapUncurry (id Flat))
        uncurriedComparison = (mapUncurry-id (X × C) D) ⁻¹ ∙
          (comp-unitʳ mapEval ∙
          ((mapEval ◁ Associativity.forward-backward Flat X C) ∙
          (comp-assoc regroup (Associativity.forward Flat X C) mapEval ∙
          ((backward-β ▷ regroup) ∙ forward-represents backward))))
    in mapReflect (map-isAn (X × C) D) (forward ∘ backward) (id Flat) uncurriedComparison

  backward-forward : (backward ∘ forward) =₁ (id Nested)
  backward-forward =
    let regroup = Associativity.forward Nested X C
        uncurriedComparison : (doubleUncurry (backward ∘ forward)) =₁
          (doubleUncurry (id Nested))
        uncurriedComparison = doubleUncurry-id ⁻¹ ∙
          (comp-unitʳ doubleEvaluation ∙
          ((doubleEvaluation ◁ Associativity.backward-forward Nested X C) ∙
          (comp-assoc regroup (Associativity.backward Nested X C) doubleEvaluation ∙
          ((forward-β ▷ regroup) ∙ backward-represents forward))))
    in doubleReflect (map-isAn X (Map C D)) (backward ∘ forward) (id Nested) uncurriedComparison

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = backward-forward ⁻¹
    ; retractionIso = forward-backward ⁻¹ }

mapUncurrying : (X C D : CAT) → isAn X
  → MAP (Map X (Map C D)) (Map (X × C) D)
mapUncurrying X C D xAn = ExponentialLaw.forward X C D xAn

mapUncurrying-isEquiv : (X C D : CAT) (xAn : isAn X)
  → IsEquiv (mapUncurrying X C D xAn)
mapUncurrying-isEquiv X C D xAn = ExponentialLaw.forward-isEquiv X C D xAn
```
