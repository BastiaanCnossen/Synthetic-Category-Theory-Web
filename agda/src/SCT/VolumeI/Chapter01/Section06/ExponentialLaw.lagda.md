# The internal exponential law

This proves `lem:Internal_Adjunction_Product_Fun`. The preferred functor
curries double evaluation; the inverse curries evaluation twice. The
inverse comparisons are proved by uncurrying and reassociating products.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.ExponentialLaw
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (module Reassociation)
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F

module ExponentialLaw (X C D : CAT) where
  Nested : CAT
  Nested = Fun X (Fun C D)

  Flat : CAT
  Flat = Fun (X × C) D

  doubleUncurry : {Z : CAT} → MAP Z Nested → MAP ((Z × X) × C) D
  doubleUncurry f = funUncurry (funUncurry f)

  doubleEvaluation : MAP ((Nested × X) × C) D
  doubleEvaluation = funUncurry (funEval {X} {Fun C D})

  forwardEvaluation : MAP (Nested × (X × C)) D
  forwardEvaluation = doubleEvaluation ∘ Associativity.backward Nested X C

  forward : MAP Nested Flat
  forward = funCurry forwardEvaluation

  backwardEvaluation : MAP ((Flat × X) × C) D
  backwardEvaluation = funEval ∘ Associativity.forward Flat X C

  backwardFirstCurry : MAP (Flat × X) (Fun C D)
  backwardFirstCurry = funCurry backwardEvaluation

  backward : MAP Flat Nested
  backward = funCurry backwardFirstCurry

  forward-β : NatIso (funUncurry forward) forwardEvaluation
  forward-β = funCurry-β forwardEvaluation

  backward-β : NatIso (doubleUncurry backward) backwardEvaluation
  backward-β = funCurry-β backwardEvaluation ∙
    funUncurry-cong (funCurry-β backwardFirstCurry)

  doubleUncurry-pre : {R Z : CAT} (f : MAP Z Nested) (σ : MAP R Z)
    → NatIso (doubleUncurry (f ∘ σ))
        (doubleUncurry f ∘ productMap (productMap σ (id X)) (id C))
  doubleUncurry-pre f σ = funUncurry-pre (funUncurry f) (productMap σ (id X)) ∙
    funUncurry-cong (funUncurry-pre f σ)

  doubleReflect : {Z : CAT} (f g : MAP Z Nested)
    → NatIso (doubleUncurry f) (doubleUncurry g) → NatIso f g
  doubleReflect f g α = funReflect f g
    (funReflect (funUncurry f) (funUncurry g) α)

  doubleUncurry-id : NatIso (doubleUncurry (id Nested)) doubleEvaluation
  doubleUncurry-id = funUncurry-cong (funUncurry-id X (Fun C D))
```

Substitution into the two constructions gives their representing formulas.
Each proof separates beta reduction from reassociation of the three factors.

```agda
  forward-represents : {Z : CAT} (f : MAP Z Nested)
    → NatIso (funUncurry (forward ∘ f))
        (doubleUncurry f ∘ Associativity.backward Z X C)
  forward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.backward Z X C

        substitute : NatIso (funUncurry (forward ∘ f)) (forwardEvaluation ∘ changePair)
        substitute = (forward-β ▷ changePair) ∙ funUncurry-pre forward f

        regroupParameters : NatIso (forwardEvaluation ∘ changePair)
          ((doubleEvaluation ∘ changeTriple) ∘ regroup)
        regroupParameters = invIso (comp-assoc regroup changeTriple doubleEvaluation) ∙
          ((doubleEvaluation ◁ Reassociation.backward-natural f) ∙
            comp-assoc changePair (Associativity.backward Nested X C) doubleEvaluation)

        evaluate : NatIso (doubleEvaluation ∘ changeTriple) (doubleUncurry f)
        evaluate = invIso (funUncurry-pre (funEval {X} {Fun C D}) (productMap f (id X)))
    in (evaluate ▷ regroup) ∙ (regroupParameters ∙ substitute)

  backward-represents : {Z : CAT} (f : MAP Z Flat)
    → NatIso (doubleUncurry (backward ∘ f))
        (funUncurry f ∘ Associativity.forward Z X C)
  backward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.forward Z X C

        substitute : NatIso (doubleUncurry (backward ∘ f)) (backwardEvaluation ∘ changeTriple)
        substitute = (backward-β ▷ changeTriple) ∙ doubleUncurry-pre backward f

        regroupParameters : NatIso (backwardEvaluation ∘ changeTriple)
          (funUncurry f ∘ regroup)
        regroupParameters = invIso (comp-assoc regroup changePair funEval) ∙
          ((funEval ◁ Reassociation.forward-natural f) ∙
            comp-assoc changeTriple (Associativity.forward Flat X C) funEval)
    in regroupParameters ∙ substitute
```

The inverse comparisons are obtained after one or two uncurrying steps,
exactly as in the book. Reflection applies to arbitrary parameters, including `Flat`,
`Nested`, and `Nested × X`.

```agda
  forward-backward : NatIso (forward ∘ backward) (id Flat)
  forward-backward =
    let regroup = Associativity.backward Flat X C
        uncurriedComparison : NatIso (funUncurry (forward ∘ backward))
          (funUncurry (id Flat))
        uncurriedComparison = invIso (funUncurry-id (X × C) D) ∙
          (comp-unitʳ funEval ∙
          ((funEval ◁ Associativity.forward-backward Flat X C) ∙
          (comp-assoc regroup (Associativity.forward Flat X C) funEval ∙
          ((backward-β ▷ regroup) ∙ forward-represents backward))))
    in funReflect (forward ∘ backward) (id Flat) uncurriedComparison

  backward-forward : NatIso (backward ∘ forward) (id Nested)
  backward-forward =
    let regroup = Associativity.forward Nested X C
        uncurriedComparison : NatIso (doubleUncurry (backward ∘ forward))
          (doubleUncurry (id Nested))
        uncurriedComparison = invIso doubleUncurry-id ∙
          (comp-unitʳ doubleEvaluation ∙
          ((doubleEvaluation ◁ Associativity.backward-forward Nested X C) ∙
          (comp-assoc regroup (Associativity.backward Nested X C) doubleEvaluation ∙
          ((forward-β ▷ regroup) ∙ backward-represents forward))))
    in doubleReflect (backward ∘ forward) (id Nested) uncurriedComparison

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward }

```
