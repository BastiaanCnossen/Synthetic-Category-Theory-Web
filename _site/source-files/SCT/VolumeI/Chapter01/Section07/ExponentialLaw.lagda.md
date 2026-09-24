# The internal exponential law

This proves `lem:Internal_Adjunction_Product_Fun`. The preferred functor
curries double evaluation; the inverse curries evaluation twice. The
equivalence is proved by testing on mapping animae, uncurrying twice,
and reassociating the parameter product.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.ExponentialLaw
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (module Reassociation)
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F

open import SCT.VolumeI.Chapter01.Section07.MappingTests 𝒯 M F
  using (module Test; fourfold-regroup)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)

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

  forward-β : (funUncurry forward) =₁ forwardEvaluation
  forward-β = funCurry-β forwardEvaluation

  backward-β : (doubleUncurry backward) =₁ backwardEvaluation
  backward-β = funCurry-β backwardEvaluation ∙
    funUncurry-cong (funCurry-β backwardFirstCurry)

  doubleUncurry-restrict : {R Z : CAT} (f : MAP Z Nested) (σ : MAP R Z)
    → (doubleUncurry (f ∘ σ)) =₁
        (doubleUncurry f ∘ productMap (productMap σ (id X)) (id C))
  doubleUncurry-restrict f σ = funUncurry-restrict (funUncurry f) (productMap σ (id X)) ∙
    funUncurry-cong (funUncurry-restrict f σ)

  doubleReflect : {Z : CAT} (f g : MAP Z Nested)
    → (doubleUncurry f) =₁ (doubleUncurry g) → f =₁ g
  doubleReflect f g α = funReflect f g
    (funReflect (funUncurry f) (funUncurry g) α)

  doubleUncurry-id : (doubleUncurry (id Nested)) =₁ doubleEvaluation
  doubleUncurry-id = funUncurry-cong (funUncurry-id X (Fun C D))
```

Substitution into the two constructions gives their representing formulas.
Each proof separates beta reduction from reassociation of the three factors.

```agda
  forward-represents : {Z : CAT} (f : MAP Z Nested)
    → (funUncurry (forward ∘ f)) =₁
        (doubleUncurry f ∘ Associativity.backward Z X C)
  forward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.backward Z X C

        substitute : (funUncurry (forward ∘ f)) =₁ (forwardEvaluation ∘ changePair)
        substitute = (forward-β ▷ changePair) ∙ funUncurry-restrict forward f

        regroupParameters : (forwardEvaluation ∘ changePair) =₁
          ((doubleEvaluation ∘ changeTriple) ∘ regroup)
        regroupParameters = (comp-assoc regroup changeTriple doubleEvaluation) ⁻¹ ∙
          ((doubleEvaluation ◁ Reassociation.backward-natural f) ∙
            comp-assoc changePair (Associativity.backward Nested X C) doubleEvaluation)

        evaluate : (doubleEvaluation ∘ changeTriple) =₁ (doubleUncurry f)
        evaluate = (funUncurry-restrict (funEval {X} {Fun C D}) (productMap f (id X))) ⁻¹
    in (evaluate ▷ regroup) ∙ (regroupParameters ∙ substitute)

  backward-represents : {Z : CAT} (f : MAP Z Flat)
    → (doubleUncurry (backward ∘ f)) =₁
        (funUncurry f ∘ Associativity.forward Z X C)
  backward-represents {Z} f =
    let changePair = productMap f (id (X × C))
        changeTriple = productMap (productMap f (id X)) (id C)
        regroup = Associativity.forward Z X C

        substitute : (doubleUncurry (backward ∘ f)) =₁ (backwardEvaluation ∘ changeTriple)
        substitute = (backward-β ▷ changeTriple) ∙ doubleUncurry-restrict backward f

        regroupParameters : (backwardEvaluation ∘ changeTriple) =₁
          (funUncurry f ∘ regroup)
        regroupParameters = (comp-assoc regroup changePair funEval) ⁻¹ ∙
          ((funEval ◁ Reassociation.forward-natural f) ∙
            comp-assoc changeTriple (Associativity.forward Flat X C) funEval)
    in regroupParameters ∙ substitute
```

For each test category, the source route uncurries twice and restricts
along the product associator. The target route uncurries once. The
representing formula above identifies `mapPost forward` with this chain.
The four-factor calculation only identifies functors; it does not assert
an unstated higher coherence for the product associators.

```agda
  module OnMaps (T : CAT) where
    module First = Test T X (Fun C D)
    module Second = Test (T × X) C D
    module FlatTest = Test T (X × C) D
    A = Map T Nested
    r = Associativity.backward T X C
    k = productMap (id A) r
    b₁ = Associativity.backward A T (X × C)
    b₂ = Associativity.backward (A × T) X C
    b₃ = Associativity.backward A (T × X) C
    e = productMap (Associativity.backward A T X) (id C)
    evaluation = doubleUncurry (mapEval {T} {Nested})
    normal = evaluation ∘ (b₂ ∘ b₁)

    sourceComparison = mapPre r ∘ (Second.forward ∘ First.forward)

    source-isEquiv : IsEquiv sourceComparison
    source-isEquiv = equiv-compose (Second.forward ∘ First.forward) (mapPre r)
      (equiv-compose First.forward Second.forward First.forward-isEquiv Second.forward-isEquiv)
      (mapPre-isEquiv r (equiv-inverse (Associativity.forward-isEquiv T X C)))

    source-evaluation : (mapUncurry sourceComparison) =₁ normal
    source-evaluation = (evaluation ◁ (fourfold-regroup A T X C) ⁻¹) ∙
      (comp-assoc (b₃ ∘ k) e evaluation ∙
      (((funUncurry-restrict (funUncurry mapEval) (Associativity.backward A T X) ∙
          funUncurry-cong (mapCurry-β (map-isAn T Nested) First.evaluation)) ▷ (b₃ ∘ k)) ∙
      (comp-assoc k b₃ (funUncurry (mapUncurry First.forward)) ∙
      ((Second.represents First.forward ▷ k) ∙
        mapPre-uncurry r (Second.forward ∘ First.forward)))))

    tested-evaluation : (mapUncurry (FlatTest.forward ∘ mapPost forward)) =₁ normal
    tested-evaluation = comp-assoc b₁ b₂ evaluation ∙
      ((forward-represents mapEval ▷ b₁) ∙
      ((funUncurry-cong (mapPost-β forward) ▷ b₁) ∙
        FlatTest.represents (mapPost forward)))

    comparison-square : (FlatTest.forward ∘ mapPost forward) =₁ sourceComparison
    comparison-square = mapReflect (map-isAn T Nested) _ _
      (source-evaluation ⁻¹ ∙ tested-evaluation)

    comparison-isEquiv : IsEquiv (mapPost {C = T} forward)
    comparison-isEquiv = equiv-cancel-left (mapPost forward) FlatTest.forward
      FlatTest.forward-isEquiv (equiv-transport (comparison-square ⁻¹) source-isEquiv)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = post-tests-all forward OnMaps.comparison-isEquiv
```

The backward functor described in the manuscript is indeed an inverse.
Its evaluation formula gives the first comparison; the second follows by
reflection through the equivalence already proved on mapping animae.
These computations are not used to establish that equivalence.

```agda
  forward-backward : (forward ∘ backward) =₁ (id Flat)
  forward-backward = funReflect _ _
    ((funUncurry-id (X × C) D) ⁻¹ ∙
    (comp-unitʳ funEval ∙
    ((funEval ◁ Associativity.forward-backward Flat X C) ∙
    (comp-assoc (Associativity.backward Flat X C) (Associativity.forward Flat X C) funEval ∙
    ((backward-β ▷ Associativity.backward Flat X C) ∙ forward-represents backward)))))

  backward-forward : (backward ∘ forward) =₁ (id Nested)
  backward-forward = equiv-reflect forward-isEquiv _ _
    ((comp-unitʳ forward) ⁻¹ ∙
    (comp-unitˡ forward ∙
    ((forward-backward ▷ forward) ∙ (comp-assoc forward backward forward) ⁻¹)))
```
