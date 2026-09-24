# Evaluating identifications of restriction maps

Evaluation retains the specified identification of a restriction map.
The naturality square below is used separately at each vertex of a
triangle, so that an edge comparison carries its endpoint equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section02.RestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EndpointNaturality 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; preWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PC
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-cong-comp; pair-cong-id)
open import SCT.VolumeI.Chapter01.Section07.TerminalDomain 𝒯 M ℱ using (evalAt-point-isEquiv)

evaluate-point-isEquiv : (C : CAT) → IsEquiv (evaluate {C = C} (id One))
evaluate-point-isEquiv C = equiv-transport (evaluate-agrees (id One)) (evalAt-point-isEquiv C)

abstract
  evaluate-cong-Iso₂ : {A C : CAT} {x y : Obj-abs A} {α β : x =₁ y} →
    α =₂ β → (evaluate-cong {C = C} α) =₂ (evaluate-cong β)
  evaluate-cong-Iso₂ {A} {C} η = postWhisker funEval ◁
    pair-cong-Iso₂ (idIso (idIso (id (Fun A C)))) (preWhisker (terminate (Fun A C)) ◁ η)

  evaluate-cong-id : {A C : CAT} (x : Obj-abs A) →
    (evaluate-cong {C = C} (idIso x)) =₂ (idIso (evaluate x))
  evaluate-cong-id {A} {C} x = postWhisker-idIso funEval (insert x) ∙
    (postWhisker funEval ◁ (pair-cong-id (id (Fun A C)) (const x) ∙
      pair-cong-Iso₂ (idIso (idIso (id (Fun A C)))) (preWhisker-idIso x (terminate (Fun A C)))))

  evaluate-cong-comp : {A C : CAT} {x y z : Obj-abs A}
    (β : y =₁ z) (α : x =₁ y) →
    (evaluate-cong {C = C} (β ∙ α)) =₂ (evaluate-cong β ∙ evaluate-cong α)
  evaluate-cong-comp {A} {C} β α = postWhisker-isoComp-at funEval _ _ ∙
    (postWhisker funEval ◁
      (pair-cong-comp (idIso (id (Fun A C))) (idIso (id (Fun A C)))
        (β ▷ terminate (Fun A C)) (α ▷ terminate (Fun A C)) ∙
        pair-cong-Iso₂ ((isoComp-unitˡ-at (idIso (id (Fun A C)))) ⁻¹)
          (preWhisker-isoComp-at β α (terminate (Fun A C)))))

module Restriction {A B C : CAT} {f g : MAP A B}
  (α : f =₁ g) (x : Obj-abs A) where
  X = Fun B C
  i = insert {X = X} x
  F = productMap (id X) f
  G = productMap (id X) g
  δ = preCong {E = C} α
  βf = funPre-β {D = C} f
  βg = funPre-β {D = C} g
  image = productMap-cong (idIso (id X)) α
  pair-image = pair-cong (idIso (id X) ▷ id X) (α ▷ const x)
  final-image = pair-cong (idIso (id X)) ((α ▷ x) ▷ terminate X)
  close-f = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x f) ⁻¹)
  close-g = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x g) ⁻¹)

  abstract
    beta-square : (βg ∙ funUncurryIso δ) =₂ ((funEval ◁ image) ∙ βf)
    beta-square = cancel-inverse βg ((funEval ◁ image) ∙ βf) ∙
      isoComp-cong (idIso βg) (preCong-β α)

    restricted-beta : ((βg ▷ i) ∙ (funUncurryIso δ ▷ i)) =₂
      (((funEval ◁ image) ▷ i) ∙ (βf ▷ i))
    restricted-beta = preWhisker-isoComp-at (funEval ◁ image) βf i ∙
      ((preWhisker i ◁ beta-square) ∙ (preWhisker-isoComp-at βg (funUncurryIso δ) i) ⁻¹)

    curried-square :
      (((βg ▷ i) ∙ evaluate-uncurry x (funPre g)) ∙ (evaluate x ◁ δ)) =₂
      (((funEval ◁ image) ▷ i) ∙ ((βf ▷ i) ∙ evaluate-uncurry x (funPre f)))
    curried-square = paste-squares
      (evaluate-uncurry x (funPre f)) (evaluate-uncurry x (funPre g))
      (βf ▷ i) (βg ▷ i) (evaluate x ◁ δ) (funUncurryIso δ ▷ i)
      ((funEval ◁ image) ▷ i) (Evaluation.natural x δ) restricted-beta

    associated-square :
      ((comp-assoc i G funEval ∙ ((βg ▷ i) ∙ evaluate-uncurry x (funPre g))) ∙ (evaluate x ◁ δ)) =₂
      ((funEval ◁ (image ▷ i)) ∙
        (comp-assoc i F funEval ∙ ((βf ▷ i) ∙ evaluate-uncurry x (funPre f))))
    associated-square = paste-squares
      ((βf ▷ i) ∙ evaluate-uncurry x (funPre f))
      ((βg ▷ i) ∙ evaluate-uncurry x (funPre g))
      (comp-assoc i F funEval) (comp-assoc i G funEval)
      (evaluate x ◁ δ) ((funEval ◁ image) ▷ i) (funEval ◁ (image ▷ i))
      curried-square (whisker-mixed-at image i funEval)

    first-coordinate : (comp-unitˡ (id X) ∙ (idIso (id X) ▷ id X)) =₂
      (idIso (id X) ∙ comp-unitˡ (id X))
    first-coordinate = (isoComp-unitˡ-at (comp-unitˡ (id X))) ⁻¹ ∙
      (isoComp-unitʳ-at (comp-unitˡ (id X)) ∙
        isoComp-cong (idIso (comp-unitˡ (id X))) (preWhisker-idIso (id X) (id X)))

    second-coordinate :
      ((comp-assoc (terminate X) x g) ⁻¹ ∙ (α ▷ const x)) =₂
      ((((α ▷ x) ▷ terminate X)) ∙ (comp-assoc (terminate X) x f) ⁻¹)
    second-coordinate = move-square (comp-assoc (terminate X) x g)
      ((α ▷ x) ▷ terminate X) (α ▷ const x) (comp-assoc (terminate X) x f)
      (preWhisker-comp-at α x (terminate X))

    insertion-square :
      ((close-g ∙ productMap-pair (id X) g (id X) (const x)) ∙ (image ▷ i)) =₂
      (final-image ∙ (close-f ∙ productMap-pair (id X) f (id X) (const x)))
    insertion-square = paste-squares
      (productMap-pair (id X) f (id X) (const x))
      (productMap-pair (id X) g (id X) (const x)) close-f close-g
      (image ▷ i) pair-image final-image
      (product-pair-natural (idIso (id X)) α (id X) (const x))
      (pair-square (comp-unitˡ (id X)) (comp-unitˡ (id X))
        ((comp-assoc (terminate X) x f) ⁻¹) ((comp-assoc (terminate X) x g) ⁻¹)
        _ _ _ _ first-coordinate second-coordinate)

    natural : (evaluate-pre {C = C} g x ∙ (evaluate x ◁ preCong α)) =₂
      (evaluate-cong (α ▷ x) ∙ evaluate-pre f x)
    natural = paste-squares
      (comp-assoc i F funEval ∙ ((βf ▷ i) ∙ evaluate-uncurry x (funPre f)))
      (comp-assoc i G funEval ∙ ((βg ▷ i) ∙ evaluate-uncurry x (funPre g)))
      (funEval ◁ (close-f ∙ productMap-pair (id X) f (id X) (const x)))
      (funEval ◁ (close-g ∙ productMap-pair (id X) g (id X) (const x)))
      (evaluate x ◁ δ) (funEval ◁ (image ▷ i)) (funEval ◁ final-image)
      associated-square
      (post-square funEval _ _ _ _ insertion-square)
```


The terminal-domain evaluation comparison is natural in the chosen absolute
object. This will convert restriction cones into the endpoint cones used
by the Segal construction, without changing their specified matchings.

```agda
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at)

module PointBoundary (C : CAT) where
  point-evaluation : MAP (Fun One C) C
  point-evaluation = evaluate (id One)

  boundary : {A : CAT} (x : Obj-abs A) →
    (point-evaluation ∘ funPre x) =₁ (evaluate x)
  boundary x = evaluate-cong (comp-unitʳ x) ∙ evaluate-pre x (id One)

  abstract
    boundary-natural : {A : CAT} {x y : Obj-abs A} (α : x =₁ y) →
      (boundary y ∙ (point-evaluation ◁ preCong α)) =₂
        (evaluate-cong α ∙ boundary x)
    boundary-natural {x = x} {y} α = paste-squares
      (evaluate-pre x (id One)) (evaluate-pre y (id One))
      (evaluate-cong (comp-unitʳ x)) (evaluate-cong (comp-unitʳ y))
      (point-evaluation ◁ preCong α) (evaluate-cong (α ▷ id One))
      (evaluate-cong α)
      (Restriction.natural {C = C} α (id One))
      (evaluate-cong-comp α (comp-unitʳ x) ∙
        (evaluate-cong-Iso₂ (preWhisker-id-at α) ∙
          (evaluate-cong-comp (comp-unitʳ y) (α ▷ id One)) ⁻¹))
```
