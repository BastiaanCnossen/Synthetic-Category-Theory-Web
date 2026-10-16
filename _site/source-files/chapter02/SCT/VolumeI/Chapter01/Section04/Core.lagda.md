# The core anima and its universal property

Core C is Map One C; its canonical inclusion evaluates after insertion of
the terminal right factor. The universal property follows by double
uncurrying and the terminal-product equivalence, within this section.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Core where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors using (functor-over)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Points
open import SCT.VolumeI.Chapter01.Section04.Functoriality
open import SCT.VolumeI.Chapter01.Section04.Uncurrying
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection
  using (post-tests-animae)

module _ {Γ : Context} where
  Core : CAT Γ → CAT Γ
  Core C = Map One C

  core-isAn : (C : CAT Γ) → isAn (Core C)
  core-isAn C = map-isAn One C

  coreInclusion : (C : CAT Γ) → MAP (Core C) C
  coreInclusion C = mapEval ∘ product-unitʳ-inverse (Core C)

  core-evaluation : {X C : CAT Γ} (f : MAP X (Core C))
    → (uncurry f ∘ product-unitʳ-inverse X) =₁ (coreInclusion C ∘ f)
  core-evaluation {X} {C} f =
    (comp-assoc f (product-unitʳ-inverse (Core C)) mapEval) ⁻¹ ∙
    ((mapEval ◁ product-unitʳ-inverse-natural f) ∙
      comp-assoc (product-unitʳ-inverse X) (productMap f (id One)) mapEval)

  module Universality (X C : CAT Γ) where
    private
      N : CAT Γ
      N = Map X (Core C)

      insert : MAP (N × X) ((N × X) × One)
      insert = product-unitʳ-inverse (N × X)

      change : MAP (N × X) (N × (X × One))
      change = productMap (id N) (product-unitʳ-inverse X)

      first : (pr₁ ∘ change) =₁ pr₁
      first = comp-unitˡ pr₁ ∙ pair-β₁ (id N ∘ pr₁) (product-unitʳ-inverse X ∘ pr₂)

      second : ((pr₁ ∘ pr₂) ∘ change) =₁ pr₂
      second = comp-unitˡ pr₂ ∙
        ((pair-β₁ (id X) (terminate X) ▷ pr₂) ∙
        ((comp-assoc pr₂ (product-unitʳ-inverse X) pr₁) ⁻¹ ∙
        ((pr₁ ◁ pair-β₂ (id N ∘ pr₁) (product-unitʳ-inverse X ∘ pr₂)) ∙
          comp-assoc change pr₂ pr₁)))

      regroup-insert : (Associativity.backward N X One ∘ change) =₁ insert
      regroup-insert = pair₌
        ((pair-β₁ (id (N × X)) (terminate (N × X))) ⁻¹ ∙
        (pair-projections ∙
        (pair⁼ first second ∙
        (pair-pre pr₁ (pr₁ ∘ pr₂) change ∙
          project-pair₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) change))))
        (terminal-identification _ _)

    uncurrying-route : MAP (Map X (Core C)) (Map X C)
    uncurrying-route = mapPre (product-unitʳ-inverse X) ∘ mapUncurrying X One C

    route-is-postcomposition : uncurrying-route =₁ (mapPost (coreInclusion C))
    route-is-postcomposition = uncurry-reflect (map-isAn X (Core C)) _ _
      ((mapPost-β (coreInclusion C)) ⁻¹ ∙
      (core-evaluation (mapEval {C = X} {D = Core C}) ∙
      ((uncurry (mapEval {C = X} {D = Core C}) ◁ regroup-insert) ∙
      (comp-assoc (productMap (id N) (product-unitʳ-inverse X))
        (Associativity.backward N X One) (uncurry (mapEval {C = X} {D = Core C})) ∙
      ((ExponentialLaw.forward-β X One C ▷ productMap (id N) (product-unitʳ-inverse X)) ∙
        mapPre-uncurry (product-unitʳ-inverse X) (mapUncurrying X One C))))))

    module _ (xAn : isAn X) where
      postcomposition-isEquiv : IsEquiv (mapPost (coreInclusion C))
      postcomposition-isEquiv = equiv-transport route-is-postcomposition
        (equiv-compose (mapUncurrying X One C) (mapPre (product-unitʳ-inverse X))
          (mapUncurrying-isEquiv X One C xAn)
          (mapPre-isEquiv (product-unitʳ-inverse X) (equiv-inverse (product-unitʳ-isEquiv X))))


  core-universal : (X C : CAT Γ) → isAn X → IsEquiv (mapPost {C = X} (coreInclusion C))
  core-universal = Universality.postcomposition-isEquiv

  factor-through-core : {X C : CAT Γ} (xAn : isAn X) (f : MAP X C)
    → Factorization (coreInclusion C) f
  factor-through-core {X} {C} xAn f = functor-over decoded-factor
    (name-reflect (coreInclusion C ∘ decoded-factor) f (triangle chosen ∙
      ((mapPost (coreInclusion C) ◁ name-decode point) ∙
        (mapPost-name (coreInclusion C) decoded-factor) ⁻¹)))
    where
    chosen : Factorization (mapPost (coreInclusion C)) (name f)
    chosen = factor-through-equiv (core-universal X C xAn) (name f)
    point : Obj-abs (Map X (Core C))
    point = factor chosen
    decoded-factor : MAP X (Core C)
    decoded-factor = decode point

  core-of-anima : (C : CAT Γ) → isAn C → IsEquiv (coreInclusion C)
  core-of-anima C cAn = post-tests-animae (core-isAn C) cAn
    (coreInclusion C) (λ X xAn → core-universal X C xAn)
```

## The core inclusion of an anima

Currying the first projection gives an explicit inverse to the core
inclusion. Beta gives one inverse comparison; reflection through the
core equivalence supplies the other.

```agda
module _ {Γ : Context} where
  module AnimaCoreEquivalence (A : CAT Γ) (aAn : isAn A) where
    forward : MAP A (Map One A)
    forward = mapCurry aAn pr₁

    backward : MAP (Map One A) A
    backward = coreInclusion A

    forward-β : (uncurry forward) =₁ pr₁
    forward-β = mapCurry-β aAn pr₁
```

The inverse calculations retain the chosen beta comparison.

```agda
    backward-forward : (backward ∘ forward) =₁ (id A)
    backward-forward = pair-β₁ (id A) (terminate A) ∙
      ((forward-β ▷ product-unitʳ-inverse A) ∙
      ((comp-assoc (product-unitʳ-inverse A) (productMap forward (id One)) mapEval) ⁻¹ ∙
      ((mapEval ◁ (product-unitʳ-inverse-natural forward) ⁻¹) ∙
        comp-assoc forward (product-unitʳ-inverse (Map One A)) mapEval)))

    backward-isEquiv : IsEquiv backward
    backward-isEquiv = core-of-anima A aAn

    forward-backward : (forward ∘ backward) =₁ (id (Map One A))
    forward-backward = equiv-reflect backward-isEquiv _ _
      ((comp-unitʳ backward) ⁻¹ ∙
        (comp-unitˡ backward ∙
          ((backward-forward ▷ backward) ∙ (comp-assoc backward forward backward) ⁻¹)))

    forward-backward-uncurried : (uncurry (forward ∘ backward)) =₁ mapEval
    forward-backward-uncurried = uncurry-id One A ∙ uncurry⁼ forward-backward

    forward-isEquiv : IsEquiv forward
    forward-isEquiv = record
      { inverse = backward
      ; left-inverse-law = backward-forward ⁻¹
      ; right-inverse-law = forward-backward ⁻¹
      }
```
