# Functors out of a coproduct

Distributivity combines the two indexed evaluations. Currying that
combination constructs the inverse of the actual pair of restriction
functors (`lem:Functors_Out_Of_Coproduct`). Recovery uses the established
whole identification-restriction equivalence, with its prescribed matching
equation, rather than reconstructing a summand reflection calculation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.CoproductDomain where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-inverse)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-preWhisker)
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing
open import SCT.VolumeI.Chapter01.Section05.IdentificationRestriction
open import SCT.VolumeI.Chapter01.Section06.Distributivity
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality

module CoproductDomain {Γ : Context} (C D E : CAT Γ) where
  private
    eC : MAP (Fun C E × C) E
    eC = funEval {C = C} {D = E}
    eD : MAP (Fun D E × D) E
    eD = funEval {C = D} {D = E}
    eSum : MAP (Fun (C ⊔ D) E × (C ⊔ D)) E
    eSum = funEval {C = C ⊔ D} {D = E}

  leftIn : (T : CAT Γ) → MAP (T × C) (T × (C ⊔ D))
  leftIn T = productMap (id T) in₁
  rightIn : (T : CAT Γ) → MAP (T × D) (T × (C ⊔ D))
  rightIn T = productMap (id T) in₂

  undistribute : (T : CAT Γ) → MAP (T × (C ⊔ D)) ((T × C) ⊔ (T × D))
  undistribute T = IsEquiv.inverse (Distributivity.distribute-isEquiv T C D)

  undistribute-left : (T : CAT Γ) → (undistribute T ∘ leftIn T) =₁ in₁
  undistribute-left T = comp-unitˡ in₁ ∙
    (((IsEquiv.left-inverse-law (Distributivity.distribute-isEquiv T C D)) ⁻¹ ▷ in₁) ∙
      ((comp-assoc in₁ (Distributivity.distribute T C D) (undistribute T)) ⁻¹ ∙
        (undistribute T ◁ (copair-β₁ (leftIn T) (rightIn T)) ⁻¹)))

  undistribute-right : (T : CAT Γ) → (undistribute T ∘ rightIn T) =₁ in₂
  undistribute-right T = comp-unitˡ in₂ ∙
    (((IsEquiv.left-inverse-law (Distributivity.distribute-isEquiv T C D)) ⁻¹ ▷ in₂) ∙
      ((comp-assoc in₂ (Distributivity.distribute T C D) (undistribute T)) ⁻¹ ∙
        (undistribute T ◁ (copair-β₂ (leftIn T) (rightIn T)) ⁻¹)))

  combinedEvaluation : {T : CAT Γ} → MAP T (Fun C E) → MAP T (Fun D E) → MAP (T × (C ⊔ D)) E
  combinedEvaluation {T} f g = copair (evaluate eC f) (evaluate eD g) ∘ undistribute T

  funCopair : {T : CAT Γ} → MAP T (Fun C E) → MAP T (Fun D E) → MAP T (Fun (C ⊔ D) E)
  funCopair f g = funCurry {C = C ⊔ D} {D = E} (combinedEvaluation f g)

  funCopair-β : {T : CAT Γ} (f : MAP T (Fun C E)) (g : MAP T (Fun D E))
    → evaluate eSum (funCopair f g) =₁ combinedEvaluation f g
  funCopair-β f g = funCurry-β {C = C ⊔ D} {D = E} (combinedEvaluation f g)

  module _ {X T : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    funCopair⁼ : {f f′ : MAP T (Fun C E)} {g g′ : MAP T (Fun D E)}
      → f ＝ f′ → g ＝ g′ → funCopair f g ＝ funCopair f′ g′
    funCopair⁼ α β = curry⁼ eSum (funUniversal (C ⊔ D) E)
      (copair-cong (evaluate⁼ eC α) (evaluate⁼ eD β) ▷ undistribute T)

    funCopair⁼-evaluation : {f f′ : MAP T (Fun C E)} {g g′ : MAP T (Fun D E)}
      (α : f ＝ f′) (β : g ＝ g′)
      → SquareCell₌ (evaluate⁼ eSum (funCopair⁼ α β))
          (copair-cong (evaluate⁼ eC α) (evaluate⁼ eD β) ▷ undistribute T)
          (const (funCopair-β f g)) (const (funCopair-β f′ g′))
    funCopair⁼-evaluation α β = curry⁼-evaluation eSum (funUniversal (C ⊔ D) E) _

  funCopair-left-evaluation : {T : CAT Γ} (f : MAP T (Fun C E)) (g : MAP T (Fun D E))
    → (evaluate eSum (funCopair f g) ∘ leftIn T) =₁ evaluate eC f
  funCopair-left-evaluation {T} f g = copair-β₁ (evaluate eC f) (evaluate eD g) ∙
    ((copair (evaluate eC f) (evaluate eD g) ◁ undistribute-left T) ∙
      (comp-assoc (leftIn T) (undistribute T) (copair (evaluate eC f) (evaluate eD g)) ∙
        (funCopair-β f g ▷ leftIn T)))

  funCopair-right-evaluation : {T : CAT Γ} (f : MAP T (Fun C E)) (g : MAP T (Fun D E))
    → (evaluate eSum (funCopair f g) ∘ rightIn T) =₁ evaluate eD g
  funCopair-right-evaluation {T} f g = copair-β₂ (evaluate eC f) (evaluate eD g) ∙
    ((copair (evaluate eC f) (evaluate eD g) ◁ undistribute-right T) ∙
      (comp-assoc (rightIn T) (undistribute T) (copair (evaluate eC f) (evaluate eD g)) ∙
        (funCopair-β f g ▷ rightIn T)))

  funCopair-left : {T : CAT Γ} (f : MAP T (Fun C E)) (g : MAP T (Fun D E))
    → (funPre {D = E} in₁ ∘ funCopair f g) =₁ f
  funCopair-left f g = reflect eC (funUniversal C E) _ _
    (funCopair-left-evaluation f g ∙ funPre-uncurry in₁ (funCopair f g))

  funCopair-right : {T : CAT Γ} (f : MAP T (Fun C E)) (g : MAP T (Fun D E))
    → (funPre {D = E} in₂ ∘ funCopair f g) =₁ g
  funCopair-right f g = reflect eD (funUniversal D E) _ _
    (funCopair-right-evaluation f g ∙ funPre-uncurry in₂ (funCopair f g))
```

## Recovery with the whole distributed matching

The family parameter is independent of `T`. Restriction to the two product
inclusions is transported to restriction along the two summands of the
distributed product. The existing recovery supplies their whole matching
equation; lifting along distributivity retains that equation.

```agda
  module EvaluationFromRestrictions {X T : CAT Γ} (h k : MAP (T × (C ⊔ D)) E)
    (α : MAP X (Equal (h ∘ leftIn T) (k ∘ leftIn T)))
    (β : MAP X (Equal (h ∘ rightIn T) (k ∘ rightIn T))) where
    open Terms.Equalities X using (_＝_)
    distribute = Distributivity.distribute T C D

    left-comparison : (l : MAP (T × (C ⊔ D)) E)
      → ((l ∘ distribute) ∘ in₁) =₁ (l ∘ leftIn T)
    left-comparison l = (l ◁ copair-β₁ (leftIn T) (rightIn T)) ∙ comp-assoc in₁ distribute l
    right-comparison : (l : MAP (T × (C ⊔ D)) E)
      → ((l ∘ distribute) ∘ in₂) =₁ (l ∘ rightIn T)
    right-comparison l = (l ◁ copair-β₂ (leftIn T) (rightIn T)) ∙ comp-assoc in₂ distribute l

    left-matching : ((h ∘ distribute) ∘ in₁) ＝ ((k ∘ distribute) ∘ in₁)
    left-matching = (const (left-comparison k)) ⁻¹ ∙ (α ∙ const (left-comparison h))
    right-matching : ((h ∘ distribute) ∘ in₂) ＝ ((k ∘ distribute) ∘ in₂)
    right-matching = (const (right-comparison k)) ⁻¹ ∙ (β ∙ const (right-comparison h))

    module I = IdentificationFromRestrictions (h ∘ distribute) (k ∘ distribute) left-matching right-matching
    chosen : Fact.Factorization (preWhisker distribute) I.identification
    chosen = factor-through-preWhisker distribute (Distributivity.distribute-isEquiv T C D) I.identification

    comparison : h ＝ k
    comparison = Fact.factor chosen

    at-distribute : (comparison ▷ distribute) =₁ I.identification
    at-distribute = Fact.triangle chosen

    whole-matching :
      (coproductRestriction₌ (h ∘ distribute) (k ∘ distribute) ∘ (comparison ▷ distribute)) =₁
        pair left-matching right-matching
    whole-matching = I.restriction-law ∙
      (coproductRestriction₌ (h ∘ distribute) (k ∘ distribute) ◁ at-distribute)

  module _ {X T : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    restricted-evaluation-comparison : (f g : MAP T (Fun (C ⊔ D) E))
      → (funPre {D = E} in₁ ∘ f) ＝ (funPre {D = E} in₁ ∘ g)
      → (funPre {D = E} in₂ ∘ f) ＝ (funPre {D = E} in₂ ∘ g)
      → evaluate eSum f ＝ evaluate eSum g
    restricted-evaluation-comparison f g α β = EvaluationFromRestrictions.comparison
      (evaluate eSum f) (evaluate eSum g)
      (const (funPre-uncurry in₁ g) ∙ (evaluate⁼ eC α ∙ (const (funPre-uncurry in₁ f)) ⁻¹))
      (const (funPre-uncurry in₂ g) ∙ (evaluate⁼ eD β ∙ (const (funPre-uncurry in₂ f)) ⁻¹))

    funRestriction-reflect : (f g : MAP T (Fun (C ⊔ D) E))
      → (funPre {D = E} in₁ ∘ f) ＝ (funPre {D = E} in₁ ∘ g)
      → (funPre {D = E} in₂ ∘ f) ＝ (funPre {D = E} in₂ ∘ g) → f ＝ g
    funRestriction-reflect f g α β = reflect eSum (funUniversal (C ⊔ D) E) f g
      (restricted-evaluation-comparison f g α β)

    funRestriction-reflect-image : (f g : MAP T (Fun (C ⊔ D) E))
      (α : (funPre {D = E} in₁ ∘ f) ＝ (funPre {D = E} in₁ ∘ g))
      (β : (funPre {D = E} in₂ ∘ f) ＝ (funPre {D = E} in₂ ∘ g))
      → evaluate⁼ eSum (funRestriction-reflect f g α β) =₁ restricted-evaluation-comparison f g α β
    funRestriction-reflect-image f g α β = reflect-β eSum (funUniversal (C ⊔ D) E) f g _
```

## The actual restriction comparison

The forward functor is the pair of the two specified precomposition
functors. Its inverse combines the two projections. Projection laws give
one inverse comparison; recovery from the two restrictions gives the other.

```agda
  Source = Fun (C ⊔ D) E
  Target = Fun C E × Fun D E
  private
    left : MAP Source (Fun C E)
    left = funPre {D = E} in₁
    right : MAP Source (Fun D E)
    right = funPre {D = E} in₂

  forward : MAP Source Target
  forward = pair left right
  backward : MAP Target Source
  backward = funCopair pr₁ pr₂

  forward-backward : (forward ∘ backward) =₁ id Target
  forward-backward = pair-projections ∙
    (pair⁼ (funCopair-left pr₁ pr₂) (funCopair-right pr₁ pr₂) ∙ pair-pre left right backward)

  backward-forward : (backward ∘ forward) =₁ id Source
  backward-forward = funRestriction-reflect _ _
    ((comp-unitʳ left) ⁻¹ ∙
      (pair-β₁ left right ∙ ((funCopair-left pr₁ pr₂ ▷ forward) ∙ (comp-assoc forward backward left) ⁻¹)))
    ((comp-unitʳ right) ⁻¹ ∙
      (pair-β₂ left right ∙ ((funCopair-right pr₁ pr₂ ▷ forward) ∙ (comp-assoc forward backward right) ⁻¹)))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; left-inverse-law = backward-forward ⁻¹
    ; right-inverse-law = forward-backward ⁻¹ }
```
