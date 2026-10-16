# Functor categories of groupoids

The native exponential comparisons identify constant diagrams after exchanging
the two diagram variables. Both evaluations retain their specified beta
triangles. Their argument maps agree by the two product projections.
Specializing the constant variable to the walking morphism proves closure
of groupoids under functor categories, for arbitrary source category.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.FunctorGroupoids where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; swap; swap-isEquiv; module Associativity)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPost; funPost-β; funPost-isEquiv; funPre; funPre-uncurry; funPre-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw using (module ExponentialLaw)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (constantArrow; constantArrow-image; identityArrow)
open import SCT.VolumeI.Chapter02.Section04.Groupoids using (IsGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure using (constant-evaluation)

module _ {Γ : Context} where
  constant-exchange-arguments : (N I K : CAT Γ)
    → (productMap (pr₁ {C = N} {D = I}) (id K) ∘
        (Associativity.backward N I K ∘ productMap (id N) (swap {C = K} {D = I})))
      =₁ (pr₁ ∘ Associativity.backward N K I)
  constant-exchange-arguments N I K = pair₌ (right-first ⁻¹ ∙ left-first)
    (right-second ⁻¹ ∙ left-second)
    where
      s : MAP (N × (K × I)) (N × (I × K))
      s = productMap (id N) (swap {C = K} {D = I})
      b : MAP (N × (I × K)) ((N × I) × K)
      b = Associativity.backward N I K
      r : MAP (N × (K × I)) ((N × K) × I)
      r = Associativity.backward N K I

      left-first : (pr₁ ∘ (productMap (pr₁ {C = N} {D = I}) (id K) ∘ (b ∘ s))) =₁ pr₁
      left-first = comp-unitˡ pr₁ ∙
        (pair-β₁ (id N ∘ pr₁) (swap ∘ pr₂) ∙
          ((Associativity.backward-first N I K ▷ s) ∙
            ((comp-assoc s b (pr₁ ∘ pr₁)) ⁻¹ ∙
              project-pair₁ (pr₁ ∘ pr₁) (id K ∘ pr₂) (b ∘ s))))

      right-first : (pr₁ ∘ (pr₁ ∘ r)) =₁ pr₁
      right-first = Associativity.backward-first N K I ∙ (comp-assoc r pr₁ pr₁) ⁻¹

      left-second : (pr₂ ∘ (productMap (pr₁ {C = N} {D = I}) (id K) ∘ (b ∘ s)))
        =₁ (pr₁ ∘ (pr₂ {C = N} {D = K × I}))
      left-second = (pair-β₂ pr₂ pr₁ ▷ pr₂) ∙
        ((comp-assoc pr₂ swap pr₂) ⁻¹ ∙
          ((pr₂ ◁ pair-β₂ (id N ∘ pr₁) (swap ∘ pr₂)) ∙
            (comp-assoc s pr₂ pr₂ ∙
              ((Associativity.backward-third N I K ▷ s) ∙
                ((comp-assoc s b pr₂) ⁻¹ ∙
                  ((comp-unitˡ pr₂ ▷ (b ∘ s)) ∙
                    project-pair₂ (pr₁ ∘ pr₁) (id K ∘ pr₂) (b ∘ s)))))))

      right-second : (pr₂ ∘ (pr₁ ∘ r)) =₁ (pr₁ ∘ (pr₂ {C = N} {D = K × I}))
      right-second = Associativity.backward-second N K I ∙ (comp-assoc r pr₁ pr₂) ⁻¹

  constant-exponential : (I K X : CAT Γ)
    → (funPre {D = X} (swap {C = K} {D = I}) ∘
        (ExponentialLaw.forward I K X ∘ constantArrow I (Fun K X)))
      =₁ (ExponentialLaw.forward K I X ∘ funPost {C = K} (constantArrow I X))
  constant-exponential I K X = reflect (funEval {C = K × I} {D = X})
    (funUniversal (K × I) X) left-functor right-functor (right ⁻¹ ∙ ((eK ◁ arguments) ∙ left))
    where
      N : CAT Γ
      N = Fun K X
      eK : MAP (N × K) X
      eK = funEval {C = K} {D = X}
      s : MAP (N × (K × I)) (N × (I × K))
      s = productMap (id N) (swap {C = K} {D = I})
      b : MAP (N × (I × K)) ((N × I) × K)
      b = Associativity.backward N I K
      r : MAP (N × (K × I)) ((N × K) × I)
      r = Associativity.backward N K I
      d : MAP ((N × I) × K) (N × K)
      d = productMap (pr₁ {C = N} {D = I}) (id K)

      left-functor : MAP N (Fun (K × I) X)
      left-functor = funPre {D = X} (swap {C = K} {D = I}) ∘
        (ExponentialLaw.forward I K X ∘ constantArrow I N)
      right-functor : MAP N (Fun (K × I) X)
      right-functor = ExponentialLaw.forward K I X ∘ funPost {C = K} (constantArrow I X)

      arguments : (d ∘ (b ∘ s)) =₁ (pr₁ ∘ r)
      arguments = constant-exchange-arguments N I K

      left : funUncurry {C = K × I} {D = X} left-functor =₁ (eK ∘ (d ∘ (b ∘ s)))
      left = comp-assoc (b ∘ s) d eK ∙
        (comp-assoc s b (eK ∘ d) ∙
          (((evaluate-cong eK (constantArrow-image I N) ▷ b) ▷ s) ∙
            ((ExponentialLaw.forward-represents I K X (constantArrow I N) ▷ s) ∙
              funPre-uncurry (swap {C = K} {D = I})
                (ExponentialLaw.forward I K X ∘ constantArrow I N))))

      right : funUncurry {C = K × I} {D = X} right-functor =₁ (eK ∘ (pr₁ ∘ r))
      right = comp-assoc r pr₁ eK ∙
        ((constant-evaluation I X eK ▷ r) ∙
          ((evaluate-cong (funEval {C = I} {D = X})
              (funPost-β {C = K} (constantArrow I X)) ▷ r) ∙
            ExponentialLaw.forward-represents K I X (funPost {C = K} (constantArrow I X))))

  functor-isGroupoid : (K : CAT Γ) {X : CAT Γ} → IsGroupoid X → IsGroupoid (Fun K X)
  functor-isGroupoid K {X} given =
    equiv-cancel-left (identityArrow {C = Fun K X}) (ExponentialLaw.forward [1] K X)
      (ExponentialLaw.forward-isEquiv [1] K X)
      (equiv-cancel-left (ExponentialLaw.forward [1] K X ∘ identityArrow {C = Fun K X})
        (funPre {D = X} (swap {C = K} {D = [1]}))
        (funPre-isEquiv {E = X} (swap {C = K} {D = [1]}) (swap-isEquiv K [1]))
        (equiv-transport ((constant-exponential [1] K X) ⁻¹)
          (equiv-compose (funPost {C = K} (identityArrow {C = X}))
            (ExponentialLaw.forward K [1] X)
            (funPost-isEquiv {A = K} (identityArrow {C = X}) given)
            (ExponentialLaw.forward-isEquiv K [1] X))))
```
