# Constant diagrams: naturality and exponentials

Under the exponential law and interchange of the two diagram variables,
the constant-diagram functor on `Fun C X` is postcomposition with the
constant-diagram functor on `X`. The calculation below proves this for
the actual functors, by uncurrying and comparing product projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ

projection-after : {W A B D : CAT} (h : MAP A B) (π : MAP B D)
  {p : MAP A D} → (π ∘ h) =₁ p → (k : MAP W A) → (π ∘ (h ∘ k)) =₁ (p ∘ k)
projection-after h π β k = (β ▷ k) ∙ (comp-assoc k h π) ⁻¹

module Constant (T C X : CAT) where
  N = Fun C X
  module First = ExponentialLaw T C X
  module Second = ExponentialLaw C T X
  module TC = Associativity N T C
  module CT = Associativity N C T
  exchange : MAP (N × (C × T)) (N × (T × C))
  exchange = productMap (id N) (swap {C} {T})
  drop : MAP ((N × T) × C) (N × C)
  drop = productMap pr₁ (id C)
  left-argument = drop ∘ (TC.backward ∘ exchange)
  right-argument = pr₁ ∘ CT.backward

  first-coordinate : (pr₁ ∘ left-argument) =₁ (pr₁ {N} {C × T})
  first-coordinate = comp-unitˡ pr₁ ∙
    (pair-β₁ (id N ∘ pr₁) (swap ∘ pr₂) ∙
    (projection-after TC.backward (pr₁ ∘ pr₁) TC.backward-first exchange ∙
      projection-after drop pr₁ (pair-β₁ (pr₁ ∘ pr₁) (id C ∘ pr₂)) (TC.backward ∘ exchange)))

  second-coordinate : (pr₂ ∘ left-argument) =₁ (pr₁ ∘ pr₂ {N} {C × T})
  second-coordinate = projection-after swap pr₂ (pair-β₂ pr₂ pr₁) pr₂ ∙
    ((pr₂ ◁ pair-β₂ (id N ∘ pr₁) (swap ∘ pr₂)) ∙
    (comp-assoc exchange pr₂ pr₂ ∙
    (projection-after TC.backward pr₂ (pair-β₂ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) exchange ∙
      projection-after drop pr₂ (comp-unitˡ pr₂ ∙ pair-β₂ (pr₁ ∘ pr₁) (id C ∘ pr₂))
        (TC.backward ∘ exchange))))

  argument-comparison : left-argument =₁ right-argument
  argument-comparison = (pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ⁻¹ ∙
    pair-iso ((pair-β₁ pr₁ (pr₁ ∘ pr₂)) ⁻¹ ∙ first-coordinate)
      ((pair-β₂ pr₁ (pr₁ ∘ pr₂)) ⁻¹ ∙ second-coordinate)

  left-map = funPre (swap {C} {T}) ∘ (First.forward ∘ constantDiagram T N)
  right-map = Second.forward ∘ funPost (constantDiagram T X)

  left-double : (First.doubleUncurry (constantDiagram T N)) =₁ (funEval ∘ drop)
  left-double = funUncurry-cong (funCurry-β pr₁)

  left-evaluation : (funUncurry left-map) =₁ (funEval ∘ left-argument)
  left-evaluation = comp-assoc (TC.backward ∘ exchange) drop funEval ∙
    (comp-assoc exchange TC.backward (funEval ∘ drop) ∙
    (((left-double ▷ TC.backward) ▷ exchange) ∙
    ((First.forward-represents (constantDiagram T N) ▷ exchange) ∙
      funPre-uncurry swap (First.forward ∘ constantDiagram T N))))

  right-double : (Second.doubleUncurry (funPost (constantDiagram T X))) =₁ (funEval ∘ pr₁)
  right-double = pair-β₁ (funEval ∘ pr₁) (id T ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap funEval (id T)) ∙
    (funUncurry-restrict (constantDiagram T X) funEval ∙
      funUncurry-cong (funPost-β (constantDiagram T X))))

  right-evaluation : (funUncurry right-map) =₁ (funEval ∘ right-argument)
  right-evaluation = comp-assoc CT.backward pr₁ funEval ∙
    ((right-double ▷ CT.backward) ∙ Second.forward-represents (funPost (constantDiagram T X)))

  comparison : left-map =₁ right-map
  comparison = funReflect _ _
    (right-evaluation ⁻¹ ∙ ((funEval ◁ argument-comparison) ∙ left-evaluation))

  preserves-equivalence : IsEquiv (constantDiagram T X) → IsEquiv (constantDiagram T N)
  preserves-equivalence e = equiv-cancel-left (constantDiagram T N) First.forward First.forward-isEquiv
    (equiv-cancel-left (First.forward ∘ constantDiagram T N) (funPre swap)
      (funPre-isEquiv swap (swap-isEquiv C T))
      (equiv-transport (comparison ⁻¹)
        (equiv-compose (funPost (constantDiagram T X)) Second.forward (funPost-isEquiv _ e) Second.forward-isEquiv)))
```

## Naturality of constant diagrams

```agda
constant-natural : (T : CAT) {C D : CAT} (f : MAP C D) →
  (funPost f ∘ constantDiagram T C) =₁ (constantDiagram T D ∘ f)
constant-natural T {C} {D} f = funReflect _ _ (right ⁻¹ ∙ left)
  where
  left : (funUncurry (funPost f ∘ constantDiagram T C)) =₁ (f ∘ pr₁)
  left = (f ◁ funCurry-β pr₁) ∙ funPost-uncurry f (constantDiagram T C)
  right : (funUncurry (constantDiagram T D ∘ f)) =₁ (f ∘ pr₁)
  right = pair-β₁ (f ∘ pr₁) (id T ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap f (id T)) ∙
      funUncurry-restrict (constantDiagram T D) f)
```
