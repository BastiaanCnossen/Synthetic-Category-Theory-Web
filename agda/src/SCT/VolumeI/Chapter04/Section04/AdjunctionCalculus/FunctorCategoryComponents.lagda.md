# Units and counits on functor categories

For postcomposition, evaluate the original unit and counit at the
universal functor and curry them. For precomposition, pair each component
with the fixed functor coordinate and evaluate. This gives the direction
`r* : Fun(C,K) → Fun(D,K)` for the left adjoint to `l*`.

The precomposition endpoint comparisons use the explicit evaluated product
route, retaining the computation rule needed for their coherence.

These are the specified unit and counit constructions for
`prop:Adjunction_On_Functor_Categories`. The triangle identities are a
separate obligation, so this module does not yet construct an adjunction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I
  using (pair-expression)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData as Data

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (A : Adjunction l r) (K : CAT) where
  module A = Adjunction A

  module Postcomposition where
    left : MAP (Fun K C) (Fun K D)
    left = funPost l
    right : MAP (Fun K D) (Fun K C)
    right = funPost r

    unit-target : funUncurry (right ∘ left) =₁ (r ∘ (l ∘ funEval))
    unit-target = (r ◁ funPost-β l) ∙ funPost-uncurry r left
    counit-source : funUncurry (left ∘ right) =₁ (l ∘ (r ∘ funEval))
    counit-source = (l ◁ funPost-β r) ∙ funPost-uncurry l right

    unit-diagram : MorphismExpression (funUncurry (id (Fun K C))) (funUncurry (right ∘ left))
    unit-diagram = retarget-expression (A.unit-at funEval)
      ((funUncurry-id K C) ⁻¹) (unit-target ⁻¹)
    counit-diagram : MorphismExpression (funUncurry (left ∘ right)) (funUncurry (id (Fun K D)))
    counit-diagram = retarget-expression (A.counit-at funEval)
      (counit-source ⁻¹) ((funUncurry-id K D) ⁻¹)

    module Unit = Currying.Curry 𝒯 M ℱ I (id (Fun K C)) (right ∘ left) unit-diagram
    module Counit = Currying.Curry 𝒯 M ℱ I (left ∘ right) (id (Fun K D)) counit-diagram
    unit : MorphismExpression (id (Fun K C)) (right ∘ left)
    unit = Unit.value
    counit : MorphismExpression (left ∘ right) (id (Fun K D))
    counit = Counit.value
    module Components = Data.Data 𝒯 M ℱ P I E S left right unit counit

  module Precomposition where
    left : MAP (Fun C K) (Fun D K)
    left = funPre {D = K} r
    right : MAP (Fun D K) (Fun C K)
    right = funPre {D = K} l

    composite-evaluation : {X Y Z : CAT} (f : MAP X Y) (g : MAP Y Z) →
      funUncurry (funPre {D = K} f ∘ funPre {D = K} g) =₁
        (funEval ∘ productMap (id (Fun Z K)) (g ∘ f))
    composite-evaluation {Z = Z} f g =
      (funEval ◁ (productMap-cong (comp-unitˡ (id (Fun Z K))) (idIso (g ∘ f)) ∙
        productMap-comp (id (Fun Z K)) (id (Fun Z K)) f g)) ∙
      (comp-assoc (productMap (id (Fun Z K)) f) (productMap (id (Fun Z K)) g) funEval ∙
        ((funPre-β {D = K} g ▷ productMap (id (Fun Z K)) f) ∙
          funPre-uncurry f (funPre {D = K} g)))
    unit-target : funUncurry (right ∘ left) =₁
      (funEval ∘ pair pr₁ (r ∘ (l ∘ pr₂)))
    unit-target = (funEval ◁ pair-cong (comp-unitˡ pr₁) (comp-assoc pr₂ l r)) ∙
      composite-evaluation l r
    counit-source : funUncurry (left ∘ right) =₁
      (funEval ∘ pair pr₁ (l ∘ (r ∘ pr₂)))
    counit-source = (funEval ◁ pair-cong (comp-unitˡ pr₁) (comp-assoc pr₂ r l)) ∙
      composite-evaluation r l

    evaluation-identity : (X : CAT) →
      (funEval ∘ pair (pr₁ {Fun X K} {X}) pr₂) =₁ funUncurry (id (Fun X K))
    evaluation-identity X = (funUncurry-id X K) ⁻¹ ∙
      (comp-unitʳ funEval ∙ (funEval ◁ pair-projections))

    unit-diagram : MorphismExpression (funUncurry (id (Fun C K))) (funUncurry (right ∘ left))
    unit-diagram = retarget-expression
      (post-expression funEval (pair-expression (identity-expression pr₁) (A.unit-at pr₂)))
      (evaluation-identity C) (unit-target ⁻¹)
    counit-diagram : MorphismExpression (funUncurry (left ∘ right)) (funUncurry (id (Fun D K)))
    counit-diagram = retarget-expression
      (post-expression funEval (pair-expression (identity-expression pr₁) (A.counit-at pr₂)))
      (counit-source ⁻¹) (evaluation-identity D)

    module Unit = Currying.Curry 𝒯 M ℱ I (id (Fun C K)) (right ∘ left) unit-diagram
    module Counit = Currying.Curry 𝒯 M ℱ I (left ∘ right) (id (Fun D K)) counit-diagram
    unit : MorphismExpression (id (Fun C K)) (right ∘ left)
    unit = Unit.value
    counit : MorphismExpression (left ∘ right) (id (Fun D K))
    counit = Counit.value
    module Components = Data.Data 𝒯 M ℱ P I E S left right unit counit
```

