# Functor categories and Bousfield localizations

Postcomposition preserves left and right adjoint sections, and hence
left and right Bousfield localizations. Invertibility is transported
through the chosen curried unit and counit, using their full inverse
equations rather than an objectwise criterion.

This proves `prop:Functor_Categories_And_Bousfield_Localizations`.

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

module SCT.VolumeI.Chapter04.Section04.FunctorCategoryLocalizations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S using (identified-invertible; retarget-invertible; restrict-invertible)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PostcompositionAdjunctions as Adjunctions
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryComponents as Components
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UncurryingInvertibility as Currying

module Postcomposition {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj using (unit; counit; unit-at; counit-at)
  module Chosen = Components.At 𝒯 M ℱ P I E S adj K using (module Postcomposition)
  module B = Chosen.Postcomposition using (left; right; unit-diagram; counit-diagram; unit-target; counit-source)
  module Result = Adjunctions.At 𝒯 M ℱ P I E S adj K using (value; unit-comparison; counit-comparison)

  abstract
    unit-invertible : IsInvertibleExpression A.unit → IsInvertibleExpression (Adjunction.unit Result.value)
    unit-invertible w = identified-invertible (expressionIso-inverse Result.unit-comparison)
      (Currying.Curry.value 𝒯 M ℱ P I E S (id (Fun K C)) (B.right ∘ B.left) B.unit-diagram
        (retarget-invertible (A.unit-at funEval) ((funUncurry-id K C) ⁻¹) (B.unit-target ⁻¹)
          (retarget-invertible (restrict-expression A.unit funEval)
            (comp-unitˡ funEval) (comp-assoc funEval l r) (restrict-invertible A.unit funEval w))))

    counit-invertible : IsInvertibleExpression A.counit → IsInvertibleExpression (Adjunction.counit Result.value)
    counit-invertible w = identified-invertible (expressionIso-inverse Result.counit-comparison)
      (Currying.Curry.value 𝒯 M ℱ P I E S (B.left ∘ B.right) (id (Fun K D)) B.counit-diagram
        (retarget-invertible (A.counit-at funEval) (B.counit-source ⁻¹) ((funUncurry-id K D) ⁻¹)
          (retarget-invertible (restrict-expression A.counit funEval)
            (comp-assoc funEval r l) (comp-unitˡ funEval) (restrict-invertible A.counit funEval w))))

post-left-adjoint-section : {C D : CAT} {f : MAP C D} {s : MAP D C} (K : CAT) →
  LeftAdjointSection f s → LeftAdjointSection (funPost {C = K} f) (funPost {C = K} s)
post-left-adjoint-section K w = record
  { adjunction = Result.Result.value
  ; unit-invertible = Result.unit-invertible W.unit-invertible }
  where
  module W = LeftAdjointSection w
  module Result = Postcomposition W.adjunction K using (module Result; unit-invertible; counit-invertible)

post-right-adjoint-section : {C D : CAT} {f : MAP C D} {s : MAP D C} (K : CAT) →
  RightAdjointSection f s → RightAdjointSection (funPost {C = K} f) (funPost {C = K} s)
post-right-adjoint-section K w = record
  { adjunction = Result.Result.value
  ; counit-invertible = Result.counit-invertible W.counit-invertible }
  where
  module W = RightAdjointSection w
  module Result = Postcomposition W.adjunction K using (module Result; unit-invertible; counit-invertible)

post-left-localization : {C D : CAT} {f : MAP C D} (K : CAT) →
  LeftBousfieldLocalization f → LeftBousfieldLocalization (funPost {C = K} f)
post-left-localization K w = record
  { section = funPost W.section
  ; right-adjoint-section = post-right-adjoint-section K W.right-adjoint-section }
  where module W = LeftBousfieldLocalization w

post-right-localization : {C D : CAT} {f : MAP C D} (K : CAT) →
  RightBousfieldLocalization f → RightBousfieldLocalization (funPost {C = K} f)
post-right-localization K w = record
  { section = funPost W.section
  ; left-adjoint-section = post-left-adjoint-section K W.left-adjoint-section }
  where module W = RightBousfieldLocalization w
```
