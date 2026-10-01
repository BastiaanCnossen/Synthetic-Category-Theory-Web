# Left and right fibrations over groupoids

For `prop:Left_Fibrations_Over_Groupoid`, the one-sided directed
pullback projection is a base change of endpoint evaluation in the base.
When the base is a groupoid this projection is an equivalence.
The two-out-of-three property reduces each fibration condition to the
corresponding endpoint evaluation of the total category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section02.GroupoidBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback-converse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

source-equivalence : {C : CAT} → IsGroupoid C → IsEquiv (ev₀ {C})
source-equivalence {C} e = equiv-cancel-right identityArrow ev₀ e
  (equiv-transport (identity-source ⁻¹) (id-isEquiv C))

target-equivalence : {C : CAT} → IsGroupoid C → IsEquiv (ev₁ {C})
target-equivalence {C} e = equiv-cancel-right identityArrow ev₁ e
  (equiv-transport (identity-target ⁻¹) (id-isEquiv C))

source-detects-groupoid : {C : CAT} → IsEquiv (ev₀ {C}) → IsGroupoid C
source-detects-groupoid {C} e = equiv-cancel-left identityArrow ev₀ e
  (equiv-transport (identity-source ⁻¹) (id-isEquiv C))

target-detects-groupoid : {C : CAT} → IsEquiv (ev₁ {C}) → IsGroupoid C
target-detects-groupoid {C} e = equiv-cancel-left identityArrow ev₁ e
  (equiv-transport (identity-target ⁻¹) (id-isEquiv C))

module OverGroupoid {A B : CAT} (f : MAP A B) (eB : IsGroupoid B) where
  open Evaluation f

  left-projection-equivalence : IsEquiv Left.left
  left-projection-equivalence = degenerate-pullback-converse
    (source-equivalence eB) (coneSwap (Source.square f))
    (pullback-swap (Source.square f) (Source.square-isPullback f))

  right-projection-equivalence : IsEquiv Right.right
  right-projection-equivalence = degenerate-pullback-converse
    (target-equivalence eB) (coneSwap (Target.square f))
    (pullback-swap (Target.square f) (Target.square-isPullback f))

  source-comparison : (Left.left ∘ directed-ev₀) =₁ ev₀
  source-comparison = pair-β₁ ev₀ (f ∘ ev₁) ∙
    ((pr₁ ◁ directed-ev₀-base) ∙ comp-assoc directed-ev₀ Left.base pr₁)

  target-comparison : (Right.right ∘ directed-ev₁) =₁ ev₁
  target-comparison = pair-β₂ (f ∘ ev₀) ev₁ ∙
    ((pr₂ ◁ directed-ev₁-base) ∙ comp-assoc directed-ev₁ Right.base pr₂)

  groupoid-to-left : IsGroupoid A → IsEquiv directed-ev₀
  groupoid-to-left eA = equiv-cancel-left directed-ev₀ Left.left left-projection-equivalence
    (equiv-transport (source-comparison ⁻¹) (source-equivalence eA))

  groupoid-to-right : IsGroupoid A → IsEquiv directed-ev₁
  groupoid-to-right eA = equiv-cancel-left directed-ev₁ Right.right right-projection-equivalence
    (equiv-transport (target-comparison ⁻¹) (target-equivalence eA))

  left-to-groupoid : IsEquiv directed-ev₀ → IsGroupoid A
  left-to-groupoid e = source-detects-groupoid
    (equiv-transport source-comparison
      (equiv-compose directed-ev₀ Left.left e left-projection-equivalence))

  right-to-groupoid : IsEquiv directed-ev₁ → IsGroupoid A
  right-to-groupoid e = target-detects-groupoid
    (equiv-transport target-comparison
      (equiv-compose directed-ev₁ Right.right e right-projection-equivalence))
```

The last two implications also give
`cor:Left_Fibration_Over_Groupoid_Is_Groupoid`.
The theorem uses the existing Chapter 2 definition of groupoid.

