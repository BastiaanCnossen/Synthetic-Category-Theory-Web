# The universal family of functors over the base

Uncurrying the forgetful functor gives a family of functors whose
triangles commute over the base. Conversely, such a family determines
a functor into `FunOver`. This is the form of its defining pullback
used to construct base change.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost; funPost-uncurry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingAction 𝒯 M ℱ using (funUncurryIso)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

uncurry-constant-name : {X C S : CAT} (f : MAP C S) (u : MAP X One) →
  funUncurry (nameFun f ∘ u) =₁ (f ∘ pr₂)
uncurry-constant-name {C = C} f u =
  (f ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (u ∘ pr₁) (id C ∘ pr₂))) ∙
    (comp-assoc (productMap u (id C)) pr₂ f ∙
      ((funCurry-β (f ∘ pr₂) ▷ productMap u (id C)) ∙
        funUncurry-restrict (nameFun f) u))

module Evaluation {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  evaluate : MAP (FunOver f g × C) D
  evaluate = funUncurry (Over.forget f g)

  over : (g ∘ evaluate) =₁ (f ∘ pr₂)
  over = uncurry-constant-name f pullback₂ ∙
    (funUncurryIso (Over.matching f g) ∙
      (funPost-uncurry g (Over.forget f g)) ⁻¹)

module Curry {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (v : MAP (X × C) D) (over : (g ∘ v) =₁ (f ∘ pr₂)) where

  desired = over ∙ (g ◁ funCurry-β v)
  leftChange = funPost-uncurry g (funCurry v)
  rightChange = uncurry-constant-name f (terminate X)
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  cone : Cone (funPost g) (nameFun f) X
  cone = record
    { left = funCurry v ; right = terminate X
    ; match = funIsoReflect (funPost g ∘ funCurry v) (nameFun f ∘ terminate X) rawMatch }

  matching-comparison :
    (rightChange ∙ (funUncurryIso (Cone.match cone) ∙ leftChange ⁻¹)) =₂ desired
  matching-comparison = cancel-right leftChange desired ∙
    (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (leftChange ⁻¹)) ∙
      ((isoComp-assoc-at rightChange rawMatch (leftChange ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso rightChange)
          (isoComp-cong
            (funIsoReflect-β (funPost g ∘ funCurry v) (nameFun f ∘ terminate X) rawMatch)
            (idIso (leftChange ⁻¹)))))

  functor : MAP X (FunOver f g)
  functor = pullbackLift cone

  comparison : ConeIso (conePre functor (pullbackCone (funPost g) (nameFun f))) cone
  comparison = pullbackLift-β cone

  evaluation : funUncurry (Over.forget f g ∘ functor) =₁ v
  evaluation = funCurry-β v ∙ funUncurry-cong (ConeIso.leftIso comparison)
```
