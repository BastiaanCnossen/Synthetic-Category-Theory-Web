# Relative functors as whole families

A map into the relative functor category evaluates to a family of
triangles. Evaluation commutes with changing the parameter category,
and currying recovers the original family over the base. These formulas
let subsequent proofs compare functors on their universal families.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Families.Families
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-inverse; conePre-id; conePre-assoc)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (module CurriedTriangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

universal : {C D S : CAT} (f : MAP C S) (g : MAP D S) → FunctorOver (f ∘ pr₂ {C = FunOver f g}) g
universal f g = EvaluatedCone (pullbackCone (funPost g) (nameFun f))

family : {X C D S : CAT} (f : MAP C S) (g : MAP D S) →
  MAP X (FunOver f g) → FunctorOver (f ∘ pr₂ {C = X}) g
family f g F = EvaluatedCone (conePre F (pullbackCone (funPost g) (nameFun f)))

abstract
  family-identity : {C D S : CAT} (f : MAP C S) (g : MAP D S) →
    FunctorOverIso (family f g (id (FunOver f g))) (universal f g)
  family-identity f g = evaluated-comparison (conePre-id (pullbackCone (funPost g) (nameFun f)))

  family-composite : {X Y C D S : CAT} (f : MAP C S) (g : MAP D S)
    (F : MAP Y X) (G : MAP X (FunOver f g)) →
    FunctorOverIso (family f g (G ∘ F)) (compose-over (family f g G) (parameter-over-functor f F))
  family-composite f g F G = compose-iso-over
    (evaluated-restriction F (conePre G (pullbackCone (funPost g) (nameFun f))))
    (evaluated-comparison (coneIso-inverse (conePre-assoc F G (pullbackCone (funPost g) (nameFun f)))))

  family-composite-underlying : {X Y C D S : CAT} (f : MAP C S) (g : MAP D S)
    (F : MAP Y X) (G : MAP X (FunOver f g)) →
    FunctorOverIso.underlying (family-composite f g F G) =₂
      (funUncurry-restrict (Over.forget f g ∘ G) F ∙
        funUncurryIso ((comp-assoc F G (Over.forget f g)) ⁻¹))
  family-composite-underlying f g F G = idIso _

  curried-beta : {X C D S : CAT} (f : MAP C S) (g : MAP D S)
    (v : FunctorOver (f ∘ pr₂ {C = X}) g) →
    FunctorOverIso (family f g (Curry.functor f g (FunctorLift.lift v) (FunctorLift.comparison v))) v
  curried-beta f g v = record
    { underlying = CurriedTriangle.evaluation-with-image f g (FunctorLift.lift v) (FunctorLift.comparison v)
    ; compatible = CurriedTriangle.native-beta f g (FunctorLift.lift v) (FunctorLift.comparison v) }

  postcompose-family : {X B C D S : CAT} (f : MAP B S) {g : MAP C S} {h : MAP D S}
    (u : FunctorOver g h) (F : MAP X (FunOver f g)) →
    FunctorOverIso (family f h (Postcompose.functor f u ∘ F)) (compose-over u (family f g F))
  postcompose-family f {g} {h} u F = compose-iso-over
    (postwhisker-over u (inverse-iso-over (evaluated-restriction F (pullbackCone (funPost g) (nameFun f)))))
    (compose-iso-over (associator-over (parameter-over-functor f F) (universal f g) u)
      (compose-iso-over (prewhisker-over (parameter-over-functor f F)
        (Postcompose.family-comparison f u))
        (family-composite f h F (Postcompose.functor f u))))

  postcompose-family-underlying : {X B C D S : CAT} (f : MAP B S) {g : MAP C S} {h : MAP D S}
    (u : FunctorOver g h) (F : MAP X (FunOver f g)) →
    FunctorOverIso.underlying (postcompose-family f u F) =₂
      ((FunctorLift.lift u ◁ (funUncurry-restrict (Over.forget f g) F) ⁻¹) ∙
        (comp-assoc (productMap F (id B)) (FunctorLift.lift (universal f g)) (FunctorLift.lift u) ∙
          ((FunctorOverIso.underlying (Postcompose.family-comparison f u) ▷ productMap F (id B)) ∙
            (funUncurry-restrict (Over.forget f h ∘ Postcompose.functor f u) F ∙
              funUncurryIso ((comp-assoc F (Postcompose.functor f u) (Over.forget f h)) ⁻¹)))))
  postcompose-family-underlying f {g} {h} u F =
    isoComp-cong (idIso (FunctorLift.lift u ◁ (funUncurry-restrict (Over.forget f g) F) ⁻¹))
      (isoComp-cong (idIso (comp-assoc (productMap F (id _)) (FunctorLift.lift (universal f g)) (FunctorLift.lift u)))
        (isoComp-cong (idIso (FunctorOverIso.underlying (Postcompose.family-comparison f u) ▷ productMap F (id _)))
          (family-composite-underlying f h F (Postcompose.functor f u))))

  family-identification : {X C D S : CAT} (f : MAP C S) (g : MAP D S)
    {F G : MAP X (FunOver f g)} → F =₁ G → FunctorOverIso (family f g F) (family f g G)
  family-identification f g α = evaluated-comparison (cone-action (pullbackCone (funPost g) (nameFun f)) α)
```
