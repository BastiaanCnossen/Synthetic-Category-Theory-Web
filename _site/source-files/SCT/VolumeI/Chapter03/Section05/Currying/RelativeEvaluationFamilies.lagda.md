# Evaluating arbitrary relative families

A projection and an evaluation map already determine uncurrying on
relative functor categories. No universal property is needed for this
construction or its computation on parameterized families. This lets us
verify proposed dependent products without assuming their universality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using () renaming (module Change to NativeChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSubstitution 𝒯 M ℱ P using (module Substitution)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones 𝒯 using (module Parameter)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedPullbacks 𝒯 P using (module Parameters)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.Section05.Currying.ActedConeRestriction 𝒯 M ℱ P using (module Restrict)

module Evaluation {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) (k : MAP K T) where
  module BC = BaseChange p k g using (f′; functor; maps; maps-as-core)
  module Post = Postcompose BC.f′ ε using (functor; maps; maps-as-core)
  evaluate : {A : CAT} {t : MAP A T} → FunctorOver t g →
    FunctorOver (pullback₂ {f = t} {p}) f
  evaluate u = compose-over ε (NativeChange.functor p u)
  functor : MAP (FunOver k g) (FunOver BC.f′ f)
  functor = Post.functor ∘ BC.functor

  abstract
    mapping-comparison : EvaluationAlong.uncurrying p f g ε k =₁ mapPost functor
    mapping-comparison = mapPost-comp BC.functor Post.functor ∙
      ((mapPost Post.functor ◁ BC.maps-as-core) ∙ (Post.maps-as-core ▷ BC.maps))

    mapping-isEquiv : IsEquiv functor → IsEquiv (EvaluationAlong.uncurrying p f g ε k)
    mapping-isEquiv e = equiv-transport (mapping-comparison ⁻¹) (mapPost-isEquiv functor e)

  module At (X : CAT) where
    module Param = Parameter X (pullbackCone k p) using (cone)
    inclusion : FunctorOver (BC.f′ ∘ pr₂ {C = X}) (pullback₂ {f = k ∘ pr₂ {C = X}} {p})
    inclusion = lift-triangle Param.cone
    abstract
      inclusion-isEquiv : IsEquiv (FunctorLift.lift inclusion)
      inclusion-isEquiv = Parameters.isPullback X (pullbackCone k p) (pullbackCone-isPullback k p)

    module On (u : FunctorOver (k ∘ pr₂ {C = X}) g) where
      module Pulled = Change.At p k g u using (pulled; action-comparison)
      module Restricted = Restrict u (pullbackCone (k ∘ pr₂ {C = X}) p) Param.cone inclusion
        (pullbackLift-β Param.cone) (idIso (pullbackLift-β₂ Param.cone)) using (comparison)
      abstract
        comparison : FunctorOverIso (compose-over ε Pulled.pulled)
          (compose-over (evaluate u) inclusion)
        comparison = compose-iso-over (inverse-iso-over (associator-over inclusion _ ε))
          (postwhisker-over ε (compose-iso-over (inverse-iso-over Restricted.comparison)
            Pulled.action-comparison))

    abstract
      family-comparison : (F : MAP X (FunOver k g)) → FunctorOverIso
        (family BC.f′ f (functor ∘ F))
        (compose-over (evaluate (family k g F)) inclusion)
      family-comparison F = compose-iso-over (On.comparison (family k g F))
        (compose-iso-over (postwhisker-over ε (Substitution.family-comparison p k g F))
          (compose-iso-over (postcompose-family BC.f′ ε (BC.functor ∘ F))
            (family-identification BC.f′ f (comp-assoc F BC.functor Post.functor))))
```
