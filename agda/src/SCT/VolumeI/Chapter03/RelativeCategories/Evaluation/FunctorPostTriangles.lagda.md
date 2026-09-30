# Postcomposition as a triangle of functor categories

Choose the triangle for ordinary postcomposition by uncurrying its
specified evaluation. Its beta comparison is therefore available when
acting on relative cones. Evaluating that action agrees over the base
with native postcomposition of the evaluated family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.FunctorPostTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (change-source; change-source-iso)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change; compose-source-change-underlying)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition 𝒯 M ℱ P using (module Composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.NativeEvaluationTriangles 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action; cone-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)

module Post (K : CAT) {C D S : CAT} {f : MAP C S} {g : MAP D S} (u : FunctorOver f g) where
  module Basic = Evaluation K f using (basic; module Factor)
  desired = compose-over u Basic.basic
  module Curried = Triangle.Recovery g (funPost {C = K} f) desired using (backward; comparison; comparison-underlying)
  triangle : FunctorOver (funPost {C = K} f) (funPost {C = K} g)
  triangle = Curried.backward

  module OnCone {X : CAT} (k : MAP K S) (s : Cone (funPost f) (nameFun k) X) where
    native = cone-triangle s
    uncurried = Uncurry.value K S native
    κ = uncurry-constant-name k (Cone.right s)
    acted = Action.value (nameFun k) triangle s
    abstract
      uncurried-comparison : FunctorOverIso
        (Triangle.value g (nameFun k ∘ Cone.right s) (compose-over triangle native))
        (compose-over u (Triangle.value f (nameFun k ∘ Cone.right s) native))
      uncurried-comparison = compose-iso-over
        (postwhisker-over u (Basic.Factor.comparison native))
        (compose-iso-over (associator-over uncurried Basic.basic u)
          (compose-iso-over (prewhisker-over uncurried Curried.comparison)
            (Composite.comparison g native triangle)))
      comparison : FunctorOverIso (EvaluatedCone acted) (compose-over u (EvaluatedCone s))
      comparison = compose-iso-over
        (inverse-iso-over (compose-source-change κ (Triangle.value f _ native) u))
        (change-source-iso κ uncurried-comparison)
      uncurried-underlying : FunctorOverIso.underlying uncurried-comparison =₂
        funPost-uncurry (FunctorLift.lift u) (Cone.left s)
      uncurried-underlying =
        let U = FunctorLift.lift u
            h = Cone.left s
            H = productMap h (id K)
            b = funPost-β U ▷ H
            ℓ = funUncurry-restrict (funPost U) h
            A = comp-assoc H funEval U
        in isoComp-unitˡ-at (funPost-uncurry U h) ∙
          isoComp-cong
            (postWhisker-idIso U (funUncurry h) ∙
              (postWhisker U ◁ Basic.Factor.comparison-underlying native))
            (isoComp-cong (idIso A)
              (isoComp-cong (preWhisker H ◁ Curried.comparison-underlying)
                (Composite.comparison-underlying g native triangle)))

      comparison-underlying : FunctorOverIso.underlying comparison =₂
        funPost-uncurry (FunctorLift.lift u) (Cone.left s)
      comparison-underlying = isoComp-unitˡ-at (funPost-uncurry (FunctorLift.lift u) (Cone.left s)) ∙
        isoComp-cong
          (inverse-identity _ ∙ (＝-inv ◁ compose-source-change-underlying κ (Triangle.value f _ native) u))
          uncurried-underlying
```
