# Uncurrying for dependent products along product projections

The defining pullback, the relative exponential law, and change of
source structure give an equivalence into the relative functor category
on `K × S`. On the universal family, this composite is restriction of
the stipulated pullback-and-evaluation functor. Cancelling restriction
therefore proves that the stipulated functor is an equivalence.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductDependentUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedRelativeExponentialLaw 𝒯 M ℱ P using (module Law)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Family)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.Currying.SourceChangeFamilies 𝒯 M ℱ P using (module Source)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.EvaluatedBaseChange 𝒯 M ℱ P using () renaming (module Evaluation to BaseEvaluation)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductEvaluationFamilies 𝒯 M ℱ P using (module Evaluate)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.ProductBaseChangeFamilies 𝒯 M ℱ P using (module Families)

module Uncurrying {T S E : CAT} (r : MAP E (T × S)) where
  module Ev = Evaluation r
  g = Ev.projection
  ε = Ev.evaluation

  module At {K : CAT} (k : MAP K T) where
    X = FunOver k g
    u = universal k g
    -- Restructured: the modules instantiated at concrete arguments are no
    -- longer instantiated; their results are used through direct calls.
    -- `BC` and `Post` are kept (restricted) because `ProductDependentProducts`
    -- uses `At.BC` and `At.Post`.
    module D = Ev.F.Domain k using (structure; inclusion; inclusion-isEquiv)
    α = Ev.F.uncurry-name k
    module BC = BaseChange Ev.F.projection k g
      using (f′; functor; maps; maps-as-core; family-comparison)
    module Post = Postcompose BC.f′ ε using (functor; maps; maps-as-core)
    private
      A-functor = PullbackTarget.functor Ev.F.name (funPost r) k
      A-evaluation-comparison = PullbackTarget.evaluation-comparison Ev.F.name (funPost r) k
      A-functor-isEquiv = PullbackTarget.functor-isEquiv Ev.F.name (funPost r) k
      B′-functor = Law.functor r (Ev.F.name ∘ k)
      B′-functor-isEquiv = Law.functor-isEquiv r (Ev.F.name ∘ k)
      C-functor = Change.functor α r
      C-functor-isEquiv = Change.functor-isEquiv α r
      restrict-functor = Precompose.functor r D.inclusion
      evaluate-source = Evaluate.source r k u
      evaluate-target = Evaluate.target r k u
      evaluate-argument = Evaluate.argument r k u
      evaluate-comparison = Evaluate.comparison r k u
      geometry-pulled = Families.Actual.At.pulled r k u u
      geometry-family = Families.Pulled.Arg.family r k u X
      geometry-comparison = Families.comparison r k u
      native-same-family = BaseEvaluation.same-family Ev.F.projection k g
    functor = Post.functor ∘ BC.functor
    left = restrict-functor ∘ functor
    right = C-functor ∘ (B′-functor ∘ A-functor)
    final-family = compose-over (compose-over ε geometry-pulled) geometry-family

    abstract
      right-family : FunctorOverIso (family D.structure r right) evaluate-source
      right-family = compose-iso-over
        (change-source-iso (α ▷ pr₂) (Family.identification r (Ev.F.name ∘ k) X A-evaluation-comparison))
        (compose-iso-over (change-source-iso (α ▷ pr₂) (Law.family-comparison r (Ev.F.name ∘ k) A-functor))
          (Source.substituted-comparison α r (B′-functor ∘ A-functor)))

      product-family : FunctorOverIso evaluate-target final-family
      product-family = compose-iso-over
        (inverse-iso-over (associator-over geometry-family geometry-pulled ε))
        (compose-iso-over (postwhisker-over ε geometry-comparison)
          (compose-iso-over (associator-over evaluate-argument Ev.D.inclusion ε)
            (prewhisker-over evaluate-argument (inverse-iso-over Ev.product-comparison))))

      left-family : FunctorOverIso (family D.structure r left) final-family
      left-family = compose-iso-over
        (prewhisker-over geometry-family (postwhisker-over ε native-same-family))
        (compose-iso-over
          (prewhisker-over geometry-family (postwhisker-over ε BC.family-comparison))
          (compose-iso-over
            (prewhisker-over geometry-family (postcompose-family BC.f′ ε BC.functor))
            (Precompose.family-comparison r D.inclusion functor)))

      comparison : left =₁ right
      comparison = reflect-family D.structure r left right
        (compose-iso-over (inverse-iso-over right-family)
          (compose-iso-over (inverse-iso-over evaluate-comparison)
            (compose-iso-over (inverse-iso-over product-family) left-family)))

      right-isEquiv : IsEquiv right
      right-isEquiv = equiv-compose (B′-functor ∘ A-functor) C-functor
        (equiv-compose A-functor B′-functor A-functor-isEquiv B′-functor-isEquiv) C-functor-isEquiv

      functor-isEquiv : IsEquiv functor
      functor-isEquiv = equiv-cancel-left functor restrict-functor
        (Precompose.Equivalence.functor-isEquiv r D.inclusion D.inclusion-isEquiv)
        (equiv-transport (comparison ⁻¹) right-isEquiv)
```
