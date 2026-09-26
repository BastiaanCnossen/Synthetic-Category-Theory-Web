# Uncurrying for dependent products along product projections

The defining pullback, the relative exponential law, and change of
source structure give an equivalence into the relative functor category
on `K × S`. On the universal family, this composite is restriction of
the stipulated pullback-and-evaluation functor. Cancelling restriction
therefore proves that the stipulated functor is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
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
    module D = Ev.F.Domain k
    α = Ev.F.uncurry-name k
    module A = PullbackTarget Ev.F.name (funPost r) k
    module B′ = Law r (Ev.F.name ∘ k)
    module C = Change α r
    module BC = BaseChange Ev.F.projection k g
    module Post = Postcompose BC.f′ ε
    module Restrict = Precompose r D.inclusion
    module Product = Evaluate r k u
    module Geometry = Families r k u
    module NativeBC = BaseEvaluation Ev.F.projection k g
    functor = Post.functor ∘ BC.functor
    left = Restrict.functor ∘ functor
    right = C.functor ∘ (B′.functor ∘ A.functor)
    final-family = compose-over (compose-over ε (Geometry.Actual.At.pulled u)) (Geometry.Pulled.Arg.family X)

    abstract
      right-family : FunctorOverIso (family D.structure r right) Product.source
      right-family = compose-iso-over
        (change-source-iso (α ▷ pr₂) (Family.identification r (Ev.F.name ∘ k) X A.evaluation-comparison))
        (compose-iso-over (change-source-iso (α ▷ pr₂) (B′.family-comparison A.functor))
          (Source.substituted-comparison α r (B′.functor ∘ A.functor)))

      product-family : FunctorOverIso Product.target final-family
      product-family = compose-iso-over
        (inverse-iso-over (associator-over (Geometry.Pulled.Arg.family X) (Geometry.Actual.At.pulled u) ε))
        (compose-iso-over (postwhisker-over ε Geometry.comparison)
          (compose-iso-over (associator-over Product.argument Ev.D.inclusion ε)
            (prewhisker-over Product.argument (inverse-iso-over Ev.product-comparison))))

      left-family : FunctorOverIso (family D.structure r left) final-family
      left-family = compose-iso-over
        (prewhisker-over (Geometry.Pulled.Arg.family X) (postwhisker-over ε NativeBC.same-family))
        (compose-iso-over
          (prewhisker-over (Geometry.Pulled.Arg.family X) (postwhisker-over ε BC.family-comparison))
          (compose-iso-over
            (prewhisker-over (Geometry.Pulled.Arg.family X) (postcompose-family BC.f′ ε BC.functor))
            (Restrict.family-comparison functor)))

      comparison : left =₁ right
      comparison = reflect-family D.structure r left right
        (compose-iso-over (inverse-iso-over right-family)
          (compose-iso-over (inverse-iso-over Product.comparison)
            (compose-iso-over (inverse-iso-over product-family) left-family)))

      right-isEquiv : IsEquiv right
      right-isEquiv = equiv-compose (B′.functor ∘ A.functor) C.functor
        (equiv-compose A.functor B′.functor A.functor-isEquiv B′.functor-isEquiv) C.functor-isEquiv

      functor-isEquiv : IsEquiv functor
      functor-isEquiv = equiv-cancel-left functor Restrict.functor
        (Restrict.Equivalence.functor-isEquiv D.inclusion-isEquiv)
        (equiv-transport (comparison ⁻¹) right-isEquiv)
```
