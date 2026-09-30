# Comparing one evaluated projection

Suppose a projection of the proposed evaluation agrees with evaluation
of the corresponding projection after base change. The tested comparison
of relative functor categories then agrees with actual uncurrying on
this leg. This argument retains its triangle over the base and requires
no higher naturality of the base-change compositor.

The two legs can be treated separately in this way. Their compatibility
with a pullback matching is a further equation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies as EvaluationFamilies

module SCT.VolumeI.Chapter03.Section05.Currying.DependentEvaluationLegs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module IdentityFamily {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) (k : MAP K T) where
  module Raw = EvaluationFamilies.Evaluation 𝒯 M ℱ P p f g ε k using (functor; evaluate; module At)
  X = FunOver k g
  module At = Raw.At X using (inclusion; family-comparison)
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  U = universal k g
  I = family k g (id X)
  module B = Change p using (functor; module Identification)

  opaque
    changed-identity : FunctorOverIso (B.functor I) (B.functor U)
    changed-identity = B.Identification.comparison {u = I} {v = U} (family-identity k g)

    evaluated-identity : FunctorOverIso (Raw.evaluate I) (Raw.evaluate U)
    evaluated-identity = postwhisker-over ε {u = B.functor I} {v = B.functor U} changed-identity

    restricted-identity : FunctorOverIso (compose-over (Raw.evaluate I) At.inclusion)
      (compose-over (Raw.evaluate U) At.inclusion)
    restricted-identity = prewhisker-over {v = Raw.evaluate I} {w = Raw.evaluate U}
      At.inclusion evaluated-identity

    evaluated-family : FunctorOverIso (family k′ f Raw.functor)
      (compose-over (Raw.evaluate I) At.inclusion)
    evaluated-family = compose-iso-over (At.family-comparison (id X))
      (family-identification k′ f {F = Raw.functor} {G = Raw.functor ∘ id X}
        ((comp-unitʳ Raw.functor) ⁻¹))

    comparison : FunctorOverIso (family k′ f Raw.functor)
      (compose-over (Raw.evaluate U) At.inclusion)
    comparison = compose-iso-over restricted-identity evaluated-family

module Projection {S T C D R Q : CAT} (p : MAP S T)
  (f : MAP C S) (g : MAP D T) (r : MAP R S) (q : MAP Q T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f)
  (η : FunctorOver (pullback₂ {f = q} {p}) r)
  (a : FunctorOver r f) (b : FunctorOver q g)
  (β : FunctorOverIso (compose-over a η) (compose-over ε (Change.functor p b))) where

  module At {K : CAT} (k : MAP K T) where
    module B = Change p using (functor; module Identification; module Composite)
    module Raw = EvaluationFamilies.Evaluation 𝒯 M ℱ P p r q η k using (functor)
    module Other = EvaluationFamilies.Evaluation 𝒯 M ℱ P p f g ε k using (functor; evaluate; module At)
    module Post = Postcompose k b using (functor; family-comparison)
    k′ : MAP (Pullback k p) S
    k′ = pullback₂
    module Project = Postcompose k′ a using (functor)
    X = FunOver k q
    U = universal k q
    BU = B.functor U
    module Parameter = Other.At X using (inclusion; family-comparison)
    module Identity = IdentityFamily p r q η k using (comparison)
    common = compose-over (compose-over ε (B.functor (compose-over b U))) Parameter.inclusion

    module Compared (F : MAP X (FunOver k′ r))
      (γ : (Project.functor ∘ F) =₁ (Other.functor ∘ Post.functor)) where

      opaque
        changed-postcomposition : FunctorOverIso
          (B.functor (family k g Post.functor)) (B.functor (compose-over b U))
        changed-postcomposition = B.Identification.comparison
          {u = family k g Post.functor} {v = compose-over b U} Post.family-comparison

        evaluated-postcomposition : FunctorOverIso
          (Other.evaluate (family k g Post.functor)) (compose-over ε (B.functor (compose-over b U)))
        evaluated-postcomposition = postwhisker-over ε
          {u = B.functor (family k g Post.functor)} {v = B.functor (compose-over b U)} changed-postcomposition

        projected-family : FunctorOverIso (compose-over a (family k′ r F))
          (family k′ f (Other.functor ∘ Post.functor))
        projected-family = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f}
          (family-identification k′ f {F = Project.functor ∘ F} {G = Other.functor ∘ Post.functor} γ)
          (inverse-iso-over (postcompose-family k′ a F))

        left-to-common : FunctorOverIso (compose-over a (family k′ r F)) common
        left-to-common = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f}
          (prewhisker-over {v = Other.evaluate (family k g Post.functor)}
            {w = compose-over ε (B.functor (compose-over b U))} Parameter.inclusion evaluated-postcomposition)
          (compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f}
            (Parameter.family-comparison Post.functor) projected-family)

        evaluation-projection : FunctorOverIso (compose-over a (compose-over η BU))
          (compose-over ε (B.functor (compose-over b U)))
        evaluation-projection = compose-iso-over {f = pullback₂ {f = k ∘ pr₂ {C = X}} {p}} {g = f}
          (postwhisker-over ε {u = compose-over (B.functor b) BU}
            {v = B.functor (compose-over b U)} (B.Composite.comparison U b))
          (compose-iso-over (associator-over BU (B.functor b) ε)
            (compose-iso-over (prewhisker-over {v = compose-over a η}
              {w = compose-over ε (B.functor b)} BU β) (inverse-iso-over (associator-over BU η a))))

        right-to-common : FunctorOverIso (compose-over a (family k′ r Raw.functor)) common
        right-to-common = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f}
          (prewhisker-over {v = compose-over a (compose-over η BU)}
            {w = compose-over ε (B.functor (compose-over b U))} Parameter.inclusion evaluation-projection)
          (compose-iso-over (inverse-iso-over (associator-over Parameter.inclusion (compose-over η BU) a))
            (postwhisker-over a Identity.comparison))

        comparison : FunctorOverIso (compose-over a (family k′ r F))
          (compose-over a (family k′ r Raw.functor))
        comparison = compose-iso-over (inverse-iso-over right-to-common) left-to-common
```
