# Natural transformations over a base

A transformation between two specified functors over a base has an
endpoint-preserving comparison between its image and the identity
transformation of the source structure map. Both structure identifications
are retained. This module supplies identity, composition, and transformations
induced by relative identifications. The comparison with arrows in the
chosen global relative functor category is a separate construction.

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

module SCT.VolumeI.Chapter03.RelativeCategories.Morphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
  public using (FunctorOver; identity-over; compose-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  using (FunctorOverIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-post; isomorphism-retarget; isomorphism-cong; isomorphism-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S
  using (left-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity

module Over {C D B : CAT} (p : MAP C B) (q : MAP D B) where
  IsOver : (u v : FunctorOver p q) →
    MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v) → Set m
  IsOver u v α = ExpressionIso
    (retarget-expression (post-expression q α) (FunctorLift.comparison u) (FunctorLift.comparison v))
    (identity-expression p)

  record MorphismOver (u v : FunctorOver p q) : Set m where
    field
      underlying : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v)
      over-base : IsOver u v underlying

  abstract
    identity-isOver : (u : FunctorOver p q) → IsOver u u (identity-expression (FunctorLift.lift u))
    identity-isOver u = expressionIso-compose (Identity.At.comparison 𝒯 M ℱ P I E (FunctorLift.comparison u))
      (retarget-expressionIso (post-identity q (FunctorLift.lift u))
        (FunctorLift.comparison u) (FunctorLift.comparison u))

    identified-isOver : {u v : FunctorOver p q}
      {α β : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v)} →
      ExpressionIso α β → IsOver u v α → IsOver u v β
    identified-isOver {u} {v} comparison over = expressionIso-compose over
      (retarget-expressionIso (post-expressionIso q (expressionIso-inverse comparison))
        (FunctorLift.comparison u) (FunctorLift.comparison v))

    compose-isOver : {u v w : FunctorOver p q}
      (α : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v))
      (β : MorphismExpression (FunctorLift.lift v) (FunctorLift.lift w)) →
      IsOver u v α → IsOver v w β → IsOver u w (compose-expression α β)
    compose-isOver {u} {v} {w} α β ea eb = expressionIso-compose (left-unit (identity-expression p))
      (expressionIso-compose (compose-expression-cong ea eb)
        (expressionIso-compose
          (expressionIso-inverse (retarget-composition (post-expression q α) (post-expression q β)
            (FunctorLift.comparison u) (FunctorLift.comparison v) (FunctorLift.comparison w)))
          (retarget-expressionIso (expressionIso-inverse (post-composition q α β))
            (FunctorLift.comparison u) (FunctorLift.comparison w))))

    identification-isOver : {u v : FunctorOver p q} (ξ : FunctorOverIso u v) →
      IsOver u v (isomorphism-expression (FunctorOverIso.underlying ξ))
    identification-isOver {u} {v} ξ = expressionIso-compose (isomorphism-id p)
      (expressionIso-compose
        (isomorphism-cong (isoComp-inverseʳ-at (FunctorLift.comparison u) ∙
          isoComp-cong (FunctorOverIso.compatible ξ) (idIso ((FunctorLift.comparison u) ⁻¹))))
        (expressionIso-compose
          (isomorphism-retarget (q ◁ FunctorOverIso.underlying ξ)
            (FunctorLift.comparison u) (FunctorLift.comparison v))
          (retarget-expressionIso (isomorphism-post q (FunctorOverIso.underlying ξ))
            (FunctorLift.comparison u) (FunctorLift.comparison v))))

  identity-over-morphism : (u : FunctorOver p q) → MorphismOver u u
  identity-over-morphism u = record
    { underlying = identity-expression (FunctorLift.lift u) ; over-base = identity-isOver u }

  compose-over-morphism : {u v w : FunctorOver p q} → MorphismOver u v → MorphismOver v w → MorphismOver u w
  compose-over-morphism α β = record
    { underlying = compose-expression (MorphismOver.underlying α) (MorphismOver.underlying β)
    ; over-base = compose-isOver (MorphismOver.underlying α) (MorphismOver.underlying β)
        (MorphismOver.over-base α) (MorphismOver.over-base β) }

  identification-over-morphism : {u v : FunctorOver p q} → FunctorOverIso u v → MorphismOver u v
  identification-over-morphism ξ = record
    { underlying = isomorphism-expression (FunctorOverIso.underlying ξ)
    ; over-base = identification-isOver ξ }
```
