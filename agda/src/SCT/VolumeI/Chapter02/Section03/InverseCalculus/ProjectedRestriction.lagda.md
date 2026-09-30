# Invertibility of a projected restriction

A comparison of projected transformations transports invertibility after
restriction. The parameter comparison is retained explicitly, and all
changes of endpoint frames preserve the actual two inverse equations.
This does not use an objectwise criterion.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ProjectedRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso; restrict-expression-compose)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I
  using (restrict-post)

module At {C D T D′ : CAT} {x y : MAP C C}
  (ε : MorphismExpression x y) (s : MAP D C) (v : MAP D′ D)
  (u : MAP T C) (j : MAP D′ T) (κ : (u ∘ j) =₁ (s ∘ v))
  {h k : MAP T T} (δ : MorphismExpression h k)
  (ξ : (x ∘ u) =₁ (u ∘ h)) (ζ : (y ∘ u) =₁ (u ∘ k))
  (projected : ExpressionIso (post-expression u δ)
    (retarget-expression (restrict-expression ε u) ξ ζ)) where

  abstract
    value : IsInvertibleExpression (restrict-expression ε s) →
      IsInvertibleExpression (post-expression u (restrict-expression δ j))
    value given =
      let along-composite = restrict-parameter-invertible ε (κ ⁻¹)
            (restrict-composite-invertible ε s v given)
          iterated = retarget-reflects-invertible (restrict-expression (restrict-expression ε u) j)
            (comp-assoc j u x) (comp-assoc j u y)
            (identified-invertible (expressionIso-inverse (restrict-expression-compose ε u j)) along-composite)
          framed = retarget-invertible (restrict-expression (restrict-expression ε u) j)
            (ξ ▷ j) (ζ ▷ j) iterated
          restricted = identified-invertible
            (expressionIso-inverse (restrict-retarget (restrict-expression ε u) ξ ζ j)) framed
          projected-restriction = identified-invertible
            (expressionIso-inverse (restrict-expressionIso projected j)) restricted
      in identified-invertible (restrict-post u δ j)
        (retarget-invertible (restrict-expression (post-expression u δ) j)
          (comp-assoc j h u) (comp-assoc j k u) projected-restriction)
```
