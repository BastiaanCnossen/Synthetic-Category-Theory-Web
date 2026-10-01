# The coslice pullback square of an adjunction

For an adjunction `l ⊣ r`, the coslice at `l b` is the pullback of the
coslice at `b` along `r`. The square uses the ordinary coslice projection
as its right leg. Its matching is the transported matching of the
transposition equivalence, and the whole-cone comparison is retained.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCosliceSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I using (module RelativeCoslice)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullbackCone-isPullback;
    pullback-restrict-equivalence; pullback-cone-invariant)
import SCT.VolumeI.Chapter04.Section04.CosliceAdjunctions as Coslices
open Laws.PullbackStructure P using (pullbackCone)

module At {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (b : Obj-abs C) where
  private
    module Transpose = Coslices.Absolute 𝒯 M ℱ P I E S Q adj b
      using (functor; isEquiv; over-base; transposed; transposed-cone; transposed-computation; coslice-projection-computation)
    bottom = coslice-projection b
    projection = coslice-projection (l ∘ b)
    universal-square = pullbackCone bottom r
    raw = conePre Transpose.functor universal-square
    α = FunctorLift.comparison Transpose.over-base

  square : Cone bottom r (Coslice D (l ∘ b))
  square = record { left = Cone.left raw ; right = projection
    ; match = (r ◁ α) ∙ Cone.match raw }

  abstract
    computation : ConeIso raw square
    computation = record { leftIso = idIso (Cone.left raw) ; rightIso = α
      ; compatible = isoComp-unitʳ-at (Cone.match square) ∙
          isoComp-cong (idIso (Cone.match square)) (postWhisker-idIso bottom (Cone.left raw)) }

    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant computation
      (pullback-restrict-equivalence universal-square Transpose.functor
        (pullbackCone-isPullback bottom r) Transpose.isEquiv)

  open Transpose public using (transposed; transposed-cone; transposed-computation; coslice-projection-computation)
```

