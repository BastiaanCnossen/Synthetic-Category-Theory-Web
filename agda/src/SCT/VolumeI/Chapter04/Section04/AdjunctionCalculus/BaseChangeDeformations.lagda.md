# Base change of relative section deformations

The counit or unit over the original base lifts through the pullback.
The relative section square provides both endpoint identifications, so
the lifted transformation has the required endpoints and is over the new
base. Its left projection is compared with the original deformation.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.BaseChangeDeformations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismWhiskering as Whiskering
import SCT.VolumeI.Chapter03.RelativeCategories.PullbackMorphisms as Lifting
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedRelativeDeformations as Normal
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.BaseChangeSectionComparisons as Comparison

module At {C D D′ T : CAT} (p : MAP C D) (s : MAP D C)
  (ρ : (p ∘ s) =₁ id D) (v : MAP D′ D) (t : Cone p v T) (et : IsPullback t) where
  module Frames = Comparison.At 𝒯 M ℱ P p s ρ v t et
    using (u; q; j; κ; ρ′; U; new-composite; source; target)
  open Frames public using (u; q; j; κ; ρ′)
  module Original = Normal.WithSection 𝒯 M ℱ P I E S p s ρ using (module Left; module Right)

  module Left (ε : MorphismExpression (s ∘ p) (id C)) (over-base : Original.Left.NormalizedOver ε) where
    module Old = Original.Left.WithOver ε over-base using (value)
    module Restricted = Whiskering.Pre 𝒯 M ℱ P I E S Frames.U Old.value using (value)
    module Lift = Lifting.At.Given 𝒯 M ℱ P I E S t et q Frames.new-composite (identity-over q)
      Restricted.value Frames.source Frames.target using (value; underlying; source-frame; target-frame; left-image)
    open Lift public using (value; underlying; source-frame; target-frame; left-image)

  module Right (η : MorphismExpression (id C) (s ∘ p)) (over-base : Original.Right.NormalizedOver η) where
    module Old = Original.Right.WithOver η over-base using (value)
    module Restricted = Whiskering.Pre 𝒯 M ℱ P I E S Frames.U Old.value using (value)
    module Lift = Lifting.At.Given 𝒯 M ℱ P I E S t et q (identity-over q) Frames.new-composite
      Restricted.value Frames.target Frames.source using (value; underlying; source-frame; target-frame; left-image)
    open Lift public using (value; underlying; source-frame; target-frame; left-image)
```
