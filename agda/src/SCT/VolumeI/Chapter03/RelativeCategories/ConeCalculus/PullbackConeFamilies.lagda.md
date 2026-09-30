# Evaluating arbitrary families in a relative pullback

The whole-cone evaluation comparison survives an arbitrary parameter
substitution. In particular, it retains the matching of a family in the
relative pullback, not just its two projected functors. This is the
parameterized form used when comparing dependent pullback cones.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingPre 𝒯 M ℱ using (uncurryCone-restrict)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeEvaluation 𝒯 M ℱ P using (module Evaluation)

open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeEvaluation 𝒯 M ℱ P using () renaming (module Evaluation to ConeEvaluation)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackMatching 𝒯 M ℱ P using (module Matching)

module Families {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (projection; left-map; right-map)
  module Evaluated = Evaluation k u v using (ordinary; comparison; forget; e)
  module Cones = ConeEvaluation k u v using (ordinary; value; comparison; restrict-ordinary)
  module Match = Matching k u v using (cone)
  module At {X : CAT} (F : MAP X (FunOver k R.projection)) where
    parameter = productMap F (id K)
    value = family k R.projection F
    source = uncurryCone (conePre F Evaluated.ordinary)
    target = conePre (FunctorLift.lift value) (pullbackCone R.left-map R.right-map)
    abstract
      comparison : ConeIso source target
      comparison = coneIso-compose
        (cone-action (pullbackCone R.left-map R.right-map) ((funUncurry-restrict Evaluated.forget F) ⁻¹))
        (coneIso-compose (conePre-assoc parameter Evaluated.e (pullbackCone R.left-map R.right-map))
          (coneIso-compose (coneIso-pre parameter Evaluated.comparison)
            (uncurryCone-restrict F Evaluated.ordinary)))

    module Compared (s : Cone (Postcompose.functor k u) (Postcompose.functor k v) X)
      (Φ : ConeIso (conePre F Match.cone) s) where
      abstract
        evaluated-comparison : ConeIso target (Cones.value s)
        evaluated-comparison = coneIso-compose (Cones.comparison Φ)
          (coneIso-compose (uncurryConeIso (Cones.restrict-ordinary F Match.cone))
            (coneIso-inverse comparison))
```
