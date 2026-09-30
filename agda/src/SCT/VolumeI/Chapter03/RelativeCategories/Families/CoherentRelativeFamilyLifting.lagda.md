# A coherent lifting rule for relative families

Present comparisons of relative families by a single universal cone.
Uncurrying its cospan preserves the pullback property, since each corner
map is an equivalence. Consequently every native relative identification
lifts, with a computation rule that retains its triangle witness.

The action here is defined by restriction of this universal cone. It is
a new coherent action; agreement with the earlier pointwise triangle
calculation is not asserted. Its underlying identification is compared
explicitly with the usual action of uncurrying below.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as PullbackComparison

module SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ComparisonCospan 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonLifting 𝒯 M ℱ P using (module Lift)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks 𝒯 P using (module Mapped; rightSquareOf)

module Families {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (F G : MAP X (FunOver f g)) where
  source = conePre F (pullbackCone (funPost g) (nameFun f))
  target = conePre G (pullbackCone (funPost g) (nameFun f))
  module Change = Uncurrying source target
    using (cospan; left; left-isEquiv; right-isEquiv; base-isEquiv; module Target)
  module Original = PullbackComparison.IsoComparison 𝒯 dataPullback F G
    using (comparisonCone)

  cone : Cone Change.Target.leftMap Change.Target.rightMap (F ＝ G)
  cone = CospanMap.mapCone Change.cospan Original.comparisonCone

  opaque
    cone-isPullback : IsPullback cone
    cone-isPullback = Mapped.isPullback Change.cospan
      (degenerate-pullback Change.base-isEquiv (rightSquareOf Change.cospan) Change.right-isEquiv)
      Original.comparisonCone (pullback-isoMap-isEquiv F G) Change.left-isEquiv

  open Lift (family f g F) (family f g G) cone cone-isPullback public
    using (action; lift; computation; cone-computation; comparison-map;
      point-image; action-image; encoded-computation; Result; result)

  opaque
    underlying-action : (α : F =₁ G) →
      FunctorOverIso.underlying (action α) =₂ funUncurryIso (Over.forget f g ◁ α)
    underlying-action α = (uncurryFamily-absolute (Over.forget f g ◁ α)) ∙
      (uncurryFamily-cong (comp-unitˡ (Over.forget f g ◁ α)) ∙
      (uncurryFamily-restrict (id _) (Over.forget f g ◁ α) ∙
        comp-assoc α (postWhisker (Over.forget f g)) Change.left))

  opaque
    underlying-computation : (Φ : FunctorOverIso (family f g F) (family f g G)) →
      funUncurryIso (Over.forget f g ◁ lift Φ) =₂ FunctorOverIso.underlying Φ
    underlying-computation Φ = FunctorOverIso₂.underlying (computation Φ) ∙
      (underlying-action (lift Φ)) ⁻¹

  opaque
    result-image : (Φ : FunctorOverIso (family f g F) (family f g G)) (chosen : Result Φ) →
      funUncurryIso (Over.forget f g ◁ Result.comparison chosen) =₂ FunctorOverIso.underlying Φ
    result-image Φ chosen = FunctorOverIso₂.underlying (Result.full-image chosen) ∙
      (underlying-action (Result.comparison chosen)) ⁻¹
```
