# The mapping-anima fiber square

Take the core of the defining pullback for `FunOver`. The two cospan
comparisons identify its corners with the displayed mapping animae.
Transporting the whole pullback cone, including its matching, gives
the square in `def:Relative_Functor_Category_Global_Sections`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.MappingFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-of-anima)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P using (module MappingPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.MappingComparisons 𝒯 M ℱ P
  using (module Postcomposition; module Named)

module MappingFiber {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  module Source = MappingPullback One (funPost g) (nameFun f)
    using (comparison; square; square-isPullback)
  module Left = CoreOfFun C D using (uncurrying; uncurrying-isEquiv)
  module Base = CoreOfFun C S using (uncurrying; uncurrying-isEquiv)

  cospan : CospanMap (mapPost {C = One} (funPost {C = C} g)) (mapPost {C = One} (nameFun f))
    (mapPost {C = C} g) (nameMap f)
  cospan = record
    { left = Left.uncurrying
    ; right = coreInclusion One
    ; base = Base.uncurrying
    ; leftSquare = (Postcomposition.comparison C g) ⁻¹
    ; rightSquare = (Named.comparison f) ⁻¹ }

  module Change = CospanMap cospan using (pullbackMap; pullbackMap-β)

  comparison : MAP (MapOver f g) (Pullback (mapPost {C = C} g) (nameMap f))
  comparison = Change.pullbackMap ∘ Source.comparison

  abstract
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-compose Source.comparison Change.pullbackMap Source.square-isPullback
      (CospanEquivalence.pullbackMap-isEquiv cospan Left.uncurrying-isEquiv
        (core-of-anima One one-isAn) Base.uncurrying-isEquiv)

  original : Cone (mapPost {C = C} g) (nameMap f) (MapOver f g)
  original = conePre comparison (pullbackCone (mapPost g) (nameMap f))

  forget : MAP (MapOver f g) (Map C D)
  forget = Left.uncurrying ∘ mapPost (Over.forget f g)

  forget-comparison : Cone.left original =₁ forget
  forget-comparison = (Left.uncurrying ◁ pullbackLift-β₁ Source.square) ∙
    (comp-assoc Source.comparison pullback₁ Left.uncurrying ∙
      ((ConeIso.leftIso Change.pullbackMap-β ▷ Source.comparison) ∙
        (comp-assoc Source.comparison Change.pullbackMap pullback₁) ⁻¹))

  square : Cone (mapPost {C = C} g) (nameMap f) (MapOver f g)
  square = coneRetarget original forget (terminate (MapOver f g))
    forget-comparison (terminal-iso _ _)

  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant
      (coneRetarget-β original forget (terminate (MapOver f g)) forget-comparison (terminal-iso _ _))
      (pullback-restrict-equivalence (pullbackCone (mapPost g) (nameMap f)) comparison
        (pullbackCone-isPullback (mapPost g) (nameMap f)) comparison-isEquiv)
```

The square has the ordinary forgetful map as its upper leg. Its
matching is transported from the core pullback through the named
comparisons, so the pullback assertion includes that identification.
