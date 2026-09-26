# Transferring the terminal mapping test

This implements the terminal-parameter comparison in the reverse implication of
`prop:Mapping_Out_Of_Pushouts`. The two evaluation comparisons are explicit
inputs to this intermediate lemma. They must compare whole cocones with
the specified product square; a comparison of the legs alone is insufficient.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapRestrictionCones as MapCones
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunRestrictionCones as FunCones

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionTransfer
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
  using (Map; mapPre; mapUncurry; mapCurry; mapCurry-β; mapReflect; map-isAn)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappedCones 𝒯 M P using (mappedCone)
import SCT.VolumeI.Chapter01.Section06.MappingCalculus.TerminalPullbackTest as TerminalTest
module MC = MapCones 𝒯 M
module FC = FunCones 𝒯 M ℱ

module Detection {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (E : CAT)
  (map-evaluate : {X : CAT} (h : MAP X (Map D E)) →
    CoconeIso (MC.uncurryRestriction {u = u} {v = l} (conePre h (mappingOut s E)))
      (restrictionCocone s (mapUncurry h)))
  (fun-evaluate : {X : CAT} (h : MAP X (Fun D E)) →
    CoconeIso (FC.uncurryRestriction {u = u} {v = l} (conePre h (functorOut s E)))
      (restrictionCocone s (funUncurry h)))
  (universal : IsPullback (mappedCone One (functorOut s E))) where

  module U = TerminalTest.Test 𝒯 M P (functorOut s E) universal
  square = mappingOut s E

  module Lift {X : CAT} (xAn : isAn X)
    (t : Cone (mapPre {D = E} u) (mapPre l) X) where

    raw = MC.uncurryRestriction {u = u} {v = l} t
    module Curried = FC.CurryRestriction {u = u} {v = l} raw
    fun-lift = U.factor xAn Curried.value
    value = mapCurry xAn (funUncurry fun-lift)

    abstract
      comparison : ConeIso (conePre value square) t
      comparison = MC.ReflectRestriction.comparison {u = u} {v = l}
        xAn (conePre value square) t
        (coconeIso-compose Curried.comparison
          (coconeIso-compose (FC.uncurryRestrictionIso {u = u} {v = l} (U.factor-β xAn Curried.value))
          (coconeIso-compose (coconeIso-inverse (fun-evaluate fun-lift))
          (coconeIso-compose (restriction-action s (mapCurry-β xAn (funUncurry fun-lift)))
            (map-evaluate value)))))

  module Compare {X : CAT} (xAn : isAn X) (h k : MAP X (Map D E))
    (Φ : ConeIso (conePre h square) (conePre k square)) where

    h′ = funCurry (mapUncurry h)
    k′ = funCurry (mapUncurry k)

    abstract
      fun-comparison : ConeIso (conePre h′ (functorOut s E)) (conePre k′ (functorOut s E))
      fun-comparison = FC.ReflectRestriction.comparison {u = u} {v = l}
        (conePre h′ (functorOut s E)) (conePre k′ (functorOut s E))
        (coconeIso-compose (coconeIso-inverse (fun-evaluate k′))
        (coconeIso-compose (coconeIso-inverse (restriction-action s (funCurry-β (mapUncurry k))))
        (coconeIso-compose (map-evaluate k)
        (coconeIso-compose (MC.uncurryRestrictionIso {u = u} {v = l} Φ)
        (coconeIso-compose (coconeIso-inverse (map-evaluate h))
        (coconeIso-compose (restriction-action s (funCurry-β (mapUncurry h)))
          (fun-evaluate h′)))))))

      comparison : h =₁ k
      comparison = mapReflect xAn h k
        (funCurry-β (mapUncurry k) ∙
          (funUncurryIso (U.reflect xAn h′ k′ fun-comparison) ∙ (funCurry-β (mapUncurry h)) ⁻¹))

  module Inverse = Lift
    (pullback-isAn (mapPre {D = E} u) (mapPre l)
      (map-isAn B E) (map-isAn C E) (map-isAn A E))
    (pullbackCone (mapPre u) (mapPre l))

  abstract
    isPullback : IsPullback square
    isPullback = cone-isPullback-from-lifting square Inverse.value Inverse.comparison
      (Compare.comparison (map-isAn D E))
```
