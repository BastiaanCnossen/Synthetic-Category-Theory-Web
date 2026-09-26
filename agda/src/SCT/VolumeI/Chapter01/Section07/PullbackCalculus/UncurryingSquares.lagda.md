# Uncurrying the specified commutative square

This is the coherence assertion used in
`lem:Functor_Category_Preserves_Pullbacks`. The cone conversion is defined
before any pullback hypothesis. For every anima parameter and every map
into the tested vertex, it identifies the converted cone with the cone
induced through the uncurrying equivalence at that vertex.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section07.PullbackCalculus.UncurryingSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappedCones as MappingCones
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones as FunctorCones
import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying as MapUncurrying
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying as FunUncurrying
import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeReflection as MapReflection
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingTests 𝒯 M F using (module Test)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.UncurryingCones 𝒯 M F using (module Transport)

private
  module MC = MappingCones 𝒯 M P
  module FC = FunctorCones 𝒯 M F P
  module MU = MapUncurrying 𝒯 M
  module FU = FunUncurrying 𝒯 M F
  module MR = MapReflection 𝒯 M

module SquareComparison {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T K : CAT) (original : Cone f g S) where

  open Transport T K f g public
  functorSquare = FC.mappedCone K original
  testedSquare = MC.mappedCone T functorSquare
  mappingSquare = MC.mappedCone (T × K) original
  module U = Test T K S

  raw-evaluation : {X : CAT} (h : MAP X (Map T (Fun K S))) →
    ConeIso (raw (conePre h testedSquare))
      (MU.uncurryCone (conePre (U.forward ∘ h) mappingSquare))
  raw-evaluation {X} h =
    coneIso-compose (coneIso-inverse (MC.MappedCone.evaluate (T × K) original (U.forward ∘ h)))
    (coneIso-compose (cone-action original ((U.represents h) ⁻¹))
    (coneIso-compose (conePre-assoc (Associativity.backward X T K)
      (funUncurry (mapUncurry h)) original)
    (coneIso-compose (coneIso-pre (Associativity.backward X T K)
      (FC.MappedCone.evaluate K original (mapUncurry h)))
      (coneIso-pre (Associativity.backward X T K)
        (FU.uncurryConeIso (MC.MappedCone.evaluate T functorSquare h))))))

  comparison : {X : CAT} (xAn : isAn X) (h : MAP X (Map T (Fun K S))) →
    ConeIso (forward xAn (conePre h testedSquare))
      (conePre (U.forward ∘ h) mappingSquare)
  comparison xAn h = MR.ReflectCone.comparison xAn _ _
    (coneIso-compose (raw-evaluation h) (Forward.evaluation xAn (conePre h testedSquare)))
```

Each evaluation comparison above retains the original matching with its
endpoint changes. After double uncurrying, `U.represents h` compares the
two maps into the original vertex. Applying `cone-action original` to
that identification supplies both leg comparisons and their compatibility
with the original matching. Reflection then supplies the compatibility
in the mapping-anima square.

The next statement makes the resulting equation explicit: after changing
the two endpoints along the comparison, the transported matching is
identified with the matching of the specified target cone.

```agda
  matching-comparison : {X : CAT} (xAn : isAn X) (h : MAP X (Map T (Fun K S))) →
    Cone.match (coneRetarget (forward xAn (conePre h testedSquare))
      (Cone.left (conePre (U.forward ∘ h) mappingSquare))
      (Cone.right (conePre (U.forward ∘ h) mappingSquare))
      (ConeIso.leftIso (comparison xAn h)) (ConeIso.rightIso (comparison xAn h)))
    =₂ Cone.match (conePre (U.forward ∘ h) mappingSquare)
  matching-comparison xAn h = coneRetarget-match (comparison xAn h)

  square-comparison :
    ConeIso (forward (map-isAn T (Fun K S)) testedSquare)
      (conePre U.forward mappingSquare)
  square-comparison = coneIso-compose (cone-action mappingSquare (comp-unitʳ U.forward))
    (coneIso-compose (comparison (map-isAn T (Fun K S)) (id (Map T (Fun K S))))
      (forward-iso (map-isAn T (Fun K S)) (coneIso-inverse (conePre-id testedSquare))))
```
