# Geometric realization preserves pushouts

This proves `cor:Fundamental_Groupoid_Preserves_Pushout_Squares` for the
specified realized square. First transfer cocone extension into an anima
using the localization equivalences on mapping animae. For an arbitrary
target, lift the cocone to its core, since realized categories are
animae. Reflection uses the original pushout and the localization
universal property. The cube comparison retains the original matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter03.Section04.RealizationPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-isAn)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.PushoutExtensions 𝒯 M P using (pushout-extension-property)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open Recognition.RecognitionAxiom N using (anima-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.PullbackAnimae 𝒯 M ℱ P I E S Q R N using (coreInclusion-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.FunctorCoreRestriction 𝒯 M ℱ using (module Restrict)
open import SCT.VolumeI.Chapter03.Section04.GeometricRealization 𝒯 M ℱ P I E S Q R using (module Realization)
open import SCT.VolumeI.Chapter03.Section04.FundamentalGroupoids 𝒯 M ℱ P I E S Q R N using (module Consequences)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.RealizationCoconeComparison 𝒯 M ℱ P I E S Q R using (module Diagram)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionUniversality 𝒯 M P using (module Transfer)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeCoreExtensions 𝒯 M P using (Factorization; module Extend)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconePostAssociativity 𝒯 M using (coconePost-assoc)

module Preservation (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L)
  {A B C D : CAT} {u : MAP A B} {v : MAP A C} {r : MAP B D} {s : MAP C D}
  (square : Square u v r s) (pushout : IsPushout square) where
  module Geom = Realization L Z using (category; localization; universal; into-groupoid)
  module Facts = Consequences L Z using (realization-isAn)
  module DiagramData = Diagram L Z square using (module Action; module Image; comparison)
  open DiagramData using (module Action; module Image)
  abstract
    original-extensions : CoconeExtensionProperty (squareCocone square)
    original-extensions = pushout-extension-property square pushout

  module Transferred = Transfer u v (Action.action u) (Action.action v)
    (Geom.localization A) (Geom.localization B) (Geom.localization C) (Action.naturality u) (Action.naturality v)
    (squareCocone square) (squareCocone Image.value) (Geom.localization D)
    original-extensions DiagramData.comparison using (module At; reflect)

  abstract
    restriction-isEquiv : (X Y : CAT) → isAn Y → IsEquiv (mapPre {D = Y} (Geom.localization X))
    restriction-isEquiv X Y yAn = Restrict.mapping-isEquiv (Geom.localization X) Y
      (Geom.into-groupoid X Y (anima-isGroupoid yAn))

  abstract
    anima-factorization : (Y : CAT) → isAn Y →
      (q : Cocone (Action.action u) (Action.action v) Y) → Factorization (squareCocone Image.value) q
    anima-factorization Y yAn q = record
      { functor = At.Factor.functor q ; comparison = At.Factor.comparison q }
      where
      module At = Transferred.At Y
        (restriction-isEquiv A Y yAn) (restriction-isEquiv B Y yAn)
        (restriction-isEquiv C Y yAn) (restriction-isEquiv D Y yAn) using (module Factor)

    reflection : (Y : CAT) (F G : MAP (Geom.category D) Y) →
      CoconeIso (coconePost F (squareCocone Image.value)) (coconePost G (squareCocone Image.value)) → F =₁ G
    reflection Y = Transferred.reflect
      (Universal.restriction-reflects L (allMorphisms D) (Geom.localization D) (Geom.universal D))

    extensions : CoconeExtensionProperty (squareCocone Image.value)
    extensions = Extend.extensions (squareCocone Image.value)
      (Facts.realization-isAn B) (Facts.realization-isAn C) coreInclusion-isEmbedding anima-factorization reflection

    preserves-pushout : IsPushout Image.value
    preserves-pushout = cocone-extension→pushout Image.value extensions
```
