# Universal objects in fibers of Bousfield localizations

The base-changed adjoint section over an absolute object is an initial
object for a right Bousfield localization, and a terminal object for a
left Bousfield localization. We normalize the projection to the terminal
category before applying the adjunction characterization. This proves
`lem:Fibers_Of_Right_Reflector_Have_Initial_Objects` and its dual.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.LocalizationFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open Laws.PullbackStructure P
  using (Pullback; pullbackCone)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as Change
import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.AdjunctionCharacterization as Universal

module At {C D : CAT} (p : MAP C D) (d : Obj-abs D) where
  F = Pullback p d
  original = pullbackCone p d
  inclusion = Cone.left original
  τ = terminal-iso (Cone.right original) (terminate F)
  fiber-cone : Cone p d F
  fiber-cone = record
    { left = inclusion ; right = terminate F
    ; match = (d ◁ τ) ∙ Cone.match original }

  abstract
    comparison : ConeIso original fiber-cone
    comparison = record
      { leftIso = idIso inclusion ; rightIso = τ
      ; compatible = isoComp-unitʳ-at (Cone.match fiber-cone) ∙
          isoComp-cong (idIso (Cone.match fiber-cone)) (postWhisker-idIso p inclusion) }
    is-pullback : IsPullback fiber-cone
    is-pullback = pullback-cone-invariant comparison (pullbackCone-isPullback p d)

  module Initial {s : MAP D C} (w : LeftAdjointSection p s) where
    module Changed = Change.Left 𝒯 M ℱ P I E S Q R w d fiber-cone is-pullback
      using (section; value; original-section)
    object : Obj-abs F
    object = Changed.section
    image : (inclusion ∘ object) =₁ (s ∘ d)
    image = Changed.original-section
    isInitial : IsInitial object
    isInitial = Universal.left-adjoint-section-is-initial 𝒯 M ℱ P I E S Q object Changed.value

  module Terminal {s : MAP D C} (w : RightAdjointSection p s) where
    module Changed = Change.Right 𝒯 M ℱ P I E S Q R w d fiber-cone is-pullback
      using (section; value; original-section)
    object : Obj-abs F
    object = Changed.section
    image : (inclusion ∘ object) =₁ (s ∘ d)
    image = Changed.original-section
    isTerminal : IsTerminal object
    isTerminal = Universal.right-adjoint-section-is-terminal 𝒯 M ℱ P I E S Q object Changed.value
```
