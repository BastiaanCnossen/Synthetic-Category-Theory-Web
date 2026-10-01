# Composing an adjoint section with a base change

Suppose a functor factors, with a specified identification, through a
base change of a Bousfield localization. Compose its adjoint section
with the base-changed section and transport along that identification.
The resulting section is identified with this explicit composite.
Keeping this construction generic avoids expanding a particular chosen
pullback while checking the adjunction formulas.

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

module SCT.VolumeI.Chapter04.Section04.CompositeBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter04.Section04.CompositeAdjunctions 𝒯 M ℱ P I E S Q
  using (compose-left-adjoint-section; compose-right-adjoint-section)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as Change
import SCT.VolumeI.Chapter04.Section04.LocalizationInvariance as Invariance

module Along {A B C D T : CAT} {p : MAP A T} {q : MAP B C} {v : MAP D C} {r : MAP A D}
  (t : Cone q v T) (et : IsPullback t) (α : (Cone.right t ∘ p) =₁ r) where

  module Right (wp : RightBousfieldLocalization p) (wq : RightBousfieldLocalization q) where
    private
      module W = RightBousfieldLocalization wp using (section; left-adjoint-section)
      module Changed = Change.Left 𝒯 M ℱ P I E S Q R
        (RightBousfieldLocalization.left-adjoint-section wq) v t et
        using (section; value)
    intermediate-section : MAP D T
    intermediate-section = Changed.section
    abstract
      composite : RightBousfieldLocalization (Cone.right t ∘ p)
      composite = record { section = W.section ∘ intermediate-section
        ; left-adjoint-section = compose-left-adjoint-section W.left-adjoint-section Changed.value }
      value : RightBousfieldLocalization r
      value = Invariance.Along.right 𝒯 M ℱ P I E S Q R α composite
      section-comparison : RightBousfieldLocalization.section value =₁ (W.section ∘ intermediate-section)
      section-comparison = Invariance.Along.right-section 𝒯 M ℱ P I E S Q R α composite

  module Left (wp : LeftBousfieldLocalization p) (wq : LeftBousfieldLocalization q) where
    private
      module W = LeftBousfieldLocalization wp using (section; right-adjoint-section)
      module Changed = Change.Right 𝒯 M ℱ P I E S Q R
        (LeftBousfieldLocalization.right-adjoint-section wq) v t et
        using (section; value)
    intermediate-section : MAP D T
    intermediate-section = Changed.section
    abstract
      composite : LeftBousfieldLocalization (Cone.right t ∘ p)
      composite = record { section = W.section ∘ intermediate-section
        ; right-adjoint-section = compose-right-adjoint-section W.right-adjoint-section Changed.value }
      value : LeftBousfieldLocalization r
      value = Invariance.Along.left 𝒯 M ℱ P I E S Q R α composite
      section-comparison : LeftBousfieldLocalization.section value =₁ (W.section ∘ intermediate-section)
      section-comparison = Invariance.Along.left-section 𝒯 M ℱ P I E S Q R α composite
```
