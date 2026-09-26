# Localization as a pushout

This proves `exercise:Localization_As_Pushout`. The parameter anima is
written before the interval, so the uncurried arrow family has domain
`W × [1]`. Given a cocone, its left leg inverts `W` and therefore factors
through the localization. Lift the required right-leg identification
through restriction along `W × [1] → W`. Its prescribed image proves
compatibility with the original commutativity identification.

Comparison of two extensions follows by restricting to the localization
map. Testing all target categories supplies the full pushout property.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.LocalizationPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)
open import SCT.VolumeI.Chapter03.Section03.PushoutCalculus.LocalizationCocones 𝒯 M ℱ P I E S Q R using (module Family)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.ConstantRestriction 𝒯 M ℱ P I E S Q R using (module Restriction)

module Pushout (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
  (l : MAP C T) (localization : WithSubcategories.IsLocalization L W l) where
  module UP = Universal L W l localization using (inverts; module Factor; restriction-reflects)
  module Diagram = Family W
  module Canonical = Diagram.FromInverting l UP.inverts
  cocone = Canonical.cocone
  square : Square Diagram.arrows Diagram.projection l Canonical.right
  square = record { commute = Canonical.matching }

  module Factor {D : CAT} (s : Cocone Diagram.arrows Diagram.projection D) where
    module Inverts = Diagram.FromCocone s
    module Extension = UP.Factor (Cocone.left s) Inverts.inverts
    functor = Extension.factor
    induced = coconePost functor cocone
    left = Extension.comparison
    σ = Cocone.match induced
    desired = Cocone.match s ∙ (left ▷ Diagram.arrows)
    raw = desired ∙ (σ ⁻¹)
    module Right = Restriction.Identification Diagram.X D Diagram.xAn
      (Cocone.right induced) (Cocone.right s) raw
    abstract
      matching : desired =₂ ((Right.lift ▷ Diagram.projection) ∙ σ)
      matching = (isoComp-unitʳ-at desired ∙
        (isoComp-cong (idIso desired) (isoComp-inverseˡ-at σ) ∙
          (isoComp-assoc-at desired (σ ⁻¹) σ ∙
            isoComp-cong Right.image (idIso σ)))) ⁻¹
      comparison : CoconeIso induced s
      comparison = record { leftIso = left ; rightIso = Right.lift ; compatible = matching }

  abstract
    extensions : CoconeExtensionProperty cocone
    extensions = record
      { factor = λ D s → Factor.functor s
      ; factor-β = λ D s → Factor.comparison s
      ; reflect = λ D f g Φ → UP.restriction-reflects f g (CoconeIso.leftIso Φ) }
    isPushout : IsPushout square
    isPushout = cocone-extension→pushout square extensions
```
