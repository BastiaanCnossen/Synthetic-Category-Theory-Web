# Functoriality of localization

This is `cons:Functoriality_Localization`. Compose the given functor
with the target localization, then factor through the source localization.
The comparison records the displayed square in the manuscript; reflection
after restriction compares any other factorization with the chosen one.

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

module SCT.VolumeI.Chapter03.Section03.LocalizationFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
  using (CAT; MAP; _∘_; _=₁_; _⁻¹; _∙_)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (MorphismCollection; PreservesMorphisms; composition-preserves)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphisms)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)

module Induced (L : SubcategoryAxiom) {C D : CAT}
  (V : MorphismCollection C) (W : MorphismCollection D)
  (source : WithSubcategories.Localization L V) (target : WithSubcategories.Localization L W)
  (f : MAP C D) (preserves : PreservesMorphisms f V W) where
  open WithSubcategories L
  module Source = Localization source
  module Target = Localization target
  module UP = Universal L V Source.functor Source.isLocalization using (module Factor; restriction-reflects)
  composite-inverts : Inverts (Target.functor ∘ f) V
  composite-inverts = composition-preserves f Target.functor
    {U = V} {V = W} {W = isomorphisms Target.category} preserves (IsLocalization.inverts Target.isLocalization)
  module Factor = UP.Factor (Target.functor ∘ f) composite-inverts
    using (factor; comparison)

  functor : MAP Source.category Target.category
  functor = Factor.factor

  comparison : (functor ∘ Source.functor) =₁ (Target.functor ∘ f)
  comparison = Factor.comparison

  unique : (g : MAP Source.category Target.category) →
    (g ∘ Source.functor) =₁ (Target.functor ∘ f) → g =₁ functor
  unique g α = UP.restriction-reflects g functor (comparison ⁻¹ ∙ α)
```
