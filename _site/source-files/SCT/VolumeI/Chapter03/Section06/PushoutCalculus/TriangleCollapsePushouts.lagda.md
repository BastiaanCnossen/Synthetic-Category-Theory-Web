# Collapsing a constant side of a square

The triangle pullback theorem identifies the two collapsed-square shapes
with `[2]`. We pass from evaluation at a vertex to restriction into
`Fun One D` through the terminal-domain equivalence. Constant arrows
form an embedding by the fundamental groupoid theorem, so the specified
matching of each shape square gives the same pullback property.

Here `p₀` collapses `[1] × {0}` and `p₂` collapses `[1] × {1}`.
These coordinate conventions are inherited from Chapter 2.

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
import SCT.VolumeI.Chapter01.Section05.Initial as Initial

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.TriangleCollapsePushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Walking.WalkingMorphism I using ([1])
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingConeInvariance 𝒯 P using (module ChangeRight)
open import SCT.VolumeI.Chapter01.Section07.TerminalDomain 𝒯 M ℱ using (module TerminalContext)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (Square)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (IsPushout)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (functorOut)
open import SCT.VolumeI.Chapter01.Section08.MappingOutOfPushouts 𝒯 M ℱ P using (functor-criterion→pushout)
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareRetractions 𝒯 M ℱ P I E Q
  using (p₀; p₂; insert; zero; one; d₁; d₂; d₀; s₀; s₁; s₀-d₂; s₁-d₀;
    vertex₀; vertex₂; d₁-zero; d₁-one; lower-cocone; upper-cocone; glue-bottom; glue-top)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open import SCT.VolumeI.Chapter02.Section02.TrianglePullbacks 𝒯 M ℱ P I E S Q using (module At)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (full-subcategory-isEmbedding)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section04.FundamentalGroupoids 𝒯 M ℱ P I E S Q R N using (module Consequences)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.ConstantFullSubcategory 𝒯 M ℱ P I E S Q R using (constant-restrict)

left-square : Square (insert zero) (terminate [1]) p₀ vertex₀
left-square = record { commute = (d₁-zero ▷ terminate [1]) ∙
  ((comp-assoc (terminate [1]) zero d₁) ⁻¹ ∙
    ((d₁ ◁ s₀-d₂) ∙ (comp-assoc d₂ s₀ d₁ ∙ glue-bottom lower-cocone))) }
right-square : Square (insert one) (terminate [1]) p₂ vertex₂
right-square = record { commute = (d₁-one ▷ terminate [1]) ∙
  ((comp-assoc (terminate [1]) one d₁) ⁻¹ ∙
    ((d₁ ◁ s₁-d₀) ∙ (comp-assoc d₀ s₁ d₁ ∙ glue-top upper-cocone))) }

module Collapse (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  module Known = Consequences L Z using (identityArrow-isFullSubcategory)
  module Into (D : CAT) where
    module Point = TerminalContext D
    termination = funPre {D = D} (terminate [1])
    abstract
      constant-comparison : (identityArrow ∘ Point.backward) =₁ termination
      constant-comparison = comp-unitʳ termination ∙
        ((termination ◁ Point.forward-backward) ∙
          (comp-assoc Point.backward Point.forward termination ∙
            ((constant-restrict {D = D} (terminate [1])) ⁻¹ ▷ Point.backward)))
      constant-isEmbedding : IsEmbedding (identityArrow {D})
      constant-isEmbedding = full-subcategory-isEmbedding identityArrow
        (Known.identityArrow-isFullSubcategory D)
    module Left = ChangeRight Point.backward Point.backward-isEquiv constant-comparison
      constant-isEmbedding (functorOut left-square D) (At.Left.vertex-square D)
      (idIso (funPre p₀)) (At.Left.vertex-square-isPullback D)
    module Right = ChangeRight Point.backward Point.backward-isEquiv constant-comparison
      constant-isEmbedding (functorOut right-square D) (At.Right.vertex-square D)
      (idIso (funPre p₂)) (At.Right.vertex-square-isPullback D)
  abstract
    left-isPushout : IsPushout left-square
    left-isPushout = functor-criterion→pushout left-square Into.Left.source-isPullback
    right-isPushout : IsPushout right-square
    right-isPushout = functor-criterion→pushout right-square Into.Right.source-isPullback
```
