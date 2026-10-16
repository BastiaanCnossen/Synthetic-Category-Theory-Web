# The naturality square with prescribed endpoints

Apply the arrow-valued functor of a natural transformation to a morphism
family. Its two endpoint images are compared with the images under the
original functors, using the same transformation endpoint identifications.
This gives the transpose of the manuscript's displayed naturality square.
Its commutativity comparison has the manuscript's orientation and retains
both endpoint equations.

The parameter category is arbitrary. In particular the family theorem
applies to another natural transformation. An actual square in the functor
category, with its chosen double-curried witness and named endpoints,
remains a separate construction in the continuation of this owner.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.NaturalTransformationNaturality where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (restrict-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcompositionPasting using (module Pasting)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares using (FramedSquare; framed-square)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
import SCT.VolumeI.Chapter02.Section02.FramedSquareCommutativity as SquareCommutativity

module NaturalitySquare {Γ : Context} {P C D : CAT Γ} {F G : MAP C D}
  (alpha : MorphismFamily F G) {a b : MAP P C} (u : MorphismFamily a b) where
  private
    module Transformation = MorphismFamily alpha

  top : MorphismFamily (F ∘ a) (F ∘ b)
  top = map-morphism-family F u
  right : MorphismFamily (F ∘ b) (G ∘ b)
  right = restrict-family alpha b
  left : MorphismFamily (F ∘ a) (G ∘ a)
  left = restrict-family alpha a
  bottom : MorphismFamily (G ∘ a) (G ∘ b)
  bottom = map-morphism-family G u

  vertical : MorphismFamily (MorphismFamily.arrow left) (MorphismFamily.arrow right)
  vertical = map-morphism-family Transformation.arrow u

  value : FramedSquare top right left bottom
  value = framed-square vertical
    (Pasting.comparison Transformation.arrow ev₀ F Transformation.source-frame u)
    (Pasting.comparison Transformation.arrow ev₁ G Transformation.target-frame u)

module _ {Γ : Context} {P C D : CAT Γ} {F G : MAP C D} where
  naturality : (alpha : MorphismFamily F G) {a b : MAP P C} (u : MorphismFamily a b)
    → MorphismFamilyIdentification One
        (MC.Composition.compose D (segal-isEquiv D)
          (map-morphism-family G u) (restrict-family alpha a))
        (MC.Composition.compose D (segal-isEquiv D)
          (restrict-family alpha b) (map-morphism-family F u))
  naturality alpha u = SquareCommutativity.comparison D (segal-isEquiv D)
    (NaturalitySquare.value alpha u)
```
