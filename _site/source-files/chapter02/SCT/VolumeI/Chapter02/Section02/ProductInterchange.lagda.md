# Interchange for a functor of two variables

Both routes are compared with the image of the paired family. Product
composition and the two unit laws retain the chosen endpoint frames.
The categorical parameter P is arbitrary.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section02.ProductInterchange where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; MorphismFamilyIdentification; identity-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (compose-family-comparisons; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcomposition using (post-family-comparison)
open import SCT.VolumeI.Chapter02.Section02.ProductMorphismFamilies using (pair-morphism-family; module ProductComposition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits using (module MorphismCompositionUnits)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionPostcomposition using (module FunctorComposition)
open import SCT.VolumeI.Chapter02.Section02.FixedInputMorphismFamilies using (pair-family-comparison)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module At {Γ : Context} {P A B C : CAT Γ} (K : MAP (A × B) C)
  {x x′ : MAP P A} {y y′ : MAP P B}
  (alpha : MorphismFamily x x′) (beta : MorphismFamily y y′) where
  private
    module Target = MC.Composition C (segal-isEquiv C) using (compose)
    module Product = ProductComposition A B (segal-isEquiv (A × B)) (segal-isEquiv A) (segal-isEquiv B)
      using (product-composition)
    module LeftUnit = MorphismCompositionUnits A (segal-isEquiv A) using (source-unit; target-unit)
    module RightUnit = MorphismCompositionUnits B (segal-isEquiv B) using (source-unit; target-unit)
    module Image = FunctorComposition K (segal-isEquiv (A × B)) (segal-isEquiv C) using (preserves-composition)
    first = pair-morphism-family alpha (identity-family y)
    second = pair-morphism-family (identity-family x′) beta
    third = pair-morphism-family (identity-family x) beta
    fourth = pair-morphism-family alpha (identity-family y′)
  top : MorphismFamily (K ∘ pair x y) (K ∘ pair x′ y)
  top = map-morphism-family K first
  right : MorphismFamily (K ∘ pair x′ y) (K ∘ pair x′ y′)
  right = map-morphism-family K second
  left : MorphismFamily (K ∘ pair x y) (K ∘ pair x y′)
  left = map-morphism-family K third
  bottom : MorphismFamily (K ∘ pair x y′) (K ∘ pair x′ y′)
  bottom = map-morphism-family K fourth
  diagonal : MorphismFamily (K ∘ pair x y) (K ∘ pair x′ y′)
  diagonal = map-morphism-family K (pair-morphism-family alpha beta)

  first-route : MorphismFamilyIdentification One (Target.compose right top) diagonal
  first-route = compose-family-comparisons
    (post-family-comparison K (pair-family-comparison (LeftUnit.target-unit alpha) (RightUnit.source-unit beta)))
    (compose-family-comparisons
      (post-family-comparison K (Product.product-composition (identity-family x′) alpha beta (identity-family y)))
      (inverse-family-comparison (Image.preserves-composition second first)))
  second-route : MorphismFamilyIdentification One (Target.compose bottom left) diagonal
  second-route = compose-family-comparisons
    (post-family-comparison K (pair-family-comparison (LeftUnit.source-unit alpha) (RightUnit.target-unit beta)))
    (compose-family-comparisons
      (post-family-comparison K (Product.product-composition alpha (identity-family x) (identity-family y′) beta))
      (inverse-family-comparison (Image.preserves-composition fourth third)))
  comparison : MorphismFamilyIdentification One (Target.compose right top) (Target.compose bottom left)
  comparison = compose-family-comparisons (inverse-family-comparison second-route) first-route
```
