# Products preserve pushouts

Transpose a cocone on the product span into a functor category, extend
it through the original pushout, and transpose back. The comparison
between the two transposed squares retains the original matching. The
same argument reflects comparisons between extensions.

This is the distributivity over pushouts used when expanding iterated
joins in the associativity argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.ProductPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeTransposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TransposedSquareEvaluation 𝒯 M ℱ using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section08.PushoutExtensions 𝒯 M P using (module Extensions)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)

module Preservation {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  {r : MAP B D} {s : MAP C D} (square : Square u v r s) (ep : IsPushout square) (X : CAT) where
  product-square : Square (productRestriction X u) (productRestriction X v)
    (productRestriction X r) (productRestriction X s)
  product-square = record { commute = Cocone.match (productCocone X square) }

  module Into (E : CAT) where
    module Original = Extensions square ep (Fun X E) using (module Lift; module Compare)
    module Factor (t : Cocone (productRestriction X u) (productRestriction X v) E) where
      module Curried = UntransposeCocone t using (value; comparison)
      module Lifted = Original.Lift Curried.value using (value; comparison)
      functor : MAP (X × D) E
      functor = transpose Lifted.value
      abstract
        comparison : CoconeIso (coconePost functor (productCocone X square)) t
        comparison = coconeIso-compose Curried.comparison
          (coconeIso-compose (transposeCoconeIso Lifted.comparison)
            (coconeIso-inverse (Evaluation.comparison square Lifted.value)))

    module Compare (f g : MAP (X × D) E)
      (Φ : CoconeIso (restrictionCocone square f) (restrictionCocone square g)) where
      F = untranspose f
      G = untranspose g
      left = coconePost F (squareCocone square)
      right = coconePost G (squareCocone square)
      abstract
        transposed : CoconeIso (transposeCocone left) (transposeCocone right)
        transposed = coconeIso-compose (coconeIso-inverse (Evaluation.comparison square G))
          (coconeIso-compose (coconeIso-inverse (restriction-action square (transpose-β g)))
            (coconeIso-compose Φ
              (coconeIso-compose (restriction-action square (transpose-β f))
                (Evaluation.comparison square F))))
        curried : F =₁ G
        curried = Original.Compare.comparison F G
          (ReflectTransposedCocone.comparison left right transposed)
        comparison : f =₁ g
        comparison = transpose-β g ∙ (transposeIso curried ∙ (transpose-β f) ⁻¹)

  abstract
    extensions : CoconeExtensionProperty (productCocone X square)
    extensions = record { factor = Into.Factor.functor ; factor-β = Into.Factor.comparison
      ; reflect = Into.Compare.comparison }
    isPushout : IsPushout product-square
    isPushout = cocone-extension→pushout product-square extensions
```
