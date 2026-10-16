# Interchange for natural transformations

Apply the internal composition functor to a paired transformation. Product
composition and the unit laws compare both routes, with common named-composite
comparisons at all four vertices. Fixed-input transfer gives the four actual
precomposition and postcomposition actions with their explicitly chosen frames.
Gluing their two complete triangle presentations supplies a framed square.

This proves the square and endpoint-preserving hom identification. Its square
is chosen by gluing. No equality with the manuscript proof's double-curried
square, or with the deferred draft's different frame choices, is asserted.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section02.Interchange where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family; retarget-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (id-family-comparison; inverse-family-comparison; compose-family-comparisons)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport using (module CompositionTransport)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
open import SCT.VolumeI.Chapter02.Section02.GluedFramedSquares using (module Glue)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares using (FramedSquare)
open import SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering using (pre-whisker; post-whisker)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
import SCT.VolumeI.Chapter02.Section02.InternalComposition as Internal
import SCT.VolumeI.Chapter02.Section02.ProductInterchange as Product
import SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering as Whiskering

module At {Γ : Context} {B C D : CAT Γ} {F G : MAP C D} {u v : MAP B C}
  (alpha : MorphismFamily (funName F) (funName G))
  (beta : MorphismFamily (funName u) (funName v)) where
  private
    module InternalAction = Internal.At B C D using (composeFunctor; module Named)
    module Base = Product.At {P = One} InternalAction.composeFunctor alpha beta
      using (top; right; left; bottom; comparison)
    module Top = Whiskering.Pre u alpha using (action; comparison)
    module Right = Whiskering.Post G beta using (action; comparison)
    module Left = Whiskering.Post F beta using (action; comparison)
    module Bottom = Whiskering.Pre v alpha using (action; comparison)
    module Chosen = MC.Composition (Fun B D) (segal-isEquiv (Fun B D)) using (compose)
    module Comparisons = CompositionComparisons (Fun B D) (segal-isEquiv (Fun B D))
      using (composition-comparison; composition-presentation)
    module Transport = CompositionTransport (Fun B D) (segal-isEquiv (Fun B D)) using (retarget-composition)
    k00 = InternalAction.Named.comparison F u
    k01 = InternalAction.Named.comparison G u
    k10 = InternalAction.Named.comparison F v
    k11 = InternalAction.Named.comparison G v
    paired-first = Chosen.compose (retarget-family Base.right k01 k11) (retarget-family Base.top k00 k01)
    transported-first = retarget-family (Chosen.compose Base.right Base.top) k00 k11
    transported-second = retarget-family (Chosen.compose Base.bottom Base.left) k00 k11
    paired-second = Chosen.compose (retarget-family Base.bottom k10 k11) (retarget-family Base.left k00 k10)
    first-edges : MorphismFamilyIdentification One (Chosen.compose Right.action Top.action) paired-first
    first-edges = inverse-family-comparison (Comparisons.composition-comparison Right.comparison Top.comparison)
    first-composite : MorphismFamilyIdentification One paired-first transported-first
    first-composite = inverse-family-comparison (Transport.retarget-composition Base.right Base.top k00 k01 k11)
    product-comparison : MorphismFamilyIdentification One transported-first transported-second
    product-comparison = retarget-family-comparison k00 k11 Base.comparison
    second-composite : MorphismFamilyIdentification One transported-second paired-second
    second-composite = Transport.retarget-composition Base.bottom Base.left k00 k10 k11
    second-edges : MorphismFamilyIdentification One paired-second (Chosen.compose Bottom.action Left.action)
    second-edges = Comparisons.composition-comparison Bottom.comparison Left.comparison

  comparison : MorphismFamilyIdentification One (Chosen.compose Right.action Top.action)
    (Chosen.compose Bottom.action Left.action)
  comparison = compose-family-comparisons second-edges
    (compose-family-comparisons second-composite
      (compose-family-comparisons product-comparison
        (compose-family-comparisons first-composite first-edges)))

  square : FramedSquare Top.action Right.action Left.action Bottom.action
  square = Glue.value (Comparisons.composition-presentation Right.action Top.action)
    (ReplacePresentation.value (Comparisons.composition-presentation Bottom.action Left.action)
      (id-family-comparison Left.action) (id-family-comparison Bottom.action)
      (inverse-family-comparison comparison))

module _ {Γ : Context} {B C D : CAT Γ} {F G : MAP C D} {u v : MAP B C} where
  interchange : (alpha : MorphismFamily (funName F) (funName G))
    (beta : MorphismFamily (funName u) (funName v)) → MorphismFamilyIdentification One
      (MC.Composition.compose (Fun B D) (segal-isEquiv (Fun B D)) (post-whisker G beta) (pre-whisker u alpha))
      (MC.Composition.compose (Fun B D) (segal-isEquiv (Fun B D)) (pre-whisker v alpha) (post-whisker F beta))
  interchange alpha beta = At.comparison alpha beta

  interchange-square : (alpha : MorphismFamily (funName F) (funName G))
    (beta : MorphismFamily (funName u) (funName v)) →
    FramedSquare (pre-whisker u alpha) (post-whisker G beta) (post-whisker F beta) (pre-whisker v alpha)
  interchange-square alpha beta = At.square alpha beta
```
