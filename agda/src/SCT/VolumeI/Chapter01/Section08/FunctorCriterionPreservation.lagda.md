# Pushouts induce pullbacks of functor categories

To extend a functor-category cone with parameter `X`, uncurry it and
transpose its product cocone to a cocone with target `Fun X E`. The
pushout property extends this cocone; currying its transpose supplies
the desired factor. The same comparisons reflect isomorphisms of factors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.FunRestrictionCones as FunCones
import SCT.VolumeI.Chapter01.Section08.PushoutExtensions as Extensions
import SCT.VolumeI.Chapter01.Section08.FunctorCriterionDetection as Evaluation
import SCT.VolumeI.Chapter01.Section08.TransposedSquareEvaluation as Transposed
import SCT.VolumeI.Chapter01.Section08.CoconeTransposition as Transposition

module SCT.VolumeI.Chapter01.Section08.FunctorCriterionPreservation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeUniversality 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackCriterion 𝒯 P
open Laws.PullbackStructure P
module FC = FunCones 𝒯 M ℱ
module TC = Transposition 𝒯 M ℱ

module Preservation {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (extensions : CoconeExtensionProperty (squareCocone s)) (E : CAT) where
  square = functorOut s E
  ordinary = squareCocone s
  evaluate : {X : CAT} (h : MAP X (Fun D E)) →
    CoconeIso (FC.uncurryRestriction {u = u} {v = l} (conePre h square))
      (restrictionCocone s (funUncurry h))
  evaluate = Evaluation.Evaluated.fun-evaluate 𝒯 M ℱ P s E

  module Lift {X : CAT} (t : Cone (funPre {D = E} u) (funPre l) X) where
    raw = FC.uncurryRestriction {u = u} {v = l} t
    module TransposedCone = TC.UntransposeCocone {u = u} {v = l} raw
    extension = CoconeExtensionProperty.factor extensions (Fun X E) TransposedCone.value
    value = funCurry (transpose extension)

    abstract
      comparison : ConeIso (conePre value square) t
      comparison = FC.ReflectRestriction.comparison {u = u} {v = l} (conePre value square) t
        (coconeIso-compose TransposedCone.comparison
        (coconeIso-compose (TC.transposeCoconeIso {u = u} {v = l} (CoconeExtensionProperty.factor-β extensions (Fun X E) TransposedCone.value))
        (coconeIso-compose (coconeIso-inverse (Transposed.Evaluation.comparison 𝒯 M ℱ s extension))
        (coconeIso-compose (restriction-action s (funCurry-β (transpose extension)))
          (evaluate value)))))

  module Compare {X : CAT} (h k : MAP X (Fun D E))
    (Φ : ConeIso (conePre h square) (conePre k square)) where
    h′ = untranspose (funUncurry h)
    k′ = untranspose (funUncurry k)

    abstract
      transposed-comparison : CoconeIso
        (TC.transposeCocone {u = u} {v = l} (coconePost h′ ordinary))
        (TC.transposeCocone {u = u} {v = l} (coconePost k′ ordinary))
      transposed-comparison = coconeIso-compose
        (coconeIso-inverse (Transposed.Evaluation.comparison 𝒯 M ℱ s k′))
        (coconeIso-compose (coconeIso-inverse (restriction-action s (transpose-β (funUncurry k))))
        (coconeIso-compose (evaluate k)
        (coconeIso-compose (FC.uncurryRestrictionIso {u = u} {v = l} Φ)
        (coconeIso-compose (coconeIso-inverse (evaluate h))
        (coconeIso-compose (restriction-action s (transpose-β (funUncurry h)))
          (Transposed.Evaluation.comparison 𝒯 M ℱ s h′))))))

      ordinary-comparison : CoconeIso (coconePost h′ ordinary) (coconePost k′ ordinary)
      ordinary-comparison = TC.ReflectTransposedCocone.comparison
        (coconePost h′ ordinary) (coconePost k′ ordinary) transposed-comparison

      extension-comparison : NatIso h′ k′
      extension-comparison = CoconeExtensionProperty.reflect extensions (Fun X E)
        h′ k′ ordinary-comparison

      comparison : NatIso h k
      comparison = funIsoReflect h k
        (transpose-β (funUncurry k) ∙
          (transposeIso extension-comparison ∙ invIso (transpose-β (funUncurry h))))

  module Inverse = Lift (pbCone (funPre {D = E} u) (funPre l))

  abstract
    isPullback : IsPullback square
    isPullback = cone-isPullback-from-lifting square Inverse.value Inverse.comparison Compare.comparison

pushout→functor-criterion : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) → IsPushout s → FunctorCriterion s
pushout→functor-criterion s universal E = Preservation.isPullback s
  (Extensions.pushout-extension-property 𝒯 M P s universal) E
```
