# Isomorphisms are cartesian and cocartesian

Composition with an isomorphism induces equivalences on hom categories,
and so does composition with its functorial image. Each defining square
is therefore a pullback. This proves the isomorphism assertion in
`lem:Cancellation_Cocartesian_Morphisms` for every functor.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section05.CocartesianIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.CocartesianMorphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I using (hom-post-β)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (IsInvertibleExpression; post-invertible; retarget-invertible; identified-invertible)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.LiftedInverseExpressions 𝒯 M ℱ P I E S
  using (lift-invertible-expression)
import SCT.VolumeI.Chapter02.Section06.HomCompositionDetection as Detection
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback; degenerate-pullback-converse)
import SCT.VolumeI.Chapter02.Section06.HomCompositionEquivalences as Equivalences

module AtIsomorphism {C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  (e : Obj-abs (Hom C x y)) (w : IsInvertibleExpression (hom-expression e)) where
  private
    module Square = Along F e using (cocartesian-square; cartesian-square; IsCocartesian; IsCartesian)
    module Original = Equivalences.InvertiblePoint 𝒯 M ℱ P I E S Q e
      (invertible-expression-lift (hom-expression e) w)
      using (precompose-isEquiv; postcompose-isEquiv)
    image = hom-post F x y ∘ e

    image-invertible : IsInvertibleExpression (hom-expression image)
    image-invertible = identified-invertible (expressionIso-inverse (hom-post-β F x y e))
      (retarget-invertible (post-expression F (hom-expression e))
        (constant-image One F x) (constant-image One F y)
        (post-invertible F (hom-expression e) w))

    module Mapped = Equivalences.InvertiblePoint 𝒯 M ℱ P I E S Q image
      (invertible-expression-lift (hom-expression image) image-invertible)
      using (precompose-isEquiv; postcompose-isEquiv)

  cocartesian : Square.IsCocartesian
  cocartesian z = degenerate-pullback (Mapped.precompose-isEquiv (F ∘ z))
    (Square.cocartesian-square z) (Original.precompose-isEquiv z)

  cartesian : Square.IsCartesian
  cartesian z = degenerate-pullback (Mapped.postcompose-isEquiv (F ∘ z))
    (Square.cartesian-square z) (Original.postcompose-isEquiv z)
```

If the image is invertible, cartesianness or cocartesianness also forces
the original morphism to be invertible. Pullback cancellation gives the
hom-composition equivalences, and the elementary Yoneda test detects an
inverse. Only the source and target tests are used in the last step.

```agda
module OverIsomorphism {C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  (e : Obj-abs (Hom C x y))
  (w : IsInvertibleExpression (hom-expression (hom-post F x y ∘ e))) where
  private
    module Square = Along F e using (cocartesian-square; cartesian-square; IsCocartesian; IsCartesian)
    module Mapped = Equivalences.InvertiblePoint 𝒯 M ℱ P I E S Q (hom-post F x y ∘ e)
      (invertible-expression-lift (hom-expression (hom-post F x y ∘ e)) w)
      using (precompose-isEquiv; postcompose-isEquiv)

  cocartesian-isomorphism : Square.IsCocartesian → IsInvertibleExpression (hom-expression e)
  cocartesian-isomorphism u = lift-invertible-expression (hom-expression e)
    (Detection.Detect.FromPre.lift 𝒯 M ℱ P I E S Q e (test x) (test y))
    where
    test : (z : Obj-abs C) → IsEquiv (At.precompose e z)
    test z = degenerate-pullback-converse (Mapped.precompose-isEquiv (F ∘ z))
      (Square.cocartesian-square z) (u z)

  cartesian-isomorphism : Square.IsCartesian → IsInvertibleExpression (hom-expression e)
  cartesian-isomorphism u = lift-invertible-expression (hom-expression e)
    (Detection.Detect.FromPost.lift 𝒯 M ℱ P I E S Q e (test x) (test y))
    where
    test : (z : Obj-abs C) → IsEquiv (At.postcompose e z)
    test z = degenerate-pullback-converse (Mapped.postcompose-isEquiv (F ∘ z))
      (Square.cartesian-square z) (u z)
```
