# The absolute join pushout in product coordinates

Replace the fiber product over the terminal category by `C × D` and
distribute its interval boundary. This gives the usual two attaching
maps from `C × D`, with the chosen join as pushout and its original
boundary inclusion. The cocone keeps the transported commutativity
identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroℕ)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.NormalizedJoinPushout
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.PullbackProducts 𝒯 P using (module PullbackProduct)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (Square)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (IsPushout)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (functorOut)
open import SCT.VolumeI.Chapter01.Section08.MappingOutOfPushouts 𝒯 M ℱ P using (pushout→functor-criterion)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpanCoordinates 𝒯 M ℱ B P U I J using (insert; module Coordinates)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoconeUniversalTransport 𝒯 M ℱ P using (module Invariant)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J using (inclusion)

module Normalized (C D : CAT) where
  module Product = PullbackProduct C D
  module Changed = Coordinates (terminate C) (terminate D) one-isAn
    Product.fromProduct Product.productCone-isPullback pr₁ pr₂
    (pullbackLift-β₁ Product.productCone) (pullbackLift-β₂ Product.productCone) using (top; bottom; module Universal)
  top : MAP ((C × D) ⊔ (C × D)) ((C × D) × [1])
  top = Changed.top
  bottom : MAP ((C × D) ⊔ (C × D)) (C ⊔ D)
  bottom = Changed.bottom
  cylinder : MAP ((C × D) × [1]) (C ⋆ D)
  cylinder = Cocone.left Changed.Universal.cocone
  boundary : MAP (C ⊔ D) (C ⋆ D)
  boundary = inclusion (terminate C) (terminate D)
  cocone : Cocone top bottom (C ⋆ D)
  cocone = coconeRetarget Changed.Universal.cocone cylinder boundary
    (idIso cylinder) (comp-unitʳ boundary)
  square : Square top bottom cylinder boundary
  square = record { commute = Cocone.match cocone }
  abstract
    extensions : CoconeExtensionProperty cocone
    extensions = Invariant.extensions
      (coconeRetarget-β Changed.Universal.cocone cylinder boundary (idIso cylinder) (comp-unitʳ boundary))
      Changed.Universal.extensions
    isPushout : IsPushout square
    isPushout = cocone-extension→pushout square extensions
    functor-square-isPullback : (E : CAT) → IsPullback (functorOut square E)
    functor-square-isPullback = pushout→functor-criterion square isPushout
```
