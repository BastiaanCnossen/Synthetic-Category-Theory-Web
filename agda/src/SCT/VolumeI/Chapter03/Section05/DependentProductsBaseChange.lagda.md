# Dependent products are preserved by base change

Pull the evaluation triangle across a specified pullback square. The
mapping-anima comparison proves that this pulled triangle is itself a
dependent product. Uniqueness then identifies it with any chosen
dependent product over the new base, and proves that the manuscript's
actual Beck–Chevalley comparison is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.DependentProductsBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalley 𝒯 M ℱ P using (module BeckChevalley)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyMapping 𝒯 M ℱ P using (module Stability)

module BaseChange {S T S′ T′ C : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (f : MAP C S)
  (Π : DependentProduct p f) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  module Proof = Stability p b square square-isPullback g f ε

  dependent-product : DependentProduct (Cone.right square) (pullback₂ {f = f} {Cone.left square})
  dependent-product = record
    { category = Pullback g b ; projection = Proof.t ; evaluation = Proof.pulled
    ; isDependentProduct = Proof.universal (DependentProduct.isDependentProduct Π) }

  abstract
    beck-chevalley-isEquiv :
      (Π′ : DependentProduct (Cone.right square) (pullback₂ {f = f} {Cone.left square})) →
      IsEquiv (BeckChevalley.functor p b square f Π Π′)
    beck-chevalley-isEquiv Π′ = BeckChevalley.from-pulled-universal-property p b square f Π Π′
      (Proof.universal (DependentProduct.isDependentProduct Π))
```
