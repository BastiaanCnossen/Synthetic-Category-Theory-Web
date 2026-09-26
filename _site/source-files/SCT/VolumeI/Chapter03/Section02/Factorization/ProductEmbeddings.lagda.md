# Products of embeddings

Changing one factor of a product is base change. Change the two factors
successively and use closure of embeddings under composition. This is
the embedding fact needed for collections of objects.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section02.Factorization.ProductEmbeddings
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P
  using (module FirstFactor; module SecondFactor)

product-first-isEmbedding : {A B : CAT} (f : MAP A B) (C : CAT) →
  IsEmbedding f → IsEmbedding (productMap f (id C))
product-first-isEmbedding f C ef = base-change-embedding (coneSwap (FirstFactor.square f C))
  (pullback-swap (FirstFactor.square f C) (FirstFactor.square-isPullback f C)) ef

product-second-isEmbedding : (A : CAT) {B C : CAT} (f : MAP B C) →
  IsEmbedding f → IsEmbedding (productMap (id A) f)
product-second-isEmbedding A f ef = base-change-embedding (coneSwap (SecondFactor.square A f))
  (pullback-swap (SecondFactor.square A f) (SecondFactor.square-isPullback A f)) ef

productMap-isEmbedding : {A B C D : CAT} (f : MAP A B) (g : MAP C D) →
  IsEmbedding f → IsEmbedding g → IsEmbedding (productMap f g)
productMap-isEmbedding {B = B} {C} f g ef eg =
  embedding-cong (productMap-cong (comp-unitˡ f) (comp-unitʳ g) ∙ productMap-comp f (id B) (id C) g)
    (LeftCancellation.compose (productMap f (id C)) (productMap (id B) g)
      (product-second-isEmbedding B g eg) (product-first-isEmbedding f C ef))
```

An equivalence in each coordinate also gives an equivalence on products.
The inverse is the product of the two inverse functors.

```agda
productMap-isEquiv : {A B C D : CAT} (f : MAP A B) (g : MAP C D) →
  IsEquiv f → IsEquiv g → IsEquiv (productMap f g)
productMap-isEquiv {A} {B} {C} {D} f g ef eg = record
  { inverse = productMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
  ; sectionIso = (productMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ⁻¹ ∙
      (productMap-cong (IsEquiv.sectionIso ef) (IsEquiv.sectionIso eg) ∙ (productMap-id A C) ⁻¹)
  ; retractionIso = (productMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ⁻¹ ∙
      (productMap-cong (IsEquiv.retractionIso ef) (IsEquiv.retractionIso eg) ∙ (productMap-id B D) ⁻¹) }
```
