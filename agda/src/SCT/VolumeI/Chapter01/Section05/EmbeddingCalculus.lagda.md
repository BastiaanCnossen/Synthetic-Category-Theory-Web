# Base change and cancellation for embeddings

The first projection of the self-pullback characterizes embeddings.
Nested pullbacks and boundary changes therefore prove the base-change
and left-cancellation statements by two-out-of-three.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.EmbeddingCalculus
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.Embeddings 𝒯 P public
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P using (IsPullback; pbCone-isPullback)
open import SCT.VolumeI.Chapter01.Section05.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section05.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section05.NestedPullbacks 𝒯 P using (module Nested)
import SCT.VolumeI.Chapter01.Section05.UniversalNestedPullbacks as UniversalNested
open import SCT.VolumeI.Chapter01.Section05.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section05.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section05.CospanEquivalences 𝒯 P using (module CospanEquivalence)

equivalence-isEmbedding : {C D : CAT} (f : MAP C D) → IsEquiv f → IsEmbedding f
equivalence-isEmbedding f ef = projection-embedding f (pullback-equivalence f f ef)

embedding-cong : {C D : CAT} {f g : MAP C D} → =₁ f g → IsEmbedding f → IsEmbedding g
embedding-cong {C} {D} {f} {g} α ef = projection-embedding g
  (equiv-cancel-right F.pullbackMap pb₁ E.pullbackMap-isEquiv
    (equiv-transport (invIso (comp-unitˡ pb₁ ∙ pbLift-β₁ (F.mapCone (pbCone f f))))
      (embedding-projection f ef)))
  where
  boundary = invIso (comp-unitˡ f) ∙ (invIso α ∙ comp-unitʳ g)
  cospan : CospanMap f f g g
  cospan = record { left = id C ; right = id C ; base = id D
    ; leftSquare = boundary ; rightSquare = boundary }
  module F = CospanMap cospan
  module E = CospanEquivalence cospan (id-isEquiv C) (id-isEquiv C) (id-isEquiv D)

nested-projection : {A B X Z : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z) →
  IsEquiv (pb₁ {f = g} {h}) → IsEquiv (pb₁ {f = g ∘ f} {h})
nested-projection f g h ep = equiv-transport (pbLift-β₁ N.insertionCone)
  (equiv-compose N.insert pb₁ N.insert-isEquiv (pullback-equivalence f N.u ep))
  where
  module N = Nested f g h

auxiliaryCone : {C D E : CAT} (f : MAP C D) (g : MAP D E) → Cone (g ∘ f) g C
auxiliaryCone {C} f g = record { left = id C ; right = f ; match = comp-unitʳ (g ∘ f) }

auxiliary-isPullback : {C D E : CAT} (f : MAP C D) (g : MAP D E) →
  IsEmbedding g → IsPullback (auxiliaryCone f g)
auxiliary-isPullback f g eg = equiv-cancel-left (pbLift (auxiliaryCone f g)) pb₁
  (nested-projection f g g (embedding-projection g eg))
  (equiv-transport (invIso (pbLift-β₁ (auxiliaryCone f g))) (id-isEquiv _))

module LeftCancellation {C D E : CAT} (f : MAP C D) (g : MAP D E) (eg : IsEmbedding g) where

  t = coneSwap (auxiliaryCone f g)
  et = pullback-swap (auxiliaryCone f g) (auxiliary-isPullback f g eg)
  module N = UniversalNested.Nested 𝒯 P f g (g ∘ f) t et

  compose : IsEmbedding f → IsEmbedding (g ∘ f)
  compose ef = projection-embedding (g ∘ f)
    (equiv-cancel-right N.flatten pb₁ N.flatten-isEquiv
      (equiv-transport (invIso (pbLift-β₁ N.flatCone)) (embedding-projection f ef)))

  cancel : IsEmbedding (g ∘ f) → IsEmbedding f
  cancel egf = projection-embedding f
    (equiv-transport (pbLift-β₁ N.flatCone)
      (equiv-compose N.flatten pb₁ N.flatten-isEquiv (embedding-projection (g ∘ f) egf)))

chosen-base-change-embedding : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEmbedding g → IsEmbedding (pb₁ {f = f} {g})
chosen-base-change-embedding f g eg = projection-embedding p
  (equiv-transport (pbLift-β₁ N.flatCone)
    (equiv-compose N.flatten pb₁ N.flatten-isEquiv outerProjection))
  where
  p = pb₁ {f = f} {g}
  q = pb₂ {f = f} {g}
  module N = Nested p f g
  module Change = ChangeLeft (pbMatch {f = f} {g}) g
  otherProjection = nested-projection q g g (embedding-projection g eg)
  outerProjection = equiv-transport (pbLift-β₁ (changeLeft (pbMatch {f = f} {g}) (pbCone (f ∘ p) g)))
    (equiv-compose Change.forward pb₁ Change.forward-isEquiv otherProjection)

base-change-embedding : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → IsPullback s → IsEmbedding g → IsEmbedding (Cone.left s)
base-change-embedding {f = f} {g} s es eg = embedding-cong (pbLift-β₁ s)
  (LeftCancellation.compose (pbLift s) pb₁ (chosen-base-change-embedding f g eg)
    (equivalence-isEmbedding (pbLift s) es))

chosen-base-change-embeddingʳ : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEmbedding f → IsEmbedding (pb₂ {f = f} {g})
chosen-base-change-embeddingʳ f g ef = base-change-embedding (coneSwap (pbCone f g))
  (pullback-swap (pbCone f g) (pbCone-isPullback f g)) ef

module RelativeEmbedding {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (ef : IsEmbedding f) where

  projection = chosen-base-change-embeddingʳ f g ef

  to-factorization : IsEmbedding (Cone.right s) → IsEmbedding (pbLift s)
  to-factorization eu = LeftCancellation.cancel (pbLift s) pb₂ projection
    (embedding-cong (invIso (pbLift-β₂ s)) eu)

  from-factorization : IsEmbedding (pbLift s) → IsEmbedding (Cone.right s)
  from-factorization eh = embedding-cong (pbLift-β₂ s)
    (LeftCancellation.compose (pbLift s) pb₂ projection eh)
```
