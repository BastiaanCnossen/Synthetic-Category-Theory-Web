# Dependent products preserve embeddings

For `cor:Dependent_Product_Preserves_Embeddings`, use the specified-lift
characterization of embeddings. Two functors over an embedded base have
an identification retaining their triangles. Apply this to the evaluated
functors and reflect through relative currying. The resulting
identification has the prescribed image in the new base, which proves
that the dependent-product projection is an embedding.

This gives a direct proof of the manuscript's corollary. It applies to
any supplied dependent product; exponentiability is only needed to
supply the product.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.Section05.DependentProductEmbeddings
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingRecognition 𝒯 P using (module Criterion)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)

module EmbeddedTarget {C S : CAT} (f : MAP C S) (ef : IsEmbedding f)
  {X : CAT} {t : MAP X S} (u v : FunctorOver t f) where
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  chosen = embedding-lift f ef (FunctorLift.lift u) (FunctorLift.lift v) (θv ⁻¹ ∙ θu)

  abstract
    comparison : FunctorOverIso u v
    comparison = record { underlying = FunctorLift.lift chosen
      ; compatible = cancel-inverse θv θu ∙ isoComp-cong (idIso θv) (FunctorLift.comparison chosen) }

module Product {S T C : CAT} (p : MAP S T) (f : MAP C S) (ef : IsEmbedding f)
  (Π : DependentProduct p f) where
  D = DependentProduct.category Π
  g = DependentProduct.projection Π
  module Native = Currying.Native p f Π

  module Lift {X : CAT} (h k : MAP X D) (α : (g ∘ h) =₁ (g ∘ k)) where
    u : FunctorOver (g ∘ k) g
    u = record { lift = h ; comparison = α }
    v : FunctorOver (g ∘ k) g
    v = record { lift = k ; comparison = idIso (g ∘ k) }
    Φ : FunctorOverIso u v
    Φ = Native.reflect (g ∘ k) u v
      (EmbeddedTarget.comparison f ef (Currying.evaluate p f Π u) (Currying.evaluate p f Π v))

    abstract
      lifted : FunctorLift (postWhisker g) α
      lifted = record { lift = FunctorOverIso.underlying Φ
        ; comparison = FunctorOverIso.compatible Φ ∙ (isoComp-unitˡ-at (g ◁ FunctorOverIso.underlying Φ)) ⁻¹ }

  abstract
    projection-isEmbedding : IsEmbedding g
    projection-isEmbedding = Criterion.isEmbedding g Lift.lifted
```
