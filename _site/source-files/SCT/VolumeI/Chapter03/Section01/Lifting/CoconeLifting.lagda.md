# Lifting a cocone through an embedding

If both legs of a cocone lift through an embedding, its specified
matching lifts as well. The result includes a comparison of whole
cocones, which will let us apply the Segal property without discarding
the middle-vertex identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section01.Lifting.CoconeLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module Lift {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (f : MAP D E) (ef : IsEmbedding f) (s : Cocone u v E)
  (l : FunctorLift f (Cocone.left s)) (r : FunctorLift f (Cocone.right s)) where
  p = FunctorLift.lift l
  q = FunctorLift.lift r
  wanted = coconeRetarget s (f ∘ p) (f ∘ q)
    ((FunctorLift.comparison l) ⁻¹) ((FunctorLift.comparison r) ⁻¹)
  leftChange = comp-assoc u p f
  rightChange = comp-assoc v q f
  desired = Cocone.match wanted
  matching = embedding-lift f ef (p ∘ u) (q ∘ v)
    (rightChange ∙ (desired ∙ leftChange ⁻¹))

  value : Cocone u v D
  value = record { left = p ; right = q ; match = FunctorLift.lift matching }

  abstract
    matching-image : Cocone.match (coconePost f value) =₂ desired
    matching-image = isoComp-unitʳ-at desired ∙
      (isoComp-cong (idIso desired) (isoComp-inverseˡ-at leftChange) ∙
      (isoComp-assoc-at desired (leftChange ⁻¹) leftChange ∙
      (isoComp-cong (cancel-left rightChange (desired ∙ leftChange ⁻¹)) (idIso leftChange) ∙
        ((isoComp-assoc-at (rightChange ⁻¹)
          (rightChange ∙ (desired ∙ leftChange ⁻¹)) leftChange) ⁻¹ ∙
          isoComp-cong (idIso (rightChange ⁻¹))
            (isoComp-cong (FunctorLift.comparison matching) (idIso leftChange))))))

    comparison : CoconeIso (coconePost f value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _
        ((FunctorLift.comparison l) ⁻¹) ((FunctorLift.comparison r) ⁻¹)))
      (cocone-match-change _ _ _ _ matching-image)
```
