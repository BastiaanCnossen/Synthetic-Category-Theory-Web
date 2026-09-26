# Changing a cospan along an embedding of its base

Equivalences on the two ends and an embedding on the base induce an
equivalence of pullbacks. A square with an equivalence on its left leg
and an embedding on its bottom leg is already a pullback: its canonical
projection is an embedding with a section. The cartesian-cospan lemma
then applies with the specified square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.CospanEmbeddings
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanCartesian 𝒯 P

embedding-degenerate-pullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E} →
  IsEmbedding g → (s : Cone f g T) → IsEquiv (Cone.left s) → IsPullback s
embedding-degenerate-pullback {f = f} {g} eg s el =
  equiv-cancel-left (pullbackLift s) pullback₁ projection-equivalence
    (equiv-transport ((pullbackLift-β₁ s) ⁻¹) el)
  where
  v = IsEquiv.inverse el
  section = pullbackLift s ∘ v
  comparison : (pullback₁ ∘ section) =₁ (id _)
  comparison = (IsEquiv.retractionIso el) ⁻¹ ∙
    ((pullbackLift-β₁ s ▷ v) ∙ (comp-assoc v (pullbackLift s) pullback₁) ⁻¹)
  projection-equivalence = embedding-with-section pullback₁
    (chosen-base-change-embedding f g eg) section comparison

cospan-embedding-isEquiv : {C D E C′ D′ E′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) → IsEquiv (CospanMap.left F) →
  IsEquiv (CospanMap.right F) → IsEmbedding (CospanMap.base F) →
  IsEquiv (CospanMap.pullbackMap F)
cospan-embedding-isEquiv F el er eb = CospanCartesian.pullbackMap-isEquiv F el
  (embedding-degenerate-pullback eb (rightSquareOf F) er)
```
