# Embeddings

The diagonal definition is `def:Embedding`. A useful equivalent condition
is that the first projection of the self-pullback is an equivalence.
The final argument proves `lem:Embedding_With_Section_Is_Homotopy_Equivalence`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.Embeddings
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P

diagonalCone : {C D : CAT} (f : MAP C D) → Cone f f C
diagonalCone {C} f = record
  { left = id C ; right = id C ; match = idIso (f ∘ id C) }

diagonal : {C D : CAT} (f : MAP C D) → MAP C (Pullback f f)
diagonal f = pbLift (diagonalCone f)

IsEmbedding : {C D : CAT} → MAP C D → Set m
IsEmbedding f = IsEquiv (diagonal f)

embedding-projection : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  IsEquiv (pb₁ {f = f} {f})
embedding-projection f ef = equiv-cancel-right (diagonal f) pb₁ ef
  (equiv-transport (invIso (pbLift-β₁ (diagonalCone f))) (id-isEquiv _))

projection-embedding : {C D : CAT} (f : MAP C D) →
  IsEquiv (pb₁ {f = f} {f}) → IsEmbedding f
projection-embedding f ep = equiv-cancel-left (diagonal f) pb₁ ep
  (equiv-transport (invIso (pbLift-β₁ (diagonalCone f))) (id-isEquiv _))

embedding-legs : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  NatIso (pb₁ {f = f} {f}) pb₂
embedding-legs f ef = FunctorLift.lift (preWhisker-lift (diagonal f) ef
  (invIso (pbLift-β₂ (diagonalCone f)) ∙ pbLift-β₁ (diagonalCone f)))

embedding-reflect : {C D T : CAT} (f : MAP C D) → IsEmbedding f →
  (h k : MAP T C) → NatIso (f ∘ h) (f ∘ k) → NatIso h k
embedding-reflect f ef h k α = pbLift-β₂ s ∙
  ((embedding-legs f ef ▷ pbLift s) ∙ invIso (pbLift-β₁ s))
  where
  s : Cone f f _
  s = record { left = h ; right = k ; match = α }

embedding-with-section : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  (s : MAP D C) → NatIso (f ∘ s) (id D) → IsEquiv f
embedding-with-section f ef s ε = record
  { inverse = s
  ; sectionIso = embedding-reflect f ef _ _
      (comp-assoc f s f ∙
        (invIso (ε ▷ f) ∙ (invIso (comp-unitˡ f) ∙ comp-unitʳ f)))
  ; retractionIso = invIso ε }
```
