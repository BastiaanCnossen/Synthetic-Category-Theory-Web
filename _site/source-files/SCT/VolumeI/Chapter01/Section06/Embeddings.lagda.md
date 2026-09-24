# Embeddings

The diagonal definition is `def:Embedding`. A useful equivalent condition
is that the first projection of the self-pullback is an equivalence.
The final argument proves `lem:Embedding_With_Section_Is_Homotopy_Equivalence`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Embeddings
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P

diagonalCone : {C D : CAT} (f : MAP C D) → Cone f f C
diagonalCone {C} f = record
  { left = id C ; right = id C ; match = idIso (f ∘ id C) }

diagonal : {C D : CAT} (f : MAP C D) → MAP C (Pullback f f)
diagonal f = pullbackLift (diagonalCone f)

IsEmbedding : {C D : CAT} → MAP C D → Set m
IsEmbedding f = IsEquiv (diagonal f)

embedding-projection : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  IsEquiv (pullback₁ {f = f} {f})
embedding-projection f ef = equiv-cancel-right (diagonal f) pullback₁ ef
  (equiv-transport ((pullbackLift-β₁ (diagonalCone f)) ⁻¹) (id-isEquiv _))

projection-embedding : {C D : CAT} (f : MAP C D) →
  IsEquiv (pullback₁ {f = f} {f}) → IsEmbedding f
projection-embedding f ep = equiv-cancel-left (diagonal f) pullback₁ ep
  (equiv-transport ((pullbackLift-β₁ (diagonalCone f)) ⁻¹) (id-isEquiv _))

embedding-legs : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  (pullback₁ {f = f} {f}) =₁ pullback₂
embedding-legs f ef = FunctorLift.lift (preWhisker-lift (diagonal f) ef
  ((pullbackLift-β₂ (diagonalCone f)) ⁻¹ ∙ pullbackLift-β₁ (diagonalCone f)))

embedding-reflect : {C D T : CAT} (f : MAP C D) → IsEmbedding f →
  (h k : MAP T C) → (f ∘ h) =₁ (f ∘ k) → h =₁ k
embedding-reflect f ef h k α = pullbackLift-β₂ s ∙
  ((embedding-legs f ef ▷ pullbackLift s) ∙ (pullbackLift-β₁ s) ⁻¹)
  where
  s : Cone f f _
  s = record { left = h ; right = k ; match = α }

embedding-with-section : {C D : CAT} (f : MAP C D) → IsEmbedding f →
  (s : MAP D C) → (f ∘ s) =₁ (id D) → IsEquiv f
embedding-with-section f ef s ε = record
  { inverse = s
  ; sectionIso = embedding-reflect f ef _ _
      (comp-assoc f s f ∙
        ((ε ▷ f) ⁻¹ ∙ ((comp-unitˡ f) ⁻¹ ∙ comp-unitʳ f)))
  ; retractionIso = ε ⁻¹ }
```
