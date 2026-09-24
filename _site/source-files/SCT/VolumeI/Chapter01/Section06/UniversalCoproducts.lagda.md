# Universality of coproducts

The two clauses of `axiom:Universality_Of_Coproducts` remain separate
fields. The first uses the actual coproduct functor and its restriction
comparisons. The second uses the actual copairing of the two base-change
projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level) renaming (_⊔_ to _⊔ℓ_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.UniversalCoproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P

coproductSquare₁ : {C D Γ₀ Γ₁ : CAT} (f : MAP C Γ₀) (g : MAP D Γ₁) →
  Cone (in₁ {Γ₀} {Γ₁}) (coproductMap f g) C
coproductSquare₁ f g = record
  { left = f ; right = in₁ ; match = (copair-β₁ (in₁ ∘ f) (in₂ ∘ g)) ⁻¹ }

coproductSquare₂ : {C D Γ₀ Γ₁ : CAT} (f : MAP C Γ₀) (g : MAP D Γ₁) →
  Cone (in₂ {Γ₀} {Γ₁}) (coproductMap f g) D
coproductSquare₂ f g = record
  { left = g ; right = in₂ ; match = (copair-β₂ (in₁ ∘ f) (in₂ ∘ g)) ⁻¹ }

reassemble : {E Γ₀ Γ₁ : CAT} (h : MAP E (Γ₀ ⊔ Γ₁)) →
  MAP (Pullback h in₁ ⊔ Pullback h in₂) E
reassemble h = copair pullback₁ pullback₁

record CoproductUniversality : Set (c ⊔ℓ m) where
  field
    inclusion₁-isPullback : {C D Γ₀ Γ₁ : CAT} (f : MAP C Γ₀) (g : MAP D Γ₁) →
      IsPullback (coproductSquare₁ f g)
    inclusion₂-isPullback : {C D Γ₀ Γ₁ : CAT} (f : MAP C Γ₀) (g : MAP D Γ₁) →
      IsPullback (coproductSquare₂ f g)
    reassemble-isEquiv : {E Γ₀ Γ₁ : CAT} (h : MAP E (Γ₀ ⊔ Γ₁)) → IsEquiv (reassemble h)
```
