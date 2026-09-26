# Constant arrows with their endpoint frames

Composing the identity-arrow functor with a term gives its constant arrow.
The two endpoint frames are natural in the term. These particular frames
will be used when recovering an invertible interval from Rezk.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)

constant-frame : {Γ C : CAT} (v : MAP (Ar C) C) →
  (v ∘ identityArrow) =₁ (id C) → (x : MAP Γ C) →
  (v ∘ (identityArrow ∘ x)) =₁ x
constant-frame v b x = comp-unitˡ x ∙ ((b ▷ x) ∙ (comp-assoc x identityArrow v) ⁻¹)

constant-frame-natural : {Γ C : CAT} (v : MAP (Ar C) C)
  (b : (v ∘ identityArrow) =₁ (id C)) {x y : MAP Γ C} (α : x =₁ y) →
  (constant-frame v b y ∙ (v ◁ (identityArrow ◁ α))) =₂ (α ∙ constant-frame v b x)
constant-frame-natural {C = C} v b {x} {y} α = paste-squares
  ((b ▷ x) ∙ (comp-assoc x identityArrow v) ⁻¹)
  ((b ▷ y) ∙ (comp-assoc y identityArrow v) ⁻¹)
  (comp-unitˡ x) (comp-unitˡ y) (v ◁ (identityArrow ◁ α)) (id C ◁ α) α
  (substitution-square-projection v identityArrow (id C) b α) (postWhisker-id-at α)

constant-identification : {Γ C : CAT} {x y : MAP Γ C} → x =₁ y → MorphismExpression x y
constant-identification {x = x} α = record
  { arrow = identityArrow ∘ x
  ; source-frame = constant-frame ev₀ identity-source x
  ; target-frame = α ∙ constant-frame ev₁ identity-target x }
```
