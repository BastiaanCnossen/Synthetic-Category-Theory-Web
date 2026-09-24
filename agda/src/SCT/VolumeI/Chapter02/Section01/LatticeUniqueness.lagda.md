# Recognizing interval diagrams by their endpoints

A family of arrows with initial source, or with terminal target, is unique.
We use this to recognize minimum, maximum, and the second projection from
their horizontal boundary values. No Segal or Rezk axiom is involved.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.LatticeUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E

initial-diagram-compare : {X : CAT} (y : MAP X [1]) (F G : MAP (X × [1]) [1]) →
  (F ∘ insert zero) =₁ (const zero) → (F ∘ insert one) =₁ y →
  (G ∘ insert zero) =₁ (const zero) → (G ∘ insert one) =₁ y → F =₁ G
initial-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
  (funUncurry-cong (initial-compare zero zero-isInitial y (expression F f₀ f₁) (expression G g₀ g₁)) ∙
    (funCurry-β F) ⁻¹)

terminal-diagram-compare : {X : CAT} (y : MAP X [1]) (F G : MAP (X × [1]) [1]) →
  (F ∘ insert zero) =₁ y → (F ∘ insert one) =₁ (const one) →
  (G ∘ insert zero) =₁ y → (G ∘ insert one) =₁ (const one) → F =₁ G
terminal-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
  (funUncurry-cong (terminal-compare one one-isTerminal y (expression F f₀ f₁) (expression G g₀ g₁)) ∙
    (funCurry-β F) ⁻¹)

recognize-min : (H : MAP ([1] × [1]) [1]) →
  (H ∘ insert zero) =₁ (const zero) → (H ∘ insert one) =₁ (id [1]) → H =₁ min
recognize-min H h₀ h₁ = initial-diagram-compare (id [1]) H min h₀ h₁ min-right-zero min-right-one

recognize-max : (H : MAP ([1] × [1]) [1]) →
  (H ∘ insert zero) =₁ (id [1]) → (H ∘ insert one) =₁ (const one) → H =₁ max
recognize-max H h₀ h₁ = terminal-diagram-compare (id [1]) H max h₀ h₁ max-right-zero max-right-one

recognize-second-projection : (H : MAP ([1] × [1]) [1]) →
  (H ∘ insert zero) =₁ (const zero) → (H ∘ insert one) =₁ (const one) → H =₁ pr₂
recognize-second-projection H h₀ h₁ = initial-diagram-compare (const one) H pr₂ h₀ h₁
  (pair-β₂ (id [1]) (const zero)) (pair-β₂ (id [1]) (const one))
```
