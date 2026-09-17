# Recognizing interval diagrams by their endpoints

A family of arrows with initial source, or with terminal target, is unique.
We use this to recognize minimum, maximum, and the second projection from
their horizontal boundary values. No Segal or Rezk axiom is involved.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.LatticeUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.Lattice 𝒯 M ℱ P I E

initial-diagram-compare : {X : CAT} (y : MAP X [1]) (F G : MAP (X × [1]) [1]) →
  =₁ (F ∘ insert zero) (const zero) → =₁ (F ∘ insert one) y →
  =₁ (G ∘ insert zero) (const zero) → =₁ (G ∘ insert one) y → =₁ F G
initial-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
  (funUncurry-cong (initial-compare zero zero-isInitial y (expression F f₀ f₁) (expression G g₀ g₁)) ∙
    invIso (funCurry-β F))

terminal-diagram-compare : {X : CAT} (y : MAP X [1]) (F G : MAP (X × [1]) [1]) →
  =₁ (F ∘ insert zero) y → =₁ (F ∘ insert one) (const one) →
  =₁ (G ∘ insert zero) y → =₁ (G ∘ insert one) (const one) → =₁ F G
terminal-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
  (funUncurry-cong (terminal-compare one one-isTerminal y (expression F f₀ f₁) (expression G g₀ g₁)) ∙
    invIso (funCurry-β F))

recognize-min : (H : MAP ([1] × [1]) [1]) →
  =₁ (H ∘ insert zero) (const zero) → =₁ (H ∘ insert one) (id [1]) → =₁ H min
recognize-min H h₀ h₁ = initial-diagram-compare (id [1]) H min h₀ h₁ min-right-zero min-right-one

recognize-max : (H : MAP ([1] × [1]) [1]) →
  =₁ (H ∘ insert zero) (id [1]) → =₁ (H ∘ insert one) (const one) → =₁ H max
recognize-max H h₀ h₁ = terminal-diagram-compare (id [1]) H max h₀ h₁ max-right-zero max-right-one

recognize-second-projection : (H : MAP ([1] × [1]) [1]) →
  =₁ (H ∘ insert zero) (const zero) → =₁ (H ∘ insert one) (const one) → =₁ H pr₂
recognize-second-projection H h₀ h₁ = initial-diagram-compare (const one) H pr₂ h₀ h₁
  (pair-β₂ (id [1]) (const zero)) (pair-β₂ (id [1]) (const one))
```
