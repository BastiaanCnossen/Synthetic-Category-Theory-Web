# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as CoordinateComparisons

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.BinaryFunctorCalculus as BinaryFunctorCalculus

module SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle using (cancel-inverse-tail)
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle using (coordinate-at)

open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (post-iterated-comparison)

open BinaryFunctorCalculus.Iteration vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (binary-pre-iterated)

applyTerm-pre-iterated : {Q R X C D : CAT}
  (f : MAP X (Map C D)) (x : MAP X C) (σ : MAP R X) (τ : MAP Q R)
  → (applyTerm-pre f x (σ ∘ τ) ∙ comp-assoc τ σ (applyTerm f x)) =₂
      (applyTerm-cong (comp-assoc τ σ f) (comp-assoc τ σ x) ∙
        (applyTerm-pre (f ∘ σ) (x ∘ σ) τ ∙ (applyTerm-pre f x σ ▷ τ)))
applyTerm-pre-iterated = binary-pre-iterated mapEval
```

A normalized application is obtained by restricting the two inputs and
then comparing them with their intended values. The following assembly
transports the normalization through another restriction, given the two
corresponding input squares.

```agda
combine-apply : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C} {source : MAP X D}
  (α : f₁ =₁ f₂) (β : x₁ =₁ x₂)
  (γ : f₀ =₁ f₁) (δ : x₀ =₁ x₁)
  (base : source =₁ (applyTerm f₀ x₀))
  → (applyTerm-cong α β ∙ (applyTerm-cong γ δ ∙ base)) =₂
      (applyTerm-cong (α ∙ γ) (β ∙ δ) ∙ base)
combine-apply α β γ δ base =
  BinaryFunctorCalculus.binary-combine vocabulary terminal products productLaws composition vertical whiskering
    mapEval α β γ δ base

module ApplicationAssembly {R Γ X C D : CAT}
  (H : MAP X (Map C D)) (K : MAP X C)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : (q ∘ r) =₁ q′)
  {f : MAP Γ (Map C D)} {x : MAP Γ C}
  {f′ : MAP R (Map C D)} {x′ : MAP R C}
  (a : (H ∘ q) =₁ f) (b : (K ∘ q) =₁ x)
  (a′ : (H ∘ q′) =₁ f′) (b′ : (K ∘ q′) =₁ x′)
  (c : (f ∘ r) =₁ f′) (d : (x ∘ r) =₁ x′) where
  open BinaryFunctorCalculus.Iteration.Assembly vocabulary terminal products productLaws composition vertical whiskering
    pentagonTriangle mapEval H K q r q′ δ a b a′ b′ c d public

```

The next two helpers carry projection witnesses through a restriction.
The second applies an additional fixed functor to the coordinate.

```agda
projection-square-forward : {R Γ X A : CAT} (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : (q ∘ r) =₁ q′) (b : (π ∘ q) =₁ p)
  (b′ : (π ∘ q′) =₁ p′) (c : (p ∘ r) =₁ p′)
  → (b′ ∙ (π ◁ δ)) =₂ (c ∙ ((b ▷ r) ∙ (comp-assoc r q π) ⁻¹))
  → (b′ ∙ ((π ◁ δ) ∙ comp-assoc r q π)) =₂ (c ∙ (b ▷ r))
projection-square-forward π q r q′ δ b b′ c square =
  let A = comp-assoc r q π
  in isoComp-cong (idIso c) (cancel-inverse-tail (b ▷ r) A) ∙
    (isoComp-assoc-at c ((b ▷ r) ∙ A ⁻¹) A ∙
      (isoComp-cong square (idIso A) ∙ (isoComp-assoc-at b′ (π ◁ δ) A) ⁻¹))

coordinate-restriction : {R Γ X A B : CAT} (F : MAP A B) (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : (q ∘ r) =₁ q′) (b : (π ∘ q) =₁ p)
  (b′ : (π ∘ q′) =₁ p′) (c : (p ∘ r) =₁ p′)
  → (b′ ∙ (π ◁ δ)) =₂ (c ∙ ((b ▷ r) ∙ (comp-assoc r q π) ⁻¹))
  →
      (coordinate-at F π q′ b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc r q (F ∘ π))) =₂
      ((F ◁ c) ∙ (comp-assoc r p F ∙ (coordinate-at F π q b ▷ r)))
coordinate-restriction F π q r q′ δ b b′ c square =
  CoordinateComparisons.coordinate-at-change vocabulary terminal products productLaws
    composition vertical whiskering pentagonTriangle F π q r q′ δ b b′ c square
```

