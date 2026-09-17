# Opaque proofs for mapping-anima calculations

These aliases expose the checked statements used by later pasting proofs.
Their implementations are checked here and remain visible in the imported
source files; making the aliases abstract avoids repeatedly expanding those
implementations. No chosen comparison or axiom interface changes.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as ProofCalculus
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ApplicationRestriction as Application
import SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange as Evaluation
import SCT.VolumeI.Chapter01.Section03.Currying as Currying

module SCT.VolumeI.Chapter01.Section03.MappingProofCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open ProofCalculus 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Currying 𝒯 M using (mapUncurryIso; mapUncurry-cong; mapUncurry-pre)

abstract
  apply-cong-Iso₂ : {X C D : CAT}
    {f f′ : MAP X (Map C D)} {x x′ : MAP X C}
    {α α′ : NatIso f f′} {β β′ : NatIso x x′}
    → Iso₂ α α′ → Iso₂ β β′
    → Iso₂ (applyTerm-cong α β) (applyTerm-cong α′ β′)
  apply-cong-Iso₂ = Naturality.apply-cong-Iso₂ 𝒯 M

  apply-cong-comp : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C}
    (α₂ : NatIso f₁ f₂) (α₁ : NatIso f₀ f₁)
    (β₂ : NatIso x₁ x₂) (β₁ : NatIso x₀ x₁)
    → Iso₂ (applyTerm-cong (α₂ ∙ α₁) (β₂ ∙ β₁))
        (applyTerm-cong α₂ β₂ ∙ applyTerm-cong α₁ β₁)
  apply-cong-comp = Naturality.apply-cong-comp 𝒯 M

  mapUncurry-at-inner : {Γ X C D : CAT} (f : MAP X (Map C D))
    {p p′ : MAP Γ X} {x x′ : MAP Γ C} (σ : NatIso p p′) (τ : NatIso x x′)
    → Iso₂ (mapUncurry-at f p′ x′ ∙ (mapUncurry f ◁ pair-cong σ τ))
        (applyTerm-cong (f ◁ σ) τ ∙ mapUncurry-at f p x)
  mapUncurry-at-inner = Naturality.mapUncurry-at-inner 𝒯 M

  mapUncurry-as-apply-natural : {X C D : CAT} {f g : MAP X (Map C D)}
    (α : NatIso f g)
    → Iso₂ (mapUncurry-as-apply g ∙ mapUncurry-cong α)
        (applyTerm-cong (α ▷ pr₁) (idIso pr₂) ∙ mapUncurry-as-apply f)
  mapUncurry-as-apply-natural = Naturality.mapUncurry-as-apply-natural 𝒯 M

  binary-pre-inputs : {X Y A B C : CAT} (F : MAP (A × B) C)
    {f f′ : MAP X A} {g g′ : MAP X B}
    (α : NatIso f f′) (β : NatIso g g′) (r : MAP Y X)
    → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
          after = (F ◁ pair-pre f′ g′ r) ∙ comp-assoc r (pair f′ g′) F
      in Iso₂ (after ∙ ((F ◁ pair-cong α β) ▷ r))
          ((F ◁ pair-cong (α ▷ r) (β ▷ r)) ∙ before)
  binary-pre-inputs = Naturality.binary-pre-inputs 𝒯 M

  combine-apply : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C} {source : MAP X D}
    (α : NatIso f₁ f₂) (β : NatIso x₁ x₂)
    (γ : NatIso f₀ f₁) (δ : NatIso x₀ x₁)
    (base : NatIso source (applyTerm f₀ x₀))
    → Iso₂ (applyTerm-cong α β ∙ (applyTerm-cong γ δ ∙ base))
        (applyTerm-cong (α ∙ γ) (β ∙ δ) ∙ base)
  combine-apply = Application.combine-apply 𝒯 M

  post-iterated-comparison : {Q R X A B : CAT}
    (F : MAP A B) (H : MAP X A) (r : MAP R X) (s : MAP Q R)
    {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
    (u : NatIso (H ∘ r) H₁) (v : NatIso (H₁ ∘ s) H₂)
    (w : NatIso (H ∘ (r ∘ s)) H₃) (z : NatIso H₂ H₃)
    → Iso₂ (w ∙ comp-assoc s r H) (z ∙ (v ∙ (u ▷ s)))
    → Iso₂
        (((F ◁ w) ∙ comp-assoc (r ∘ s) H F) ∙ comp-assoc s r (F ∘ H))
        ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc s H₁ F) ∙
          (((F ◁ u) ∙ comp-assoc r H F) ▷ s)))
  post-iterated-comparison = Application.post-iterated-comparison 𝒯 M

  mapUncurry-at-restriction : {R Γ X C D : CAT}
    (f : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
    → Iso₂
        (applyTerm-cong (comp-assoc r p f) (idIso (x ∘ r)) ∙
          (applyTerm-pre (f ∘ p) x r ∙ (mapUncurry-at f p x ▷ r)))
        (mapUncurry-at f (p ∘ r) (x ∘ r) ∙
          ((mapUncurry f ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (mapUncurry f)))
  mapUncurry-at-restriction = Evaluation.mapUncurry-at-restriction 𝒯 M

  mapUncurry-as-apply-parameter-change : {P Q C D : CAT}
    (f : MAP P (Map C D)) (σ : MAP Q P)
    → let s = productMap σ (id C)
          a = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f
          b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      in Iso₂
        (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ))
        (applyTerm-cong a b ∙
          (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-pre f σ)))
  mapUncurry-as-apply-parameter-change = Evaluation.mapUncurry-as-apply-parameter-change 𝒯 M

  mapUncurryIso-at : {X C D : CAT} {f g : MAP X (Map C D)} (α : NatIso f g)
    → Iso₂ (mapUncurryIso α) (mapUncurry-cong α)
  mapUncurryIso-at = Currying.mapUncurryIso-at 𝒯 M

```
