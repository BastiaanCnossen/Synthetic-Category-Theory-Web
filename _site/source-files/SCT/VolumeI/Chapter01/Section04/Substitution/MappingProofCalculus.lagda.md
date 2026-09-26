# Application and uncurrying comparisons

The lemmas below describe how application and uncurrying interact with
composition, identifications, and restriction of parameters. They collect
the statements needed in later mapping-anima calculations; the imported
modules contain their proofs.

The aliases are `abstract` to avoid repeatedly expanding those proofs
during checking. This changes neither the chosen comparisons nor the
axiom interface.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as ProofCalculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as Naturality
import SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction as Application
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as Evaluation
import SCT.VolumeI.Chapter01.Section04.Currying as Currying

module SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open ProofCalculus 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Currying 𝒯 M using (mapUncurryIso; mapUncurry-cong; mapUncurry-restrict)

abstract
  apply-cong-Iso₂ : {X C D : CAT}
    {f f′ : MAP X (Map C D)} {x x′ : MAP X C}
    {α α′ : f =₁ f′} {β β′ : x =₁ x′}
    → α =₂ α′ → β =₂ β′
    → (applyTerm-cong α β) =₂ (applyTerm-cong α′ β′)
  apply-cong-Iso₂ = Naturality.apply-cong-Iso₂ 𝒯 M

  apply-cong-comp : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C}
    (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
    (β₂ : x₁ =₁ x₂) (β₁ : x₀ =₁ x₁)
    → (applyTerm-cong (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
        (applyTerm-cong α₂ β₂ ∙ applyTerm-cong α₁ β₁)
  apply-cong-comp = Naturality.apply-cong-comp 𝒯 M

  mapUncurry-at-inner : {Γ X C D : CAT} (f : MAP X (Map C D))
    {p p′ : MAP Γ X} {x x′ : MAP Γ C} (σ : p =₁ p′) (τ : x =₁ x′)
    → (mapUncurry-at f p′ x′ ∙ (mapUncurry f ◁ pair-cong σ τ)) =₂
        (applyTerm-cong (f ◁ σ) τ ∙ mapUncurry-at f p x)
  mapUncurry-at-inner = Naturality.mapUncurry-at-inner 𝒯 M

  mapUncurry-as-apply-natural : {X C D : CAT} {f g : MAP X (Map C D)}
    (α : f =₁ g)
    → (mapUncurry-as-apply g ∙ mapUncurry-cong α) =₂
        (applyTerm-cong (α ▷ pr₁) (idIso pr₂) ∙ mapUncurry-as-apply f)
  mapUncurry-as-apply-natural = Naturality.mapUncurry-as-apply-natural 𝒯 M

  binary-pre-inputs : {X Y A B C : CAT} (F : MAP (A × B) C)
    {f f′ : MAP X A} {g g′ : MAP X B}
    (α : f =₁ f′) (β : g =₁ g′) (r : MAP Y X)
    → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
          after = (F ◁ pair-pre f′ g′ r) ∙ comp-assoc r (pair f′ g′) F
      in (after ∙ ((F ◁ pair-cong α β) ▷ r)) =₂
          ((F ◁ pair-cong (α ▷ r) (β ▷ r)) ∙ before)
  binary-pre-inputs = Naturality.binary-pre-inputs 𝒯 M

  combine-apply : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C} {source : MAP X D}
    (α : f₁ =₁ f₂) (β : x₁ =₁ x₂)
    (γ : f₀ =₁ f₁) (δ : x₀ =₁ x₁)
    (base : source =₁ (applyTerm f₀ x₀))
    → (applyTerm-cong α β ∙ (applyTerm-cong γ δ ∙ base)) =₂
        (applyTerm-cong (α ∙ γ) (β ∙ δ) ∙ base)
  combine-apply = Application.combine-apply 𝒯 M

  post-iterated-comparison : {Q R X A B : CAT}
    (F : MAP A B) (H : MAP X A) (r : MAP R X) (s : MAP Q R)
    {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
    (u : (H ∘ r) =₁ H₁) (v : (H₁ ∘ s) =₁ H₂)
    (w : (H ∘ (r ∘ s)) =₁ H₃) (z : H₂ =₁ H₃)
    → (w ∙ comp-assoc s r H) =₂ (z ∙ (v ∙ (u ▷ s)))
    →
        (((F ◁ w) ∙ comp-assoc (r ∘ s) H F) ∙ comp-assoc s r (F ∘ H)) =₂
        ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc s H₁ F) ∙
          (((F ◁ u) ∙ comp-assoc r H F) ▷ s)))
  post-iterated-comparison = Application.post-iterated-comparison 𝒯 M

  mapUncurry-at-restriction : {R Γ X C D : CAT}
    (f : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
    →
        (applyTerm-cong (comp-assoc r p f) (idIso (x ∘ r)) ∙
          (applyTerm-pre (f ∘ p) x r ∙ (mapUncurry-at f p x ▷ r))) =₂
        (mapUncurry-at f (p ∘ r) (x ∘ r) ∙
          ((mapUncurry f ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (mapUncurry f)))
  mapUncurry-at-restriction = Evaluation.mapUncurry-at-restriction 𝒯 M

  mapUncurry-as-apply-parameter-change : {P Q C D : CAT}
    (f : MAP P (Map C D)) (σ : MAP Q P)
    → let s = productMap σ (id C)
          a = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f
          b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      in
        (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ)) =₂
        (applyTerm-cong a b ∙
          (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-restrict f σ)))
  mapUncurry-as-apply-parameter-change = Evaluation.mapUncurry-as-apply-parameter-change 𝒯 M

  mapUncurry-actions-agree : {X C D : CAT} {f g : MAP X (Map C D)} (α : f =₁ g)
    → (mapUncurryIso α) =₂ (mapUncurry-cong α)
  mapUncurry-actions-agree = Currying.mapUncurry-actions-agree 𝒯 M

```
