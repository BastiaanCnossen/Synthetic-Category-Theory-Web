# Vertical composition and whiskering comparisons

This module collects the previously proved associativity, unit, inverse,
and whiskering comparisons used in later pasting arguments. Their proofs
are the corresponding lemmas re-exported by `Setup`.

The aliases are `abstract` so that Agda can use their statements without
repeatedly expanding the proofs. The functors, natural isomorphisms, and
chosen comparison maps keep their definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

module Original = Setup 𝒯
open Original public hiding
  (isoComp-cong; isoComp-assoc-at; isoComp-unitˡ-at; isoComp-unitʳ-at;
   isoComp-inverseˡ-at; isoComp-inverseʳ-at;
   preWhisker-isoComp-at; postWhisker-isoComp-at)

abstract
  isoComp-cong : {X C D : CAT} {f g h : MAP C D}
    {β β′ : MAP X (g ＝ h)} {α α′ : MAP X (f ＝ g)}
    → β =₁ β′ → α =₁ α′ → (β ∙ α) =₁ (β′ ∙ α′)
  isoComp-cong = Original.isoComp-cong

  isoComp-assoc-at : {C D : CAT} {f g h k : MAP C D}
    (γ : h =₁ k) (β : g =₁ h) (α : f =₁ g)
    → ((γ ∙ β) ∙ α) =₂ (γ ∙ (β ∙ α))
  isoComp-assoc-at = Original.isoComp-assoc-at

  isoComp-unitˡ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (idIso g ∙ α) =₂ α
  isoComp-unitˡ-at = Original.isoComp-unitˡ-at

  isoComp-unitʳ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ∙ idIso f) =₂ α
  isoComp-unitʳ-at = Original.isoComp-unitʳ-at

  isoComp-inverseˡ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ⁻¹ ∙ α) =₂ (idIso f)
  isoComp-inverseˡ-at = Original.isoComp-inverseˡ-at

  isoComp-inverseʳ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ∙ α ⁻¹) =₂ (idIso g)
  isoComp-inverseʳ-at = Original.isoComp-inverseʳ-at

  preWhisker-isoComp-at : {B C D : CAT} {f g h : MAP C D}
    (β : g =₁ h) (α : f =₁ g) (k : MAP B C)
    → ((β ∙ α) ▷ k) =₂ ((β ▷ k) ∙ (α ▷ k))
  preWhisker-isoComp-at = Original.preWhisker-isoComp-at

  postWhisker-isoComp-at : {C D E : CAT} {f g h : MAP C D}
    (u : MAP D E) (β : g =₁ h) (α : f =₁ g)
    → (u ◁ (β ∙ α)) =₂ ((u ◁ β) ∙ (u ◁ α))
  postWhisker-isoComp-at = Original.postWhisker-isoComp-at
```
