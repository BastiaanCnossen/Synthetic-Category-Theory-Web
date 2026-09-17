# Checked coherence proofs with opaque implementations

Large pasting proofs need the statements of the elementary coherence
lemmas, but do not need to unfold their proofs. The abstract aliases below
keep those implementations opaque during later checking. They are proved
by the corresponding lemmas from Sections 1.1 and 1.2. All functors,
natural isomorphisms, and chosen comparison maps retain their definitions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section03.ProofCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

module Original = Setup 𝒯
open Original public hiding
  (isoComp-cong; isoComp-assoc-at; isoComp-unitˡ-at; isoComp-unitʳ-at;
   isoComp-inverseˡ-at; isoComp-inverseʳ-at;
   preWhisker-isoComp-at; postWhisker-isoComp-at)

abstract
  isoComp-cong : {X C D : CAT} {f g h : MAP C D}
    {β β′ : MAP X (g ≅ h)} {α α′ : MAP X (f ≅ g)}
    → NatIso β β′ → NatIso α α′ → NatIso (β ∙ α) (β′ ∙ α′)
  isoComp-cong = Original.isoComp-cong

  isoComp-assoc-at : {C D : CAT} {f g h k : MAP C D}
    (γ : NatIso h k) (β : NatIso g h) (α : NatIso f g)
    → Iso₂ ((γ ∙ β) ∙ α) (γ ∙ (β ∙ α))
  isoComp-assoc-at = Original.isoComp-assoc-at

  isoComp-unitˡ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (idIso g ∙ α) α
  isoComp-unitˡ-at = Original.isoComp-unitˡ-at

  isoComp-unitʳ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (α ∙ idIso f) α
  isoComp-unitʳ-at = Original.isoComp-unitʳ-at

  isoComp-inverseˡ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (invIso α ∙ α) (idIso f)
  isoComp-inverseˡ-at = Original.isoComp-inverseˡ-at

  isoComp-inverseʳ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (α ∙ invIso α) (idIso g)
  isoComp-inverseʳ-at = Original.isoComp-inverseʳ-at

  preWhisker-isoComp-at : {B C D : CAT} {f g h : MAP C D}
    (β : NatIso g h) (α : NatIso f g) (k : MAP B C)
    → Iso₂ ((β ∙ α) ▷ k) ((β ▷ k) ∙ (α ▷ k))
  preWhisker-isoComp-at = Original.preWhisker-isoComp-at

  postWhisker-isoComp-at : {C D E : CAT} {f g h : MAP C D}
    (u : MAP D E) (β : NatIso g h) (α : NatIso f g)
    → Iso₂ (u ◁ (β ∙ α)) ((u ◁ β) ∙ (u ◁ α))
  postWhisker-isoComp-at = Original.postWhisker-isoComp-at
```
