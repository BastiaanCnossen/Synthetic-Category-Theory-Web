# Coherence of the frames of a section

The identification exhibiting a section gives compatible frames after
restriction and postcomposition. The compatibility follows from the
pentagon, triangle, and naturality of the unitors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses
  vocabulary terminal products productLaws composition vertical
  using (cancel-left-reflect; cancel-right)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses
open Inverses.Whiskering vocabulary terminal products productLaws composition vertical whiskering
  using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect; triangle-whiskered; right-unitor-comp;
    postWhisker-id-reflect; left-unitor-comp; pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at; postWhisker-comp-at; preWhisker-comp-at)

open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle public
  using (identity-unitors; self-naturality)

private
  solve-right : {X Y : CAT} {u v w : MAP X Y}
    (α : v =₁ w) (β : u =₁ v) (γ : u =₁ w) →
    (α ∙ β) =₂ γ → α =₂ (γ ∙ β ⁻¹)
  solve-right α β γ same = isoComp-cong same (idIso (β ⁻¹)) ∙ (cancel-right β α) ⁻¹

module WithSection {C D : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  section-frame = comp-unitʳ s ∙ ((s ◁ ρ) ∙ comp-assoc s p s)
  base-frame = comp-unitˡ p ∙ (ρ ▷ p)
  vertical-frame = base-frame ∙ (comp-assoc p s p) ⁻¹

  private
    t = p ∘ s
    aa = comp-assoc s p s
    bb = comp-assoc s (s ∘ p) p
    cc = comp-assoc p s p ▷ s
    dd = comp-assoc t s p
    ee = comp-assoc s p t
    jj = comp-assoc (id D) s p
    mm = comp-assoc s p (id D)
    xx = p ◁ comp-unitʳ s
    yy = p ◁ (s ◁ ρ)
    zz = p ◁ aa

  abstract
    identity-frame : (p ◁ comp-unitˡ s) =₂
      ((comp-unitʳ p ▷ s) ∙ (comp-assoc s (id C) p) ⁻¹)
    identity-frame = isoComp-cong ((triangle-whiskered s p) ⁻¹)
      (idIso ((comp-assoc s (id C) p) ⁻¹)) ∙
      (cancel-right (comp-assoc s (id C) p) (p ◁ comp-unitˡ s)) ⁻¹

    common-tail : ((p ◁ section-frame) ∙ (bb ∙ cc)) =₂ (base-frame ▷ s)
    common-tail = (preWhisker-isoComp-at (comp-unitˡ p) (ρ ▷ p) s) ⁻¹ ∙
      (isoComp-cong (left-unitor-comp s p) (idIso ((ρ ▷ p) ▷ s)) ∙
      ((isoComp-assoc-at (comp-unitˡ t) mm ((ρ ▷ p) ▷ s)) ⁻¹ ∙
      (isoComp-cong (idIso (comp-unitˡ t)) ((preWhisker-comp-at ρ p s) ⁻¹) ∙
      (isoComp-assoc-at (comp-unitˡ t) (ρ ▷ t) ee ∙
      (isoComp-cong (self-naturality ρ) (idIso ee) ∙
      ((isoComp-assoc-at (comp-unitʳ t) (t ◁ ρ) ee) ⁻¹ ∙
      (isoComp-cong ((right-unitor-comp s p) ⁻¹) (idIso ((t ◁ ρ) ∙ ee)) ∙
      ((isoComp-assoc-at xx jj ((t ◁ ρ) ∙ ee)) ⁻¹ ∙
      (isoComp-cong (idIso xx) (isoComp-assoc-at jj (t ◁ ρ) ee) ∙
      (isoComp-cong (idIso xx) (isoComp-cong ((postWhisker-comp-at ρ s p) ⁻¹) (idIso ee)) ∙
      (isoComp-cong (idIso xx) ((isoComp-assoc-at yy dd ee) ⁻¹) ∙
      (isoComp-cong (idIso xx) (isoComp-cong (idIso yy) ((pentagon-whiskered s p s p) ⁻¹)) ∙
      (isoComp-cong (idIso xx) (isoComp-assoc-at yy zz (bb ∙ cc)) ∙
      (isoComp-assoc-at xx (yy ∙ zz) (bb ∙ cc) ∙
        isoComp-cong
          (isoComp-cong (idIso xx) (postWhisker-isoComp-at p (s ◁ ρ) aa) ∙
            postWhisker-isoComp-at p (comp-unitʳ s) ((s ◁ ρ) ∙ aa))
          (idIso (bb ∙ cc))))))))))))))))

    section-frame-image : (p ◁ section-frame) =₂
      ((vertical-frame ▷ s) ∙ bb ⁻¹)
    section-frame-image =
      isoComp-cong
        ((isoComp-cong (idIso (base-frame ▷ s)) (pre-inverse (comp-assoc p s p) s) ∙
          preWhisker-isoComp-at base-frame ((comp-assoc p s p) ⁻¹) s) ⁻¹)
        (idIso (bb ⁻¹)) ∙
      solve-right (p ◁ section-frame) bb ((base-frame ▷ s) ∙ cc ⁻¹)
        (solve-right ((p ◁ section-frame) ∙ bb) cc (base-frame ▷ s)
          (common-tail ∙ isoComp-assoc-at (p ◁ section-frame) bb cc))
```
