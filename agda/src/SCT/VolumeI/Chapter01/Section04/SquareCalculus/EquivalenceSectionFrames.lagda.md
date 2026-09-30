# Normalizing the inverse of an equivalence

For an equivalence and a specified section identification, choose the
other inverse identification with a prescribed image. Its second triangle
follows by reflection along the equivalence and section-frame coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.EquivalenceSectionFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames 𝒯 public
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect; triangle-whiskered)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module At {C D : CAT} (p : MAP C D) (ep : IsEquiv p)
  (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  module F = WithSection p s ρ
  chosen = postWhisker-lift p ep (F.vertical-frame ⁻¹ ∙ comp-unitʳ p)
  χ : id C =₁ (s ∘ p)
  χ = FunctorLift.lift chosen

  private
    aa = F.section-frame
    vv = F.vertical-frame
    kk = comp-assoc s (s ∘ p) p
    jj = comp-assoc s (id C) p

  abstract
    image : (p ◁ χ) =₂ (vv ⁻¹ ∙ comp-unitʳ p)
    image = FunctorLift.comparison chosen

    base-triangle : (vv ∙ (p ◁ χ)) =₂ comp-unitʳ p
    base-triangle = cancel-inverse vv (comp-unitʳ p) ∙ isoComp-cong (idIso vv) image

    section-frame-tail : ((p ◁ aa) ∙ kk) =₂ (vv ▷ s)
    section-frame-tail = isoComp-unitʳ-at (vv ▷ s) ∙
      (isoComp-cong (idIso (vv ▷ s)) (isoComp-inverseˡ-at kk) ∙
      (isoComp-assoc-at (vv ▷ s) (kk ⁻¹) kk ∙
        isoComp-cong F.section-frame-image (idIso kk)))

    section-image-tail : ((p ◁ (aa ∙ (χ ▷ s))) ∙ jj) =₂ (comp-unitʳ p ▷ s)
    section-image-tail = (preWhisker s ◁ base-triangle) ∙
      ((preWhisker-isoComp-at vv (p ◁ χ) s) ⁻¹ ∙
      (isoComp-cong section-frame-tail (idIso ((p ◁ χ) ▷ s)) ∙
      ((isoComp-assoc-at (p ◁ aa) kk ((p ◁ χ) ▷ s)) ⁻¹ ∙
      (isoComp-cong (idIso (p ◁ aa)) ((whisker-mixed-at χ s p) ⁻¹) ∙
      (isoComp-assoc-at (p ◁ aa) (p ◁ (χ ▷ s)) jj ∙
        isoComp-cong (postWhisker-isoComp-at p aa (χ ▷ s)) (idIso jj))))))

    section-triangle : (aa ∙ (χ ▷ s)) =₂ comp-unitˡ s
    section-triangle = FunctorLift.lift
      (postWhisker-Iso₂-lift p ep (aa ∙ (χ ▷ s)) (comp-unitˡ s)
        (cancel-right-reflect jj (triangle-whiskered s p ∙ section-image-tail)))
```
