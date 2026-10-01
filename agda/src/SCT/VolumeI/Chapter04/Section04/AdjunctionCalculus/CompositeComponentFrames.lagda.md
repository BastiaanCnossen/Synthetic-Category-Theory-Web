# The associators in composite adjunction components

One four-functor reassociation supplies the endpoint equation for both
the composite unit and the composite counit. It is an instance of the
external pentagon with its final associator cancelled.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeComponentFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; pre-inverse-at)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {Γ A B C D E : CAT} (x : MAP Γ A) (f : MAP A B) (g : MAP B C)
  (h : MAP C D) (k : MAP D E) where
  output : (((k ∘ h) ∘ ((g ∘ f) ∘ x))) =₁ (k ∘ (h ∘ (g ∘ (f ∘ x))))
  output = (k ◁ (h ◁ comp-assoc x f g)) ∙ comp-assoc ((g ∘ f) ∘ x) h k
  inner = (h ◁ comp-assoc x f g) ∙ comp-assoc x (g ∘ f) h
  outer = comp-assoc x (g ∘ f) (k ∘ h)
  global = (comp-assoc (g ∘ f) h k) ⁻¹

  private
    aa = k ◁ (h ◁ comp-assoc x f g)
    bb = comp-assoc x (g ∘ f) h
    dd = comp-assoc ((g ∘ f) ∘ x) h k
    ee = outer
    ff = comp-assoc x (h ∘ (g ∘ f)) k
    tail = comp-assoc (g ∘ f) h k ▷ x

  abstract
    pentagon-cancel : ((dd ∙ ee) ∙ (global ▷ x)) =₂ ((k ◁ bb) ∙ ff)
    pentagon-cancel = cancel-right tail ((k ◁ bb) ∙ ff) ∙
      (isoComp-cong
        ((isoComp-assoc-at (k ◁ bb) ff tail) ⁻¹ ∙ pentagon-whiskered x (g ∘ f) h k)
        (idIso (tail ⁻¹)) ∙
        isoComp-cong (idIso (dd ∙ ee)) (pre-inverse-at (comp-assoc (g ∘ f) h k) x))

    comparison : (output ∙ (outer ∙ (global ▷ x))) =₂
      ((k ◁ inner) ∙ comp-assoc x (h ∘ (g ∘ f)) k)
    comparison = isoComp-cong ((postWhisker-isoComp-at k (h ◁ comp-assoc x f g) bb) ⁻¹) (idIso ff) ∙
      ((isoComp-assoc-at aa (k ◁ bb) ff) ⁻¹ ∙
      (isoComp-cong (idIso aa) pentagon-cancel ∙
      (isoComp-cong (idIso aa) ((isoComp-assoc-at dd ee (global ▷ x)) ⁻¹) ∙
        isoComp-assoc-at aa dd (ee ∙ (global ▷ x)))))
```
