# Coherence along a specified retraction

Given `i : B → X` and `r : X → B` with `e : r ∘ i = id`, any `h : B → C`
satisfies `reduce h : (h ∘ r) ∘ i = h`. Postcomposing with `g` is
compatible with this reduction, up to the specified associators; the proof
is a whiskered pentagon together with Kelly's right-unitor lemma. For a
section `s` of `p : C → D`, the section frame `(s ∘ p) ∘ s = s` is this
reduction, and its postcomposition with `p` is computed from the
self-naturality of `ρ : p ∘ s = id`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.RetractionCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
```

## Reduction along a retraction

```agda
module _ {Γ : Context} where
  module Reduction {B X : CAT Γ} (i : MAP B X) (r : MAP X B) (e : (r ∘ i) =₁ id B) where
    reduce : {C : CAT Γ} (h : MAP B C) → ((h ∘ r) ∘ i) =₁ h
    reduce h = comp-unitʳ h ∙ ((h ◁ e) ∙ comp-assoc i r h)

    module Post {C D : CAT Γ} (h : MAP B C) (g : MAP C D) where
      A₀ : ((g ∘ h) ∘ id B) =₁ (g ∘ (h ∘ id B))
      A₀ = comp-assoc (id B) h g
      A₁ : (((g ∘ h) ∘ r) ∘ i) =₁ ((g ∘ (h ∘ r)) ∘ i)
      A₁ = comp-assoc r h g ▷ i
      A₂ : ((g ∘ (h ∘ r)) ∘ i) =₁ (g ∘ ((h ∘ r) ∘ i))
      A₂ = comp-assoc i (h ∘ r) g
      A₃ : ((h ∘ r) ∘ i) =₁ (h ∘ (r ∘ i))
      A₃ = comp-assoc i r h
      A₄ : ((g ∘ h) ∘ (r ∘ i)) =₁ (g ∘ (h ∘ (r ∘ i)))
      A₄ = comp-assoc (r ∘ i) h g
      A₅ : (((g ∘ h) ∘ r) ∘ i) =₁ ((g ∘ h) ∘ (r ∘ i))
      A₅ = comp-assoc i r (g ∘ h)
      ρ : (h ∘ id B) =₁ h
      ρ = comp-unitʳ h

      private
        abstract
          merge : ((g ◁ ρ) ∙ ((g ◁ (h ◁ e)) ∙ (g ◁ A₃))) =₂ (g ◁ reduce h)
          merge = (postWhisker-comp₌ g ρ ((h ◁ e) ∙ A₃)) ⁻¹ ∙
            comp₌-cong (id₌ (g ◁ ρ)) ((postWhisker-comp₌ g (h ◁ e) A₃) ⁻¹)

      abstract
        reduce-comp : reduce (g ∘ h) =₂ ((g ◁ reduce h) ∙ (A₂ ∙ A₁))
        reduce-comp = comp₌-cong merge (id₌ (A₂ ∙ A₁)) ∙
          ((comp₌-assoc (g ◁ ρ) ((g ◁ (h ◁ e)) ∙ (g ◁ A₃)) (A₂ ∙ A₁)) ⁻¹ ∙
            (comp₌-cong (id₌ (g ◁ ρ)) ((comp₌-assoc (g ◁ (h ◁ e)) (g ◁ A₃) (A₂ ∙ A₁)) ⁻¹) ∙
              (comp₌-cong (id₌ (g ◁ ρ))
                (comp₌-cong (id₌ (g ◁ (h ◁ e))) (pentagon-whiskered-right i r h g)) ∙
                (comp₌-cong (id₌ (g ◁ ρ)) (comp₌-assoc (g ◁ (h ◁ e)) A₄ A₅) ∙
                  (comp₌-cong (id₌ (g ◁ ρ)) (comp₌-cong (postWhisker-comp-One e h g) (id₌ A₅)) ∙
                    (reassociateFour (g ◁ ρ) A₀ ((g ∘ h) ◁ e) A₅ ∙
                      comp₌-cong (right-unitor-comp h g) (id₌ (((g ∘ h) ◁ e) ∙ A₅))))))))

        cancel-associator : (reduce (g ∘ h) ∙ (comp-assoc r h g ⁻¹ ▷ i)) =₂
          ((g ◁ reduce h) ∙ A₂)
        cancel-associator = comp-inv-right ((g ◁ reduce h) ∙ A₂) A₁ ∙
          comp₌-cong ((comp₌-assoc (g ◁ reduce h) A₂ A₁) ⁻¹ ∙ reduce-comp)
            (preWhisker-inverse (comp-assoc r h g) i)
```

## Frames of a section

```agda
  private
    module _ {X : CAT Γ} where
      open Terms.InContext X using (Term)

      solve-right : {Y : CAT Γ} {u v w : Term Y}
        (α : v =₁ w) (β : u =₁ v) (γ : u =₁ w)
        → (α ∙ β) =₂ γ → α =₂ (γ ∙ β ⁻¹)
      solve-right α β γ same = comp₌-cong same (id₌ (β ⁻¹)) ∙ (comp-inv-right α β) ⁻¹

  module WithSection {C D : CAT Γ} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
    section-frame : ((s ∘ p) ∘ s) =₁ s
    section-frame = Reduction.reduce s p ρ s

    base-frame : ((p ∘ s) ∘ p) =₁ p
    base-frame = comp-unitˡ p ∙ (ρ ▷ p)

    vertical-frame : (p ∘ (s ∘ p)) =₁ p
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
      identity-frame = comp₌-cong ((triangle-whiskered s p) ⁻¹)
        (id₌ ((comp-assoc s (id C) p) ⁻¹)) ∙
        (comp-inv-right (p ◁ comp-unitˡ s) (comp-assoc s (id C) p)) ⁻¹

    private
      abstract
        common-tail : ((p ◁ section-frame) ∙ (bb ∙ cc)) =₂ (base-frame ▷ s)
        common-tail = (preWhisker-comp₌ (comp-unitˡ p) (ρ ▷ p) s) ⁻¹ ∙
          (comp₌-cong (left-unitor-comp s p) (id₌ ((ρ ▷ p) ▷ s)) ∙
          ((comp₌-assoc (comp-unitˡ t) mm ((ρ ▷ p) ▷ s)) ⁻¹ ∙
          (comp₌-cong (id₌ (comp-unitˡ t)) ((preWhisker-comp-One ρ p s) ⁻¹) ∙
          (comp₌-assoc (comp-unitˡ t) (ρ ▷ t) ee ∙
          (comp₌-cong (self-naturality-One ρ) (id₌ ee) ∙
          ((comp₌-assoc (comp-unitʳ t) (t ◁ ρ) ee) ⁻¹ ∙
          (comp₌-cong ((right-unitor-comp s p) ⁻¹) (id₌ ((t ◁ ρ) ∙ ee)) ∙
          ((comp₌-assoc xx jj ((t ◁ ρ) ∙ ee)) ⁻¹ ∙
          (comp₌-cong (id₌ xx) (comp₌-assoc jj (t ◁ ρ) ee) ∙
          (comp₌-cong (id₌ xx) (comp₌-cong ((postWhisker-comp-One ρ s p) ⁻¹) (id₌ ee)) ∙
          (comp₌-cong (id₌ xx) ((comp₌-assoc yy dd ee) ⁻¹) ∙
          (comp₌-cong (id₌ xx) (comp₌-cong (id₌ yy) ((pentagon-whiskered-right s p s p) ⁻¹)) ∙
          (comp₌-cong (id₌ xx) (comp₌-assoc yy zz (bb ∙ cc)) ∙
          (comp₌-assoc xx (yy ∙ zz) (bb ∙ cc) ∙
            comp₌-cong
              (comp₌-cong (id₌ xx) (postWhisker-comp₌ p (s ◁ ρ) aa) ∙
                postWhisker-comp₌ p (comp-unitʳ s) ((s ◁ ρ) ∙ aa))
              (id₌ (bb ∙ cc))))))))))))))))

    abstract
      section-frame-post : (p ◁ section-frame) =₂ ((vertical-frame ▷ s) ∙ bb ⁻¹)
      section-frame-post =
        comp₌-cong
          ((comp₌-cong (id₌ (base-frame ▷ s)) (preWhisker-inverse (comp-assoc p s p) s) ∙
            preWhisker-comp₌ base-frame ((comp-assoc p s p) ⁻¹) s) ⁻¹)
          (id₌ (bb ⁻¹)) ∙
        solve-right (p ◁ section-frame) bb ((base-frame ▷ s) ∙ cc ⁻¹)
          (solve-right ((p ◁ section-frame) ∙ bb) cc (base-frame ▷ s)
            (common-tail ∙ comp₌-assoc (p ◁ section-frame) bb cc))
```
