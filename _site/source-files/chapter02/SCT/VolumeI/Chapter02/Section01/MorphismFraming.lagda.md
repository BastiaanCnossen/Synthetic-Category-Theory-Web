# Comparing arrows with their specified endpoint frames

A single triangle to the paired endpoints determines both endpoint frames.
A comparison compatible with that triangle yields a comparison with a
morphism family carrying its original, individually specified frames.
The projected frames are exactly those used by the chosen composition.
No replacement of the target frames or choice of arrow identification occurs.

This offsource candidate reuses the two private projection calculations from
WalkingTriangle verbatim. Canonical adoption should share those calculations
with that existing consumer, rather than keep a permanent second copy.
The complete relative short-edge comparison required for units is still an
input to the later unit argument and is not supplied by this adapter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFraming where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)

private
  module _ {Γ : Context} where
    project-frame : {P K E C : CAT Γ}
      (π : MAP K E) (r : MAP E C) (s : MAP K C)
      (projection : (r ∘ π) =₁ s)
      {u v : MAP P K} (δ : u =₁ v)
      {w : MAP P E} {f : MAP P C}
      (h : (π ∘ u) =₁ w) (h′ : (π ∘ v) =₁ w)
      (k : (r ∘ w) =₁ f)
      (a : (s ∘ u) =₁ f) (b : (s ∘ v) =₁ f)
      → (k ∙ (r ◁ h)) =₂ (a ∙ restrict-triangle r π projection u)
      → (k ∙ (r ◁ h′)) =₂ (b ∙ restrict-triangle r π projection v)
      → CompatibleOver π h h′ δ
      → CompatibleOver s a b δ
    project-frame π r s projection {u} {v} δ h h′ k a b first second given =
      cancel-right p
        (paired ∙
          ((comp₌-assoc b p′ t) ⁻¹ ∙
            (comp₌-cong (id₌ b) (natural ⁻¹) ∙
              comp₌-assoc b (s ◁ δ) p)))
      where
        p = restrict-triangle r π projection u
        p′ = restrict-triangle r π projection v
        t = r ◁ (π ◁ δ)
        natural = restrict-change-square-One r π s projection δ
        projected = comp₌-cong (id₌ k)
          ((postWhisker r ◁ given) ∙
            (postWhisker-comp₌ r h′ (π ◁ δ)) ⁻¹) ∙
          comp₌-assoc k (r ◁ h′) t
        paired = first ∙ (projected ∙ comp₌-cong (second ⁻¹) (id₌ t))

    constant-frame-compatible : {P K C : CAT Γ} (π : MAP K C)
      {u v : MAP P K} {f : MAP P C}
      (a : (π ∘ u) =₁ f) (b : (π ∘ v) =₁ f) (δ : u =₁ v)
      → CompatibleOver π a b δ
      → (const b ∙ (π ◁ δ)) =₁ const a
    constant-frame-compatible π {u} {v} {f} a b δ given =
      comp₌-unitˡ (const a) ∙
        compatible-to-over
          {X = category-over _ f} {Y = category-over _ π}
          {F = functor-over u a} {G = functor-over v b} given


module _ {Γ : Context} where
  endpoint-triangle : {P C : CAT Γ} {f g : MAP P C}
    (α : MorphismFamily f g)
    → (pair ev₀ ev₁ ∘ MorphismFamily.arrow α) =₁ pair f g
  endpoint-triangle α =
    pair⁼ (MorphismFamily.source-frame α) (MorphismFamily.target-frame α) ∙
      pair-pre ev₀ ev₁ (MorphismFamily.arrow α)

  framed-arrow : {P C : CAT Γ} {f g : MAP P C}
    (u : MAP P (Ar C)) → (pair ev₀ ev₁ ∘ u) =₁ pair f g
    → MorphismFamily f g
  framed-arrow {f = f} {g} u frame = record
    { arrow = u
    ; source-frame = pair-β₁ f g ∙
        ((pr₁ ◁ frame) ∙ (project-pair₁ ev₀ ev₁ u) ⁻¹)
    ; target-frame = pair-β₂ f g ∙
        ((pr₂ ◁ frame) ∙ (project-pair₂ ev₀ ev₁ u) ⁻¹) }

  private
    projection-frame-image : {X C : CAT Γ} {a b c d : MAP X C}
      (k : c =₁ d) (h : b =₁ c) (p : b =₁ a)
      → (k ∙ h) =₂ ((k ∙ (h ∙ p ⁻¹)) ∙ p)
    projection-frame-image k h p =
      (inv-comp-right (k ∙ h) p ∙
        comp₌-cong ((comp₌-assoc k h (p ⁻¹)) ⁻¹) (id₌ p)) ⁻¹

  compare-framed-arrow : {P C : CAT Γ} {f g : MAP P C}
    (u : MAP P (Ar C)) (frame : (pair ev₀ ev₁ ∘ u) =₁ pair f g)
    (β : MorphismFamily f g) (δ : u =₁ MorphismFamily.arrow β)
    → CompatibleOver (pair ev₀ ev₁) frame (endpoint-triangle β) δ
    → MorphismFamilyIdentification One (framed-arrow u frame) β
  compare-framed-arrow {f = f} {g} u frame β δ given = record
    { identification = δ
    ; source-compatible = constant-frame-compatible ev₀
        (MorphismFamily.source-frame (framed-arrow u frame))
        (MorphismFamily.source-frame β) δ
        (project-frame (pair ev₀ ev₁) pr₁ ev₀ (pair-β₁ ev₀ ev₁) δ
          frame (endpoint-triangle β) (pair-β₁ f g)
          (MorphismFamily.source-frame (framed-arrow u frame))
          (MorphismFamily.source-frame β)
          (projection-frame-image (pair-β₁ f g) (pr₁ ◁ frame) (project-pair₁ ev₀ ev₁ u))
          (pair-evaluation-over₁-One ev₀ ev₁ (MorphismFamily.arrow β)
            (MorphismFamily.source-frame β) (MorphismFamily.target-frame β)) given)
    ; target-compatible = constant-frame-compatible ev₁
        (MorphismFamily.target-frame (framed-arrow u frame))
        (MorphismFamily.target-frame β) δ
        (project-frame (pair ev₀ ev₁) pr₂ ev₁ (pair-β₂ ev₀ ev₁) δ
          frame (endpoint-triangle β) (pair-β₂ f g)
          (MorphismFamily.target-frame (framed-arrow u frame))
          (MorphismFamily.target-frame β)
          (projection-frame-image (pair-β₂ f g) (pr₂ ◁ frame) (project-pair₂ ev₀ ev₁ u))
          (pair-evaluation-over₂-One ev₀ ev₁ (MorphismFamily.arrow β)
            (MorphismFamily.source-frame β) (MorphismFamily.target-frame β)) given) }
```
