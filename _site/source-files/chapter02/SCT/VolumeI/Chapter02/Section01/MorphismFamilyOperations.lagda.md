# Changing the parameter and endpoints of a morphism family

Restriction pulls both endpoint triangles back along a parameter map.
Changing endpoints composes their specified identifications with the two
frames. Both operations preserve comparisons of framed families. These
operations are already used privately by WalkingTriangle; the common owner
must be shared on adoption.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-unitʳ; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle; restrict-square-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (MorphismFamily; MorphismFamilyIdentification; ev₀; ev₁)

private
  module _ {Γ : Context} {P K C : CAT Γ} (pi : MAP K C)
    {u v : MAP P K} {f : MAP P C}
    (a : (pi ∘ u) =₁ f) (b : (pi ∘ v) =₁ f) (delta : u =₁ v) where
    constant-frame : CompatibleOver pi a b delta → (const b ∙ (pi ◁ delta)) =₁ const a
    constant-frame given = (const-One a) ⁻¹ ∙
      (given ∙ comp₌-cong (const-One b) (id₌ (pi ◁ delta)))
    absolute-frame : (const b ∙ (pi ◁ delta)) =₁ const a → CompatibleOver pi a b delta
    absolute-frame given = const-One a ∙
      (given ∙ comp₌-cong ((const-One b) ⁻¹) (id₌ (pi ◁ delta)))

module _ {Γ : Context} where
  family-comparison : {P C : CAT Γ} {f g : MAP P C} (alpha beta : MorphismFamily f g)
    (delta : MorphismFamily.arrow alpha =₁ MorphismFamily.arrow beta)
    → CompatibleOver ev₀ (MorphismFamily.source-frame alpha) (MorphismFamily.source-frame beta) delta
    → CompatibleOver ev₁ (MorphismFamily.target-frame alpha) (MorphismFamily.target-frame beta) delta
    → MorphismFamilyIdentification One alpha beta
  family-comparison alpha beta delta source target = record
    { identification = delta
    ; source-compatible = constant-frame ev₀ _ _ delta source
    ; target-compatible = constant-frame ev₁ _ _ delta target }

  module FamilyComparison {P C : CAT Γ} {f g : MAP P C} {alpha beta : MorphismFamily f g}
    (given : MorphismFamilyIdentification One alpha beta) where
    identification : MorphismFamily.arrow alpha =₁ MorphismFamily.arrow beta
    identification = MorphismFamilyIdentification.identification given
    source : CompatibleOver ev₀ (MorphismFamily.source-frame alpha) (MorphismFamily.source-frame beta) identification
    source = absolute-frame ev₀ _ _ identification (MorphismFamilyIdentification.source-compatible given)
    target : CompatibleOver ev₁ (MorphismFamily.target-frame alpha) (MorphismFamily.target-frame beta) identification
    target = absolute-frame ev₁ _ _ identification (MorphismFamilyIdentification.target-compatible given)

  restrict-family : {P Q C : CAT Γ} {f g : MAP P C}
    → MorphismFamily f g → (r : MAP Q P) → MorphismFamily (f ∘ r) (g ∘ r)
  restrict-family alpha r = record
    { arrow = MorphismFamily.arrow alpha ∘ r
    ; source-frame = restrict-triangle ev₀ (MorphismFamily.arrow alpha) (MorphismFamily.source-frame alpha) r
    ; target-frame = restrict-triangle ev₁ (MorphismFamily.arrow alpha) (MorphismFamily.target-frame alpha) r }

  retarget-family : {P C : CAT Γ} {f g f′ g′ : MAP P C}
    → MorphismFamily f g → f =₁ f′ → g =₁ g′ → MorphismFamily f′ g′
  retarget-family alpha p q = record
    { arrow = MorphismFamily.arrow alpha
    ; source-frame = p ∙ MorphismFamily.source-frame alpha
    ; target-frame = q ∙ MorphismFamily.target-frame alpha }

  private
    restrict-compatible : {P Q K C : CAT Γ} (pi : MAP K C) {u v : MAP P K} {f : MAP P C}
      (a : (pi ∘ u) =₁ f) (b : (pi ∘ v) =₁ f) (delta : u =₁ v) (r : MAP Q P)
      → CompatibleOver pi a b delta
      → CompatibleOver pi (restrict-triangle pi u a r) (restrict-triangle pi v b r) (delta ▷ r)
    restrict-compatible pi {u} {v} {f} a b delta r given =
      comp₌-unitˡ-One (restrict-triangle pi u a r) ∙
        (comp₌-cong (preWhisker-id₌ f r) (id₌ (restrict-triangle pi u a r)) ∙
          restrict-square-One pi delta (id₌ f) a b r
            (((comp₌-unitˡ-One a) ⁻¹) ∙ given))

  restrict-family-comparison : {P Q C : CAT Γ} {f g : MAP P C} {alpha beta : MorphismFamily f g}
    (r : MAP Q P) → MorphismFamilyIdentification One alpha beta
    → MorphismFamilyIdentification One (restrict-family alpha r) (restrict-family beta r)
  restrict-family-comparison {alpha = alpha} {beta} r given =
    family-comparison (restrict-family alpha r) (restrict-family beta r) (F.identification ▷ r)
      (restrict-compatible ev₀ _ _ F.identification r F.source)
      (restrict-compatible ev₁ _ _ F.identification r F.target)
    where module F = FamilyComparison given

  retarget-family-comparison : {P C : CAT Γ} {f g f′ g′ : MAP P C} {alpha beta : MorphismFamily f g}
    (p : f =₁ f′) (q : g =₁ g′) → MorphismFamilyIdentification One alpha beta
    → MorphismFamilyIdentification One (retarget-family alpha p q) (retarget-family beta p q)
  retarget-family-comparison {alpha = alpha} {beta} p q given =
    family-comparison (retarget-family alpha p q) (retarget-family beta p q) F.identification
      (comp₌-cong (id₌ p) F.source ∙ comp₌-assoc p (MorphismFamily.source-frame beta) (ev₀ ◁ F.identification))
      (comp₌-cong (id₌ q) F.target ∙ comp₌-assoc q (MorphismFamily.target-frame beta) (ev₁ ◁ F.identification))
    where module F = FamilyComparison given

  restrict-family-id : {P C : CAT Γ} {f g : MAP P C} (alpha : MorphismFamily f g)
    → MorphismFamilyIdentification One
        (retarget-family (restrict-family alpha (id P)) (comp-unitʳ f) (comp-unitʳ g)) alpha
  restrict-family-id {P} alpha = family-comparison _ alpha (comp-unitʳ (MorphismFamily.arrow alpha))
    (compatible-unitʳ ev₀ (MorphismFamily.arrow alpha) (MorphismFamily.source-frame alpha))
    (compatible-unitʳ ev₁ (MorphismFamily.arrow alpha) (MorphismFamily.target-frame alpha))
```
