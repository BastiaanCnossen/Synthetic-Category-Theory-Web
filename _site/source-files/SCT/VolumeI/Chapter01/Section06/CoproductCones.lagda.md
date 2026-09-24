# Copairing cones with their matching isomorphisms

The matching is constructed from the two given summand matchings using
the actual restriction equivalence. Both restriction comparisons retain
their compatibility. Cone comparisons can likewise be checked on summands.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section06.CoproductCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.IsomorphismRestriction 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCompatibilityRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯

coproduct-reflect-Iso₂ : {C D E : CAT} {h k : MAP (C ⊔ D) E}
  (α β : h =₁ k) → (α ▷ in₁) =₂ (β ▷ in₁)
  → (α ▷ in₂) =₂ (β ▷ in₂) → α =₂ β
coproduct-reflect-Iso₂ {h = h} {k} α β p q =
  equiv-reflect (coproductIsoRestriction-isEquiv h k) α β
    ((pair-pre (preWhisker in₁) (preWhisker in₂) β) ⁻¹ ∙
      (pair-cong p q ∙ pair-pre (preWhisker in₁) (preWhisker in₂) α))

coproduct-cone-comparison : {A B C D E : CAT} {f : MAP A E} {g : MAP B E}
  (s t : Cone f g (C ⊔ D))
  (α : (Cone.left s) =₁ (Cone.left t)) (β : (Cone.right s) =₁ (Cone.right t))
  (Φ₁ : ConeIso (conePre in₁ s) (conePre in₁ t))
  (Φ₂ : ConeIso (conePre in₂ s) (conePre in₂ t))
  → (ConeIso.leftIso Φ₁) =₂ (α ▷ in₁) → (ConeIso.rightIso Φ₁) =₂ (β ▷ in₁)
  → (ConeIso.leftIso Φ₂) =₂ (α ▷ in₂) → (ConeIso.rightIso Φ₂) =₂ (β ▷ in₂)
  → ConeIso s t
coproduct-cone-comparison {f = f} {g} s t α β Φ₁ Φ₂ l₁ r₁ l₂ r₂ = record
  { leftIso = α ; rightIso = β
  ; compatible = coproduct-reflect-Iso₂ (Cone.match t ∙ (f ◁ α)) ((g ◁ β) ∙ Cone.match s)
      (cone-pre-compatible in₁ s t α β
        (ConeIso.compatible (coneIso-adjust Φ₁ (α ▷ in₁) (β ▷ in₁) l₁ r₁)))
      (cone-pre-compatible in₂ s t α β
        (ConeIso.compatible (coneIso-adjust Φ₂ (α ▷ in₂) (β ▷ in₂) l₂ r₂))) }

module CopairCone {A B C D E : CAT} {f : MAP A E} {g : MAP B E}
  (s : Cone f g C) (t : Cone f g D) where

  left = copair (Cone.left s) (Cone.left t)
  right = copair (Cone.right s) (Cone.right t)
  left₁ = copair-β₁ (Cone.left s) (Cone.left t)
  left₂ = copair-β₂ (Cone.left s) (Cone.left t)
  right₁ = copair-β₁ (Cone.right s) (Cone.right t)
  right₂ = copair-β₂ (Cone.right s) (Cone.right t)
  left-boundary₁ = (f ◁ left₁) ∙ comp-assoc in₁ left f
  left-boundary₂ = (f ◁ left₂) ∙ comp-assoc in₂ left f
  right-boundary₁ = (g ◁ right₁) ∙ comp-assoc in₁ right g
  right-boundary₂ = (g ◁ right₂) ∙ comp-assoc in₂ right g
  matching₁ = right-boundary₁ ⁻¹ ∙ (Cone.match s ∙ left-boundary₁)
  matching₂ = right-boundary₂ ⁻¹ ∙ (Cone.match t ∙ left-boundary₂)
  module Matching = RestrictionLift (f ∘ left) (g ∘ right) matching₁ matching₂

  value : Cone f g (C ⊔ D)
  value = record { left = left ; right = right ; match = Matching.lift }

  restriction₁ : ConeIso (conePre in₁ value) s
  restriction₁ = record
    { leftIso = left₁ ; rightIso = right₁
    ; compatible = encoded-restriction-square (comp-assoc in₁ left f) (comp-assoc in₁ right g)
        (f ◁ left₁) (g ◁ right₁) (Cone.match s) (Matching.lift ▷ in₁) Matching.left-image }

  restriction₂ : ConeIso (conePre in₂ value) t
  restriction₂ = record
    { leftIso = left₂ ; rightIso = right₂
    ; compatible = encoded-restriction-square (comp-assoc in₂ left f) (comp-assoc in₂ right g)
        (f ◁ left₂) (g ◁ right₂) (Cone.match t) (Matching.lift ▷ in₂) Matching.right-image }

module CopairComparison {A B C D E : CAT} {f : MAP A E} {g : MAP B E}
  (s : Cone f g (C ⊔ D)) (t₁ : Cone f g C) (t₂ : Cone f g D)
  (Φ₁ : ConeIso (conePre in₁ s) t₁) (Φ₂ : ConeIso (conePre in₂ s) t₂) where

  module Copair = CopairCone t₁ t₂
  local₁ = coneIso-compose (coneIso-inverse Copair.restriction₁) Φ₁
  local₂ = coneIso-compose (coneIso-inverse Copair.restriction₂) Φ₂
  module Left = RestrictionLift (Cone.left s) Copair.left (ConeIso.leftIso local₁) (ConeIso.leftIso local₂)
  module Right = RestrictionLift (Cone.right s) Copair.right (ConeIso.rightIso local₁) (ConeIso.rightIso local₂)

  opaque
    comparison : ConeIso s Copair.value
    comparison = coproduct-cone-comparison s Copair.value Left.lift Right.lift local₁ local₂
      (Left.left-image ⁻¹) (Right.left-image ⁻¹)
      (Left.right-image ⁻¹) (Right.right-image ⁻¹)
```
