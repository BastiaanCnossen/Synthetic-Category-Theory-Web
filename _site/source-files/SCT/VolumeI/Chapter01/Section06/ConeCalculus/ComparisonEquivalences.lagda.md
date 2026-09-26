# Equivalences presenting cone comparisons

Encode a cone comparison as a point of the pullback of its two
leg-identification animae. The point and value constructions retain the
entire matching witness in their computation rules. An equivalence into
this pullback therefore supplies lifting, reflection, and congruence for
full cone comparisons.

These computations concern the chosen equivalence. They do not identify
its action with an independently specified pasting of cone comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action; module Action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (pullbackLift-cong; pullback-η)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherReflection as Reflection
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherComparisons 𝒯 P using (module Calculus)

opaque
  action-congruence : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) {h k : MAP S T} {α β : h =₁ k} →
    α =₂ β → ConeIso₂ (cone-action s α) (cone-action s β)
  action-congruence s {h} {k} {α} {β} δ = Action.Boundary.decode-comparison s h k
    {z = conePre α (Action.universal s h k)}
    {z′ = conePre β (Action.universal s h k)}
    (cone-action (Action.universal s h k) δ)

module Encoded {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) where
  module Boundary = Encoding s t
  module Higher = Reflection.Encoded 𝒯 P s t using (comparison; normalization)
  category : CAT
  category = Pullback Boundary.leftMap Boundary.rightMap

  point : ConeIso s t → Obj-abs category
  point Φ = pullbackLift (Boundary.encode Φ)

  value : Obj-abs category → ConeIso s t
  value x = Boundary.decode (conePre x (pullbackCone Boundary.leftMap Boundary.rightMap))

  opaque
    point-congruence : {Φ Ψ : ConeIso s t} → ConeIso₂ Φ Ψ → point Φ =₁ point Ψ
    point-congruence {Φ} {Ψ} Ω = pullbackLift-cong (Higher.comparison {Φ = Φ} {Ψ = Ψ} Ω)

    value-congruence : {x y : Obj-abs category} → x =₁ y → ConeIso₂ (value x) (value y)
    value-congruence {x} {y} δ = Boundary.decode-comparison
      {z = conePre x (pullbackCone Boundary.leftMap Boundary.rightMap)}
      {z′ = conePre y (pullbackCone Boundary.leftMap Boundary.rightMap)}
      (cone-action (pullbackCone Boundary.leftMap Boundary.rightMap) δ)

    point-computation : (Φ : ConeIso s t) → ConeIso₂ (value (point Φ)) Φ
    point-computation Φ = Boundary.decode-into _ Φ (pullbackLift-β (Boundary.encode Φ))

    value-computation : (x : Obj-abs category) → point (value x) =₁ x
    value-computation x = pullback-η x ∙ pullbackLift-cong
      (Higher.normalization (conePre x (pullbackCone Boundary.leftMap Boundary.rightMap)))

-- Any specified equivalence into the comparison anima supplies a
-- conversion and its complete computation rule. No comparison with a
-- separately chosen pasting of ordinary cone comparisons is implicit.
module Equivalence {A C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) (F : MAP A (Encoded.category s t)) (e : IsEquiv F) where
  module E = Encoded s t
  module H = Calculus s t using (compose)

  action : Obj-abs A → ConeIso s t
  action x = E.value (F ∘ x)

  lift : ConeIso s t → Obj-abs A
  lift Φ = FunctorLift.lift (equiv-lift e (E.point Φ))

  opaque
    image : (Φ : ConeIso s t) → (F ∘ lift Φ) =₁ E.point Φ
    image Φ = FunctorLift.comparison (equiv-lift e (E.point Φ))

    computation : (Φ : ConeIso s t) → ConeIso₂ (action (lift Φ)) Φ
    computation Φ = H.compose {Φ = action (lift Φ)} {Ψ = E.value (E.point Φ)} {Ω = Φ}
      (E.point-computation Φ)
      (E.value-congruence {x = F ∘ lift Φ} {y = E.point Φ} (image Φ))

    reflection : {x y : Obj-abs A} → ConeIso₂ (action x) (action y) → x =₁ y
    reflection {x} {y} Ω = equiv-reflect e x y
      (E.value-computation (F ∘ y) ∙
        (E.point-congruence {Φ = action x} {Ψ = action y} Ω ∙
          E.value-computation (F ∘ x) ⁻¹))

    congruence : {x y : Obj-abs A} → x =₁ y → ConeIso₂ (action x) (action y)
    congruence {x} {y} δ = E.value-congruence {x = F ∘ x} {y = F ∘ y} (F ◁ δ)
```
