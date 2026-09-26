# Hom expressions under restriction

Restriction changes the terminal parameter of an endpoint cone. Normalize
that leg, retaining both matching coordinates, before applying uniqueness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomNormalization 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
import SCT.VolumeI.Chapter01.Section06.Coordinates.PairedConeCoordinates 𝒯 as Paired

hom-restrict : {Γ Δ C : CAT} {x y : Obj-abs C} →
  MorphismExpression (const {P = Γ} x) (const y) → MAP Δ Γ →
  MorphismExpression (const x) (const y)
hom-restrict {x = x} {y} f r = retarget-expression (restrict-expression f r) (const-pre x r) (const-pre y r)

hom-restrict-cong : {Γ Δ C : CAT} {x y : Obj-abs C}
  {f g : MorphismExpression (const {P = Γ} x) (const y)} →
  ExpressionIso f g → (r : MAP Δ Γ) → ExpressionIso (hom-restrict f r) (hom-restrict g r)
hom-restrict-cong {x = x} {y} Φ r = retarget-expressionIso (restrict-expressionIso Φ r) (const-pre x r) (const-pre y r)

module RestrictedCone {Γ Δ C : CAT} {x y : Obj-abs C}
  (f : MorphismExpression (const {P = Γ} x) (const y)) (r : MAP Δ Γ) where
  module F = MorphismExpression f
  module H = EndpointFiber x y
  module Coordinates = Paired.Coordinates (ev₀ {C}) ev₁ x y
    using (edge₁; edge₂; edge₁-restrict; edge₂-restrict; encode-edge₁; encode-edge₂; cone-from-coordinates)
  before = H.cone (terminate Γ) f
  restricted = conePre r before
  after = H.cone (terminate Δ) (hom-restrict f r)
  τ = terminal-iso (terminate Γ ∘ r) (terminate Δ)

  coordinate : (π : MAP (Ar C) C) (z : Obj-abs C)
    (p : (π ∘ F.arrow) =₁ const z)
    (old : (π ∘ (F.arrow ∘ r)) =₁ (z ∘ (terminate Γ ∘ r)))
    (new : (π ∘ (F.arrow ∘ r)) =₁ const z) →
    old =₂ (comp-assoc r (terminate Γ) z ∙ ((p ▷ r) ∙ (comp-assoc r F.arrow π) ⁻¹)) →
    new =₂ (const-pre z r ∙ ((p ▷ r) ∙ (comp-assoc r F.arrow π) ⁻¹)) →
    (new ∙ (π ◁ idIso (F.arrow ∘ r))) =₂ ((z ◁ τ) ∙ old)
  coordinate π z p old new old-value new-value =
    (isoComp-cong (idIso (z ◁ τ)) old-value) ⁻¹ ∙
    (isoComp-assoc-at (z ◁ τ) (comp-assoc r (terminate Γ) z) ((p ▷ r) ∙ (comp-assoc r F.arrow π) ⁻¹) ∙
      (new-value ∙ (isoComp-unitʳ-at new ∙ isoComp-cong (idIso new) (postWhisker-idIso π (F.arrow ∘ r)))))

  comparison : ConeIso restricted after
  comparison = Coordinates.cone-from-coordinates restricted after (idIso (F.arrow ∘ r)) τ
    (coordinate ev₀ x F.source-frame _ _
      (isoComp-cong (idIso (comp-assoc r (terminate Γ) x))
        (isoComp-cong (preWhisker r ◁ Coordinates.encode-edge₁ F.arrow (terminate Γ) F.source-frame F.target-frame)
          (idIso ((comp-assoc r F.arrow ev₀) ⁻¹))) ∙ Coordinates.edge₁-restrict r before)
      (Coordinates.encode-edge₁ _ _ _ _))
    (coordinate ev₁ y F.target-frame _ _
      (isoComp-cong (idIso (comp-assoc r (terminate Γ) y))
        (isoComp-cong (preWhisker r ◁ Coordinates.encode-edge₂ F.arrow (terminate Γ) F.source-frame F.target-frame)
          (idIso ((comp-assoc r F.arrow ev₁) ⁻¹))) ∙ Coordinates.edge₂-restrict r before)
      (Coordinates.encode-edge₂ _ _ _ _))

hom-intro-restrict : {Γ Δ C : CAT} {x y : Obj-abs C}
  (f : MorphismExpression (const {P = Γ} x) (const y)) (r : MAP Δ Γ) →
  (hom-intro f ∘ r) =₁ hom-intro (hom-restrict f r)
hom-intro-restrict f r = pullbackLift-cong (RestrictedCone.comparison f r) ∙
  (pullbackLift-restrict r (RestrictedCone.before f r)) ⁻¹

hom-expression-restrict : {Γ Δ C : CAT} {x y : Obj-abs C}
  (h : MAP Γ (Hom C x y)) (r : MAP Δ Γ) →
  ExpressionIso (hom-expression (h ∘ r)) (hom-restrict (hom-expression h) r)
hom-expression-restrict h r = expressionIso-compose (hom-β (hom-restrict (hom-expression h) r))
  (hom-expression-cong (hom-intro-restrict (hom-expression h) r ∙ ((hom-η h ▷ r) ⁻¹)))
```
