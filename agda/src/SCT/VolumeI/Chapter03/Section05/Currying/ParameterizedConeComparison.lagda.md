# Adjoining a parameter to a cone comparison

A comparison from a restricted cone to another cone induces the same
comparison after adjoining a parameter. The right leg is the native
argument-family triangle. Lift the projected left leg with its prescribed
image, so the full matching is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.ParameterizedConeComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone; compositeCone-pre; compositeCone-compatible)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (restriction-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones 𝒯 using (module Parameter)

module Parameters {C D B Y Z : CAT} {f : MAP C B} {p : MAP D B}
  (s : Cone f p Y) (t : Cone f p Z)
  (u : FunctorOver (Cone.right t) (Cone.right s))
  (Φ : ConeIso (conePre (FunctorLift.lift u) s) t)
  (image : ConeIso.rightIso Φ =₂ FunctorLift.comparison u) (X : CAT) where
  module Ps = Parameter X s
  module Pt = Parameter X t
  module Arg = Argument u
  e = FunctorLift.lift u
  H = productMap (id X) e
  π = pr₂ {X} {C}
  r = Cone.right s
  θ = FunctorLift.comparison u
  A = comp-assoc (pr₂ {X} {Z}) e r
  B′ = comp-assoc H (pr₂ {X} {Y}) r
  β = restriction-base X e
  source = conePre H Ps.cone
  target = Pt.cone
  step₁ = coneIso-inverse (compositeCone-pre π f H Ps.cone)
  step₂ = coneIso-compose (coneIso-pre H Ps.projection) step₁
  step₃ = coneIso-compose (conePre-assoc H (pr₂ {X} {Y}) s) step₂
  step₄ = coneIso-compose (cone-action s β) step₃
  step₅ = coneIso-compose (coneIso-inverse (conePre-assoc (pr₂ {X} {Z}) e s)) step₄
  step₆ = coneIso-compose (coneIso-pre (pr₂ {X} {Z}) Φ) step₅
  projected = coneIso-compose (coneIso-inverse Pt.projection) step₆
  tail = (idIso (r ∘ pr₂ {X} {Y}) ▷ H) ∙ (idIso ((r ∘ pr₂ {X} {Y}) ∘ H)) ⁻¹

  abstract
    units : tail =₂ idIso ((r ∘ pr₂ {X} {Y}) ∘ H)
    units = isoComp-unitˡ-at (idIso _) ∙
      isoComp-cong (preWhisker-idIso (r ∘ pr₂ {X} {Y}) H) (inverse-identity _)

    right-image : ConeIso.rightIso projected =₂ FunctorLift.comparison (Arg.family X)
    right-image = isoComp-unitˡ-at (FunctorLift.comparison (Arg.family X)) ∙
      isoComp-cong (inverse-identity (Cone.right target))
        (isoComp-cong (preWhisker (pr₂ {X} {Z}) ◁ image)
          (isoComp-cong (idIso (A ⁻¹))
            (isoComp-cong (idIso (r ◁ β))
              (isoComp-unitʳ-at B′ ∙ isoComp-cong (idIso B′) units))))

  first-s = comp-unitˡ (pr₁ {X} {Y}) ∙
    pair-β₁ (id X ∘ pr₁ {X} {Y}) (Cone.left s ∘ pr₂ {X} {Y})
  first-H = comp-unitˡ (pr₁ {X} {Z}) ∙
    pair-β₁ (id X ∘ pr₁ {X} {Z}) (e ∘ pr₂ {X} {Z})
  first-source = first-H ∙ ((first-s ▷ H) ∙ (comp-assoc H Ps.R (pr₁ {X} {C})) ⁻¹)
  first-target = comp-unitˡ (pr₁ {X} {Z}) ∙
    pair-β₁ (id X ∘ pr₁ {X} {Z}) (Cone.left t ∘ pr₂ {X} {Z})
  first = first-target ⁻¹ ∙ first-source
  second = ConeIso.leftIso projected
  left = pair-iso first second
  adjusted = coneIso-adjust projected (π ◁ left) (FunctorLift.comparison (Arg.family X))
    ((pair-iso-β₂ first second) ⁻¹) right-image

  comparison : ConeIso source target
  comparison = compositeCone-compatible π f source target left (FunctorLift.comparison (Arg.family X))
    (ConeIso.compatible adjusted)
```
