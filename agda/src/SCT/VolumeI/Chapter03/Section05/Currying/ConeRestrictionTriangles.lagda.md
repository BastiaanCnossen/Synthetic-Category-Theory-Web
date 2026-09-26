# Restricting a cone with a prescribed right-leg triangle

A comparison of cone restrictions can be composed with a native
identification of the two arguments. Its resulting right leg is the
specified triangle of the second argument. This calculation is used
when the parameter projection of a product is reassociated.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.ConeRestrictionTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse; pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Restrict {C D B Y Z X : CAT} {f : MAP C B} {p : MAP D B}
  (s : Cone f p Y) (t : Cone f p Z)
  (u : FunctorOver (Cone.right t) (Cone.right s))
  (Φ : ConeIso (conePre (FunctorLift.lift u) s) t)
  (image : ConeIso.rightIso Φ =₂ FunctorLift.comparison u)
  (z : MAP X Y) (v : FunctorOver (Cone.right s ∘ z) (Cone.right t))
  (Ψ : FunctorOverIso (compose-over u v) (record { lift = z ; comparison = idIso (Cone.right s ∘ z) })) where
  h = FunctorLift.lift u
  j = FunctorLift.lift v
  q = Cone.right s
  θ = FunctorLift.comparison u
  χ = FunctorLift.comparison v
  A = comp-assoc j h q
  d = θ ▷ j
  tail = d ∙ A ⁻¹
  δ = FunctorOverIso.underlying Ψ
  value = coneIso-compose (cone-action s δ)
    (coneIso-compose (conePre-assoc j h s) (coneIso-pre j (coneIso-inverse Φ)))

  abstract
    cancel-tail : (A ∙ ((ConeIso.rightIso Φ) ⁻¹ ▷ j)) =₂ (tail ⁻¹)
    cancel-tail = (inverse-composite d (A ⁻¹)) ⁻¹ ∙
      (isoComp-cong ((inverse-inverse A) ⁻¹) (idIso (d ⁻¹)) ∙
        isoComp-cong (idIso A) (pre-inverse θ j ∙ (preWhisker j ◁ (＝-inv ◁ image))))

    right-image : ConeIso.rightIso value =₂ χ
    right-image = cancel-right tail χ ∙
      isoComp-cong (FunctorOverIso.compatible Ψ ∙ (isoComp-unitˡ-at (q ◁ δ)) ⁻¹) cancel-tail
```
