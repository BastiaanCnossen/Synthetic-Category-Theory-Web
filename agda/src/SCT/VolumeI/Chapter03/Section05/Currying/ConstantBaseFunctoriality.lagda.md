# Functors between constant families

A functor between categories with the same constant structure map is a
functor over that base. Postcompose its unique triangle over `One` by
the chosen base point. The identity and composition comparisons retain
the resulting triangles.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as ProjectionSquares

module SCT.VolumeI.Chapter03.Section05.Currying.ConstantBaseFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
open import SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (right-unitor-comp)

terminal-over : {C D : CAT} → MAP C D → FunctorOver (terminate C) (terminate D)
terminal-over f = record { lift = f ; comparison = terminal-iso _ _ }
terminal-identification : {C D : CAT} {f g : MAP C D} → f =₁ g →
  FunctorOverIso (terminal-over f) (terminal-over g)
terminal-identification α = record { underlying = α ; compatible = terminal-Iso₂ _ _ }
terminal-identity : (C : CAT) → FunctorOverIso (terminal-over (id C)) (identity-over (terminate C))
terminal-identity C = record { underlying = idIso (id C) ; compatible = terminal-Iso₂ _ _ }
terminal-composite : {C D E : CAT} (f : MAP C D) (g : MAP D E) →
  FunctorOverIso (compose-over (terminal-over g) (terminal-over f)) (terminal-over (g ∘ f))
terminal-composite f g = record { underlying = idIso (g ∘ f) ; compatible = terminal-Iso₂ _ _ }

module At {S : CAT} (e : Obj-abs S) where
  over : {C D : CAT} (f : MAP C D) → FunctorOver (const {P = C} e) (const {P = D} e)
  over f = postbase e (terminal-over f)
  abstract
    identification : {C D : CAT} {f g : MAP C D} → f =₁ g → FunctorOverIso (over f) (over g)
    identification α = postbase-iso e (terminal-identification α)
    identity : (C : CAT) → FunctorOverIso (over (id C)) (identity-over (const e))
    identity C = compose-iso-over
      (triangle-identification (id C) _ _ ((right-unitor-comp (terminate C) e) ⁻¹))
      (postbase-iso e (terminal-identity C))
    composite : {C D E : CAT} (f : MAP C D) (g : MAP D E) →
      FunctorOverIso (compose-over (over g) (over f)) (over (g ∘ f))
    composite f g = compose-iso-over (postbase-iso e (terminal-composite f g))
      (postbase-composite e (terminal-over f) (terminal-over g))
```
