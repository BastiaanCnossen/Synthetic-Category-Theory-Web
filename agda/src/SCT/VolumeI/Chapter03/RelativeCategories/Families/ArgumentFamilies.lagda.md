# Varying the argument of a relative family

A triangle over the base induces the same triangle after adjoining a
parameter. Restricting the parameter commutes with this operation. Its
specified identification is the product separation comparison, with the
triangle over the base retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M
  using (restriction-base; restriction-over; parameter-base; separation)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-assoc; change-middle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
module PS = Projections 𝒯

module Composite {A B S : CAT} (e : MAP A B) (r : MAP B S) where
  argument : (X : CAT) → FunctorOver ((r ∘ e) ∘ pr₂ {C = X}) (r ∘ pr₂ {C = X})
  argument X = record { lift = productMap (id X) e
    ; comparison = (comp-assoc pr₂ e r) ⁻¹ ∙ restriction-over X e r }

  module Parameter {X Y : CAT} (h : MAP X Y) where
    EY = productMap (id Y) e
    EX = productMap (id X) e
    HA = productMap h (id A)
    HB = productMap h (id B)
    AX = comp-assoc (pr₂ {C = X}) e r
    AY = comp-assoc (pr₂ {C = Y}) e r
    d = PS.lift-base r (e ∘ pr₂) HA (parameter-over h e)
    d′ = parameter-over h (r ∘ e)
    first = PS.compose-base (r ∘ pr₂) EY (restriction-over Y e r) HA d
    second = PS.compose-base (r ∘ pr₂) HB (parameter-over h r) EX (restriction-over X e r)
    χ = productMap-separate h e

    abstract
      raw-square : PS.Square (r ∘ pr₂) first second χ
      raw-square = (PS.lift-compose r pr₂ EY HA (restriction-base Y e) (parameter-over h e)) ⁻¹ ∙
        (PS.lift-square r pr₂ _ _ χ (separation h e) ∙
          isoComp-cong (PS.lift-compose r pr₂ HB EX (parameter-base h B) (restriction-base X e))
            (idIso ((r ∘ pr₂) ◁ χ)))

      middle : ((AX ⁻¹) ∙ d) =₂ (d′ ∙ ((AY ⁻¹) ▷ HA))
      middle = isoComp-cong (idIso d′) ((pre-inverse AY HA) ⁻¹) ∙
        move-square AX d′ d (AY ▷ HA) (lift-assoc pr₂ pr₂ HA (parameter-base h A) e r)

      first-change : FunctorLift.comparison
        (compose-over (argument Y) (parameter-over-functor (r ∘ e) h)) =₂ ((AX ⁻¹) ∙ first)
      first-change = change-middle (r ∘ pr₂) EY HA (restriction-over Y e r) d
        (AY ⁻¹) d′ (AX ⁻¹) middle

      second-change : FunctorLift.comparison
        (compose-over (parameter-over-functor r h) (argument X)) =₂ ((AX ⁻¹) ∙ second)
      second-change = isoComp-assoc-at (AX ⁻¹) (restriction-over X e r)
        ((parameter-over h r ▷ EX) ∙ (comp-assoc EX HB (r ∘ pr₂)) ⁻¹)

      comparison : FunctorOverIso
        (compose-over (argument Y) (parameter-over-functor (r ∘ e) h))
        (compose-over (parameter-over-functor r h) (argument X))
      comparison = record { underlying = χ ; compatible = first-change ⁻¹ ∙
        (isoComp-cong (idIso (AX ⁻¹)) raw-square ∙
          (isoComp-assoc-at (AX ⁻¹) second ((r ∘ pr₂) ◁ χ) ∙
            isoComp-cong second-change (idIso ((r ∘ pr₂) ◁ χ)))) }

module Argument {A B S : CAT} {a′ : MAP A S} {r : MAP B S} (u : FunctorOver a′ r) where
  e = FunctorLift.lift u
  θ = FunctorLift.comparison u
  module Raw = Composite e r
  family : (X : CAT) → FunctorOver (a′ ∘ pr₂ {C = X}) (r ∘ pr₂ {C = X})
  family X = change-source (θ ▷ pr₂) (Raw.argument X)

  abstract
    parameter : {X Y : CAT} (h : MAP X Y) → FunctorOverIso
      (compose-over (family Y) (parameter-over-functor a′ h))
      (compose-over (parameter-over-functor r h) (family X))
    parameter {X} {Y} h = compose-iso-over
      (inverse-iso-over (compose-source-change (θ ▷ pr₂) (Raw.argument X) (parameter-over-functor r h)))
      (compose-iso-over (change-source-iso (θ ▷ pr₂) (Raw.Parameter.comparison h))
        (parameter-change θ h (Raw.argument Y)))
```
