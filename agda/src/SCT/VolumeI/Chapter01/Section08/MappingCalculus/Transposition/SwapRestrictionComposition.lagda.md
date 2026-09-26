# Product symmetry preserves successive restrictions

The square for a composite restriction agrees with the pasted squares
for its two factors. Both projections retain the specified product
compositors; the varying coordinate also retains its associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.SwapRestrictionData as Swap
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductFirstCoordinate as RestrictionFirst
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate as RestrictionSecond
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterFirstCoordinate as ParameterFirst
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate as ParameterSecond
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.SwapRestrictionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open Swap 𝒯 using (swap-restriction)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
module PS = Projections 𝒯
module RF = RestrictionFirst 𝒯 M
module RS = RestrictionSecond 𝒯 M
module PF = ParameterFirst 𝒯 M
module PQ = ParameterSecond 𝒯 M

module Composite {X A B C : CAT} (f : MAP A B) (g : MAP B C) where
  SA = swap {X} {A}
  SB = swap {X} {B}
  SC = swap {X} {C}
  Lf = productRestriction X f
  Lg = productRestriction X g
  Lgf = productRestriction X (g ∘ f)
  Rf = productMap f (id X)
  Rg = productMap g (id X)
  Rgf = productMap (g ∘ f) (id X)
  χ = productRestriction-comp X f g
  κ = slice-comparison {C = X} g f
  Sf = swap-restriction {X} f
  Sg = swap-restriction {X} g
  Sgf = swap-restriction {X} (g ∘ f)
  short = (κ ▷ SA) ∙ paste (Sg ⁻¹) (Sf ⁻¹)
  long = Sgf ⁻¹ ∙ (SC ◁ χ)

  module Second where
    bA = pair-β₂ (pr₂ {X} {A}) pr₁
    bB = pair-β₂ (pr₂ {X} {B}) pr₁
    bC = pair-β₂ (pr₂ {X} {C}) pr₁
    module Diagram = PS.Pasting pr₁ pr₁ pr₁ pr₂ pr₂ pr₂ SA SB SC Lf Lg Rf Rg
      (RF.restriction-base X f) (RF.restriction-base X g)
      (RS.parameter-base f X) (RS.parameter-base g X) bA bB bC (Sf ⁻¹) (Sg ⁻¹)
    final = PS.compose-base pr₂ Rgf (RS.parameter-base (g ∘ f) X) SA bA
    middle = PS.compose-base pr₂ SC bC Lgf (RF.restriction-base X (g ∘ f))

    abstract
      short-square : PS.Square pr₂ Diagram.b₀ final short
      short-square = PS.compose-square pr₂ Diagram.b₀ Diagram.b₅ final (κ ▷ SA)
        (paste (Sg ⁻¹) (Sf ⁻¹))
        (PS.pre-square pr₂ SA
          (PS.compose-base pr₂ Rg (RS.parameter-base g X) Rf (RS.parameter-base f X))
          (RS.parameter-base (g ∘ f) X) bA κ (PQ.compositor f g X))
        (Diagram.paste-square
          (PS.inverse-square pr₂ _ _ Sf (Swap.Coordinates.projection₂ 𝒯 f))
          (PS.inverse-square pr₂ _ _ Sg (Swap.Coordinates.projection₂ 𝒯 g)))

      long-square : PS.Square pr₂ Diagram.b₀ final long
      long-square = PS.compose-square pr₂ Diagram.b₀ middle final (Sgf ⁻¹) (SC ◁ χ)
        (PS.inverse-square pr₂ _ _ Sgf (Swap.Coordinates.projection₂ 𝒯 (g ∘ f)))
        (PS.post-square pr₂ SC bC
          (PS.compose-base pr₁ Lg (RF.restriction-base X g) Lf (RF.restriction-base X f))
          (RF.restriction-base X (g ∘ f)) χ (RF.compositor X f g))

      comparison : (pr₂ ◁ short) =₂ (pr₂ ◁ long)
      comparison = cancel-left-reflect final (long-square ⁻¹ ∙ short-square)

  module First where
    bA = PS.lift-base g (f ∘ pr₁) SA (PS.lift-base f pr₁ SA (pair-β₁ pr₂ pr₁))
    bB = PS.lift-base g pr₁ SB (pair-β₁ pr₂ pr₁)
    bC = pair-β₁ (pr₂ {X} {C}) pr₁
    bLf = RS.restriction-over X f g
    bLg = RS.restriction-base X g
    bRf = PF.parameter-over f g X
    bRg = RF.parameter-base g X
    module Single = Swap.Coordinates 𝒯 {X} f
    first-source = PS.compose-base (g ∘ pr₁) Rf bRf SA bA
    first-target = PS.compose-base (g ∘ pr₁) SB bB Lf bLf

    abstract
      first-square : PS.Square (g ∘ pr₁) first-source first-target Sf
      first-square = (PS.lift-compose g pr₁ Rf SA (RF.parameter-base f X)
          (PS.lift-base f pr₁ SA (pair-β₁ pr₂ pr₁))) ⁻¹ ∙
        (PS.lift-square g pr₁ Single.first-source-base Single.first-target-base Sf Single.projection₁ ∙
          isoComp-cong (PS.lift-compose g pr₁ SB Lf (pair-β₁ pr₂ pr₁) (RS.restriction-base X f))
            (idIso ((g ∘ pr₁) ◁ Sf)))

    module Diagram = PS.Pasting (g ∘ (f ∘ pr₂)) (g ∘ pr₂) pr₂
      (g ∘ (f ∘ pr₁)) (g ∘ pr₁) pr₁ SA SB SC Lf Lg Rf Rg
      bLf bLg bRf bRg bA bB bC (Sf ⁻¹) (Sg ⁻¹)
    final = PS.compose-base pr₁ Rgf (PF.composite-base f g X) SA bA
    middle = PS.compose-base pr₁ SC bC Lgf (RS.composite-base X f g)
    module SingleComposite = Swap.Coordinates 𝒯 {X} (g ∘ f)
    η = comp-assoc (pr₂ {X} {A}) f g

    abstract
      composite-source : final =₂ (η ∙ SingleComposite.first-source-base)
      composite-source = change-middle pr₁ Rgf SA (RF.parameter-base (g ∘ f) X)
        (PS.lift-base (g ∘ f) pr₁ SA (pair-β₁ pr₂ pr₁))
        (comp-assoc pr₁ f g) bA η (lift-assoc pr₁ pr₂ SA (pair-β₁ pr₂ pr₁) f g)

      composite-target : middle =₂ (η ∙ SingleComposite.first-target-base)
      composite-target = isoComp-assoc-at η (RS.restriction-base X (g ∘ f))
        ((bC ▷ Lgf) ∙ (comp-assoc Lgf SC pr₁) ⁻¹)

      composite-square : PS.Square pr₁ final middle Sgf
      composite-square = composite-source ⁻¹ ∙
        (isoComp-cong (idIso η) SingleComposite.projection₁ ∙
        (isoComp-assoc-at η SingleComposite.first-target-base (pr₁ ◁ Sgf) ∙
          isoComp-cong composite-target (idIso (pr₁ ◁ Sgf))))

      short-square : PS.Square pr₁ Diagram.b₀ final short
      short-square = PS.compose-square pr₁ Diagram.b₀ Diagram.b₅ final (κ ▷ SA)
        (paste (Sg ⁻¹) (Sf ⁻¹))
        (PS.pre-square pr₁ SA (PS.compose-base pr₁ Rg bRg Rf bRf)
          (PF.composite-base f g X) bA κ (PF.compositor f g X))
        (Diagram.paste-square (PS.inverse-square (g ∘ pr₁) _ _ Sf first-square)
          (PS.inverse-square pr₁ _ _ Sg (Swap.Coordinates.projection₁ 𝒯 g)))

      long-square : PS.Square pr₁ Diagram.b₀ final long
      long-square = PS.compose-square pr₁ Diagram.b₀ middle final (Sgf ⁻¹) (SC ◁ χ)
        (PS.inverse-square pr₁ _ _ Sgf composite-square)
        (PS.post-square pr₁ SC bC (PS.compose-base pr₂ Lg bLg Lf bLf)
          (RS.composite-base X f g) χ (RS.compositor X f g))

      comparison : (pr₁ ◁ short) =₂ (pr₁ ◁ long)
      comparison = cancel-left-reflect final (long-square ⁻¹ ∙ short-square)

  abstract
    comparison : short =₂ long
    comparison = pair-iso-extensionality First.comparison Second.comparison
```
