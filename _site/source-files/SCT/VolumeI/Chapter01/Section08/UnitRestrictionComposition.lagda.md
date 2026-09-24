# Decoding and successive restrictions

The comparison for a composite restriction is the pasting of the two
terminal-product comparisons. We check the second projection over the
final category; the first projection lands in the terminal category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.UnitRestrictionData as Unit
import SCT.VolumeI.Chapter01.Section08.ProductSecondCoordinate as Second
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductUnits

module SCT.VolumeI.Chapter01.Section08.UnitRestrictionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; cancel-left-reflect)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (right-unitor-comp; triangle-whiskered)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
module PS = Projections 𝒯
module RS = Second 𝒯 M

unit-lift-assoc : {R K B C : CAT} (π : MAP K R) (I : MAP R K)
  (b : (π ∘ I) =₁ (id R)) (f : MAP R B) (g : MAP B C) →
  (comp-unitʳ (g ∘ f) ∙ PS.lift-base (g ∘ f) π I b) =₂
    (PS.lift-base g (f ∘ π) I (comp-unitʳ f ∙ PS.lift-base f π I b) ∙
      (comp-assoc π f g ▷ I))
unit-lift-assoc {R} π I b f g =
  let L = PS.lift-base f π I b
      D = PS.lift-base g (f ∘ π) I L
      V = PS.lift-base (g ∘ f) π I b
      δ = g ◁ comp-unitʳ f
      A = comp-assoc π f g ▷ I
      B = comp-assoc I (f ∘ π) g
      merge = isoComp-cong ((postWhisker-isoComp-at g (comp-unitʳ f) L) ⁻¹) (idIso B) ∙
        (isoComp-assoc-at δ (g ◁ L) B) ⁻¹
  in isoComp-cong merge (idIso A) ∙
    ((isoComp-assoc-at δ D A) ⁻¹ ∙
    (isoComp-cong (idIso δ) (lift-assoc π (id R) I b f g) ∙
    (isoComp-assoc-at δ (comp-assoc (id R) f g) V ∙
      isoComp-cong (right-unitor-comp f g) (idIso V))))

module Composite {A B C : CAT} (f : MAP A B) (g : MAP B C) where
  module F = Unit.Coordinates 𝒯 M f
  module G = Unit.Coordinates 𝒯 M g
  module GF = Unit.Coordinates 𝒯 M (g ∘ f)
  IA = oneProduct-in A
  IB = oneProduct-in B
  IC = oneProduct-in C
  bA = PS.lift-base g (f ∘ pr₂) IA F.endpoint
  bB = G.endpoint
  bC = oneProduct-retraction C
  bF = RS.restriction-over One f g
  bG = RS.restriction-base One g
  first-source = PS.compose-base (g ∘ pr₂) F.step bF IA bA
  first-target = PS.compose-base (g ∘ pr₂) IB bB f (idIso (g ∘ f))
  first-head = PS.lift-base g pr₂ IB (oneProduct-retraction B)
  first-tail = PS.lift-base g (id B) f (comp-unitˡ f)

  abstract
    first-endpoint : first-target =₂ (PS.lift-base g pr₂ (IB ∘ f) F.target)
    first-endpoint = PS.lift-compose g pr₂ IB f (oneProduct-retraction B) (comp-unitˡ f) ∙
      (isoComp-unitˡ-at (PS.compose-base (g ∘ pr₂) IB first-head f first-tail) ∙
        change-middle (g ∘ pr₂) IB f first-head first-tail
          (comp-unitʳ g) (idIso (g ∘ f)) (idIso (g ∘ f))
          (isoComp-cong (idIso (idIso (g ∘ f))) ((triangle-whiskered f g) ⁻¹)))

    first-square : PS.Square (g ∘ pr₂) first-source first-target F.value
    first-square = (PS.lift-compose g pr₂ F.step IA F.base F.endpoint) ⁻¹ ∙
      (PS.lift-square g pr₂ F.source F.target F.value F.projection₂ ∙
        isoComp-cong first-endpoint (idIso ((g ∘ pr₂) ◁ F.value)))

  module Diagram = PS.Pasting (g ∘ f) g (id C)
    (g ∘ (f ∘ pr₂)) (g ∘ pr₂) pr₂ IA IB IC f g F.step G.step
    (idIso (g ∘ f)) (comp-unitˡ g) bF bG bA bB bC
    (F.value ⁻¹) (G.value ⁻¹)
  χ = productRestriction-comp One f g
  final = PS.compose-base pr₂ GF.step (RS.composite-base One f g) IA bA
  short = (χ ▷ IA) ∙ paste (G.value ⁻¹) (F.value ⁻¹)
  long = GF.value ⁻¹
  top = PS.compose-base (id C) g (comp-unitˡ g) f (idIso (g ∘ f))
  top-associator = comp-assoc f g (id C)

  abstract
    final-normalize : final =₂ GF.source
    final-normalize = isoComp-unitˡ-at GF.source ∙
      change-middle pr₂ GF.step IA GF.base GF.endpoint
        (comp-assoc pr₂ f g) bA (idIso (g ∘ f))
        (unit-lift-assoc pr₂ IA (oneProduct-retraction A) f g ∙ isoComp-unitˡ-at GF.endpoint)

    top-normalize : top =₂ (comp-unitˡ (g ∘ f))
    top-normalize = cancel-right top-associator (comp-unitˡ (g ∘ f)) ∙
      (isoComp-cong ((left-unitor-comp f g) ⁻¹) (idIso (top-associator ⁻¹)) ∙
        isoComp-unitˡ-at ((comp-unitˡ g ▷ f) ∙ top-associator ⁻¹))

    initial-normalize : Diagram.b₀ =₂ GF.target
    initial-normalize = isoComp-cong top-normalize
      (idIso ((bC ▷ (g ∘ f)) ∙ (comp-assoc (g ∘ f) IC pr₂) ⁻¹))

    short-square : PS.Square pr₂ Diagram.b₀ final short
    short-square = PS.compose-square pr₂ Diagram.b₀ Diagram.b₅ final (χ ▷ IA)
      (paste (G.value ⁻¹) (F.value ⁻¹))
      (PS.pre-square pr₂ IA (PS.compose-base pr₂ G.step bG F.step bF)
        (RS.composite-base One f g) bA χ (RS.compositor One f g))
      (Diagram.paste-square
        (PS.inverse-square (g ∘ pr₂) first-source first-target F.value first-square)
        (PS.inverse-square pr₂ G.source G.target G.value G.projection₂))

    long-square : PS.Square pr₂ Diagram.b₀ final long
    long-square = initial-normalize ⁻¹ ∙
      (PS.inverse-square pr₂ GF.source GF.target GF.value GF.projection₂ ∙
        isoComp-cong final-normalize (idIso (pr₂ ◁ long)))

    comparison : short =₂ long
    comparison = pair-iso-extensionality (terminal-Iso₂ _ _)
      (cancel-left-reflect final (long-square ⁻¹ ∙ short-square))
```
