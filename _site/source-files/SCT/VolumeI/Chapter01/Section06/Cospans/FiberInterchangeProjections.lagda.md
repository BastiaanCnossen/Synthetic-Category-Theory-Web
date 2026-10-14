# Projection squares for cospan fibers

The composite-leg fibers supply the cartesian squares used to paste the
fibers of a cospan map. Their maps retain full cone computations. The
right component map agrees with the existing fiber map after projection,
and the target family is recovered by a whole-cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchangeProjections
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses
open Inverses vocabulary terminal products productLaws composition vertical using (cancel-right; cancel-left; cancel-left-reflect)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change; coneIso-swap; coneSwap-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-composite; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Actions
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Normalized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (right-unitor-comp)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section06.Cospans.Fibers as Fibers
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones as Edges
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)

module At {C D E C′ D′ E′ Γ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (x : MAP Γ (Pullback f′ g′)) where
  private
    module F = CospanMap F using (mapCone; pullbackMap; pullbackMap-β)
      renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
    module Fib = Fibers.At 𝒯 P F x
      using (family; left-family; right-family; base-family; matching;
        left-fiber; right-fiber; base-fiber; left-map; right-map;
        left-image-cone; right-image-cone; left-image; right-image; left-restriction)
    A = pullbackCone F.u Fib.left-family
    B = pullbackCone F.v Fib.right-family
    Z = pullbackCone F.w Fib.base-family
    target = pullbackCone f′ g′

  composite-fiber : CAT
  composite-fiber = Pullback (F.w ∘ g) Fib.base-family
  target-leg-fiber : CAT
  target-leg-fiber = Pullback g′ Fib.base-family
  composite-cone : Cone (F.w ∘ g) Fib.base-family composite-fiber
  composite-cone = pullbackCone (F.w ∘ g) Fib.base-family
  target-leg-cone : Cone g′ Fib.base-family target-leg-fiber
  target-leg-cone = pullbackCone g′ Fib.base-family

  base-image : Cone F.w Fib.base-family composite-fiber
  base-image = compositeCone g F.w composite-cone
  to-base : MAP composite-fiber Fib.base-fiber
  to-base = pullbackLift base-image
  base-computation : ConeIso (conePre to-base Z) base-image
  base-computation = pullbackLift-β base-image
  private
    module Base = Cancellation.At 𝒯 P g F.w Fib.base-family Z
      (pullbackCone-isPullback F.w Fib.base-family) composite-cone
      (pullbackCone-isPullback (F.w ∘ g) Fib.base-family) to-base base-computation
      using (square; square-isPullback)
  base-square : Cone (Cone.left Z) g composite-fiber
  base-square = record { left = to-base ; right = Cone.left composite-cone
    ; match = ConeIso.leftIso base-computation }
  opaque
    base-square-isPullback : IsPullback base-square
    base-square-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _ (inverse-inverse (ConeIso.leftIso base-computation)))
      (pullback-swap Base.square Base.square-isPullback)

  target-image : Cone f′ g′ target-leg-fiber
  target-image = compositeCone Fib.left-family f′ (coneSwap target-leg-cone)
  to-target : MAP target-leg-fiber (Pullback f′ g′)
  to-target = pullbackLift target-image
  target-computation : ConeIso (conePre to-target target) target-image
  target-computation = pullbackLift-β target-image
  private
    module Target = Cancellation.At 𝒯 P Fib.left-family f′ g′ target
      (pullbackCone-isPullback f′ g′) (coneSwap target-leg-cone)
      (pullback-swap target-leg-cone (pullbackCone-isPullback g′ Fib.base-family))
      to-target target-computation using (square; square-isPullback)
  target-square : Cone (Cone.left target) Fib.left-family target-leg-fiber
  target-square = record { left = to-target ; right = Cone.right target-leg-cone
    ; match = ConeIso.leftIso target-computation }
  opaque
    target-square-isPullback : IsPullback target-square
    target-square-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _ (inverse-inverse (ConeIso.leftIso target-computation)))
      (pullback-swap Target.square Target.square-isPullback)

  private
    module RightEdge = Edges.At 𝒯 F.v g′ F.β Fib.base-family using (edge; action-with-legs; restrict-with-legs)
    module RightImage = Images.Along 𝒯 F.v Fib.right-family g F.w g′ Fib.base-family F.β (Fib.matching ⁻¹)
      using (factor-restriction)
  right-image : Cone g′ Fib.base-family composite-fiber
  right-image = RightEdge.edge composite-cone
  right-map : MAP composite-fiber target-leg-fiber
  right-map = pullbackLift right-image
  right-computation : ConeIso (conePre right-map target-leg-cone) right-image
  right-computation = pullbackLift-β right-image
  private
    module Right = Cancellation.Framed 𝒯 P F.v g′ Fib.base-family F.β
      target-leg-cone (pullbackCone-isPullback g′ Fib.base-family)
      composite-cone (pullbackCone-isPullback (F.w ∘ g) Fib.base-family)
      using (module WithComparison)
    module RightSquare = Right.WithComparison right-map right-computation using (square; square-isPullback)
  right-square : Cone F.v (Cone.left target-leg-cone) composite-fiber
  right-square = RightSquare.square
  right-square-isPullback : IsPullback right-square
  right-square-isPullback = RightSquare.square-isPullback


  section-cone : Cone g′ Fib.base-family Γ
  section-cone = record { left = Fib.right-family ; right = id Γ
    ; match = (comp-unitʳ Fib.base-family) ⁻¹ ∙ Fib.matching ⁻¹ }
  section : MAP Γ target-leg-fiber
  section = pullbackLift section-cone
  section-computation : ConeIso (conePre section target-leg-cone) section-cone
  section-computation = pullbackLift-β section-cone
  private
    module RightBaseChange = BaseChange.Along 𝒯 P F.v (Cone.left target-leg-cone)
      right-square right-square-isPullback section (ConeIso.leftIso section-computation)
      B (pullbackCone-isPullback F.v Fib.right-family)
      using (factor-cone; module WithFactor)
  component-cone : Cone (F.w ∘ g) Fib.base-family Fib.right-fiber
  component-cone = record
    { left = Cone.left B ; right = Cone.right B
    ; match = Cone.match Fib.right-image-cone ∙ comp-assoc (Cone.left B) g F.w }
  direct-component-map : MAP Fib.right-fiber composite-fiber
  direct-component-map = pullbackLift component-cone
  direct-component-computation : ConeIso (conePre direct-component-map composite-cone) component-cone
  direct-component-computation = pullbackLift-β component-cone

  opaque
    component-base-normal : ConeIso (compositeCone g F.w component-cone) Fib.right-image-cone
    component-base-normal = cone-match-change _ _ _ _
      (cancel-right (comp-assoc (Cone.left B) g F.w) (Cone.match Fib.right-image-cone))

    component-base-computation :
      ConeIso (conePre (to-base ∘ direct-component-map) Z) Fib.right-image-cone
    component-base-computation = coneIso-compose component-base-normal
      (coneIso-compose (compositeConeIso g F.w direct-component-computation)
        (coneIso-compose (compositeCone-pre g F.w direct-component-map composite-cone)
          (coneIso-compose (coneIso-pre direct-component-map base-computation)
            (coneIso-inverse (conePre-assoc direct-component-map to-base Z)))))

    component-map-identification : (to-base ∘ direct-component-map) =₁ Fib.right-map
    component-map-identification = pullback-reflect _ _
      (coneIso-compose (coneIso-inverse Fib.right-image) component-base-computation)


  component-target-computation-raw :
    ConeIso (conePre (right-map ∘ direct-component-map) target-leg-cone)
      (conePre (section ∘ Cone.right B) target-leg-cone)
  component-target-computation-raw = coneIso-compose (conePre-assoc (Cone.right B) section target-leg-cone)
    (coneIso-compose (coneIso-pre (Cone.right B) (coneIso-inverse section-computation))
      (coneIso-compose (RightImage.factor-restriction B)
        (coneIso-compose (RightEdge.action-with-legs direct-component-computation)
          (coneIso-compose (RightEdge.restrict-with-legs direct-component-map composite-cone)
            (coneIso-compose (coneIso-pre direct-component-map right-computation)
              (coneIso-inverse (conePre-assoc direct-component-map right-map target-leg-cone)))))))


  private
    component-first-edge = comp-assoc direct-component-map (Cone.left composite-cone) F.v ∙
      ((ConeIso.leftIso right-computation ▷ direct-component-map) ∙
        (comp-assoc direct-component-map right-map (Cone.left target-leg-cone)) ⁻¹)
    component-second-edge = (ConeIso.leftIso section-computation ▷ Cone.right B) ∙
      (comp-assoc (Cone.right B) section (Cone.left target-leg-cone)) ⁻¹
    component-tail = Cone.match B ∙ ((F.v ◁ ConeIso.leftIso direct-component-computation) ∙ component-first-edge)

  component-target-computation :
    ConeIso (conePre (right-map ∘ direct-component-map) target-leg-cone)
      (conePre (section ∘ Cone.right B) target-leg-cone)
  component-target-computation = coneIso-adjust component-target-computation-raw
    (component-second-edge ⁻¹ ∙ component-tail)
    (ConeIso.rightIso component-target-computation-raw) left-normal (idIso _)
    where
    A₀ = comp-assoc (Cone.right B) section (Cone.left target-leg-cone)
    κ = ConeIso.leftIso section-computation
    inverse-edge : (component-second-edge ⁻¹) =₂ (A₀ ∙ (κ ⁻¹ ▷ Cone.right B))
    inverse-edge = isoComp-cong (inverse-inverse A₀) ((pre-inverse κ (Cone.right B)) ⁻¹) ∙
      inverse-composite (κ ▷ Cone.right B) (A₀ ⁻¹)
    left-normal = isoComp-cong (inverse-edge ⁻¹) (idIso component-tail) ∙
      (isoComp-assoc-at A₀ (κ ⁻¹ ▷ Cone.right B) component-tail) ⁻¹

  private
    module ComponentLift = Lifting.Lift 𝒯 P (right-map ∘ direct-component-map)
      (section ∘ Cone.right B) component-target-computation using (lift; left-image)
  component-target-identification : (right-map ∘ direct-component-map) =₁ (section ∘ Cone.right B)
  component-target-identification = ComponentLift.lift


  direct-factor-computation :
    ConeIso (conePre direct-component-map (coneSwap right-square)) RightBaseChange.factor-cone
  direct-factor-computation = record
    { leftIso = component-target-identification
    ; rightIso = ConeIso.leftIso direct-component-computation
    ; compatible = isoComp-cong (idIso _) first-normal ∙
        (cancel-left (Cone.match B) ((F.v ◁ ConeIso.leftIso direct-component-computation) ∙ component-first-edge) ∙
        (isoComp-cong (idIso ((Cone.match B) ⁻¹)) (cancel-left (component-second-edge ⁻¹) component-tail ∙
          isoComp-cong (inverse-inverse component-second-edge ⁻¹) (idIso _)) ∙
        (isoComp-assoc-at ((Cone.match B) ⁻¹) component-second-edge (component-second-edge ⁻¹ ∙ component-tail) ∙
          isoComp-cong (idIso _) ComponentLift.left-image))) }
    where
    first-normal : component-first-edge =₂ Cone.match (conePre direct-component-map (coneSwap right-square))
    first-normal = isoComp-cong (idIso _)
      (isoComp-cong ((preWhisker direct-component-map ◁ inverse-inverse (ConeIso.leftIso right-computation)) ⁻¹)
        (idIso _))

  private
    module DirectBaseChange = RightBaseChange.WithFactor direct-component-map direct-factor-computation
      using (square; square-isPullback)
  direct-component-square : Cone right-map section Fib.right-fiber
  direct-component-square = DirectBaseChange.square
  direct-component-square-isPullback : IsPullback direct-component-square
  direct-component-square-isPullback = DirectBaseChange.square-isPullback

  intermediate : CAT
  intermediate = Pullback Fib.left-map to-base
  intermediate-cone : Cone Fib.left-map to-base intermediate
  intermediate-cone = pullbackCone Fib.left-map to-base
  private
    module BasePaste = Pasting.Pasting 𝒯 P Fib.left-map (Cone.left Z) g
      base-square base-square-isPullback using (module Paste; paste-isPullback)
    left-projection = ConeIso.leftIso Fib.left-image
    module Change = ArrowChange.ChangeLeft 𝒯 P left-projection g using (preserve)
  source-outer : Cone (f ∘ Cone.left A) g intermediate
  source-outer = changeLeft left-projection (BasePaste.Paste.flatten intermediate-cone)
  opaque
    source-outer-isPullback : IsPullback source-outer
    source-outer-isPullback = Change.preserve (BasePaste.Paste.flatten intermediate-cone)
      (BasePaste.paste-isPullback intermediate-cone (pullbackCone-isPullback Fib.left-map to-base))

  source-image : Cone f g intermediate
  source-image = compositeCone (Cone.left A) f source-outer
  to-source : MAP intermediate (Pullback f g)
  to-source = pullbackLift source-image
  source-computation : ConeIso (conePre to-source (pullbackCone f g)) source-image
  source-computation = pullbackLift-β source-image
  private
    module Source = Cancellation.At 𝒯 P (Cone.left A) f g (pullbackCone f g)
      (pullbackCone-isPullback f g) source-outer source-outer-isPullback to-source source-computation
      using (square; square-isPullback)
    module SourcePaste = BaseChange.Successive 𝒯 P Fib.left-family F.u (coneSwap A)
      (Cone.left (pullbackCone f g)) Source.square using (composite; composite-isPullback)
  source-square : Cone (F.u ∘ Cone.left (pullbackCone f g)) Fib.left-family intermediate
  source-square = coneSwap SourcePaste.composite
  opaque
    source-square-isPullback : IsPullback source-square
    source-square-isPullback = pullback-swap SourcePaste.composite
      (SourcePaste.composite-isPullback (pullback-swap A (pullbackCone-isPullback F.u Fib.left-family))
        Source.square-isPullback)


  source-square-matching : Cone.match source-square =₂
    (Cone.match (conePre (Cone.left intermediate-cone) A) ∙
      ((F.u ◁ ConeIso.leftIso source-computation) ∙
        comp-assoc to-source (Cone.left (pullbackCone f g)) F.u))
  source-square-matching = isoComp-cong swapped-first
    (isoComp-cong (postWhisker F.u ◁ inverse-inverse (ConeIso.leftIso source-computation)) (idIso _)) ∙
      inverse-inverse _
    where
    l = Cone.left intermediate-cone
    swapped-first : Cone.match (conePre l (coneSwap (coneSwap A))) =₂ Cone.match (conePre l A)
    swapped-first = isoComp-cong (idIso _)
      (isoComp-cong (preWhisker l ◁ inverse-inverse (Cone.match A)) (idIso _))

  section-image-comparison : ConeIso (compositeCone Fib.left-family f′ (coneSwap section-cone)) Fib.family
  section-image-comparison = record
    { leftIso = comp-unitʳ Fib.left-family ; rightIso = idIso Fib.right-family
    ; compatible = isoComp-cong ((postWhisker-idIso g′ Fib.right-family) ⁻¹) (idIso _)
        ∙ ((isoComp-unitˡ-at _) ⁻¹ ∙ calculation ⁻¹) }
    where
    A₀ = comp-assoc (id Γ) Fib.left-family f′
    U = comp-unitʳ Fib.base-family
    L₀ = f′ ◁ comp-unitʳ Fib.left-family
    inverse-matching : ((Cone.match section-cone) ⁻¹) =₂ (Fib.matching ∙ U)
    inverse-matching = isoComp-cong (inverse-inverse Fib.matching) (inverse-inverse U) ∙
      inverse-composite (U ⁻¹) (Fib.matching ⁻¹)
    calculation : Cone.match (compositeCone Fib.left-family f′ (coneSwap section-cone)) =₂
      (Fib.matching ∙ L₀)
    calculation = isoComp-cong (idIso Fib.matching)
      (cancel-right A₀ L₀ ∙ isoComp-cong (right-unitor-comp Fib.left-family f′) (idIso (A₀ ⁻¹))) ∙
      (isoComp-assoc-at Fib.matching U (A₀ ⁻¹) ∙ isoComp-cong inverse-matching (idIso (A₀ ⁻¹)))

  section-total-comparison : ConeIso (conePre (to-target ∘ section) target) (conePre x target)
  section-total-comparison = coneIso-compose section-image-comparison
    (coneIso-compose (compositeConeIso Fib.left-family f′ (coneIso-swap section-computation))
      (coneIso-compose (compositeConeIso Fib.left-family f′ (coneSwap-pre section target-leg-cone))
        (coneIso-compose (compositeCone-pre Fib.left-family f′ section (coneSwap target-leg-cone))
          (coneIso-compose (coneIso-pre section target-computation)
            (coneIso-inverse (conePre-assoc section to-target target))))))

  section-identification : (to-target ∘ section) =₁ x
  section-identification = pullback-reflect _ _ section-total-comparison


  private
    module SectionLift = Lifting.Lift 𝒯 P (to-target ∘ section) x section-total-comparison
      using (left-image; right-image; comparison-image)
  open SectionLift public using () renaming
    (left-image to section-left-image; right-image to section-right-image;
     comparison-image to section-comparison-image)
```
