# The section square after base change

The chosen pullback section commutes with the original section as a
relative functor. Associativity of relative composition transports that
square to the two section composites. The normalization of the postbased
composite uses the already proved projection-square pasting calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.BaseChangeSectionComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered; right-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as ProjectionSquaresLibrary
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames as Frames
import SCT.VolumeI.Chapter01.Section06.SectionBaseChange as Sections

module At {C D D′ T : CAT} (p : MAP C D) (s : MAP D C)
  (ρ : (p ∘ s) =₁ id D) (v : MAP D′ D) (t : Cone p v T) (et : IsPullback t) where
  module Changed = Sections.At 𝒯 P p s ρ v t et
    using (section; original-section; section-identification; compatible; section-cone)
  module PS = ProjectionSquaresLibrary 𝒯 using (lift-base; lift-compose)
  u = Cone.left t
  q = Cone.right t
  ω = Cone.match t
  j = Changed.section
  κ = Changed.original-section
  ρ′ = Changed.section-identification
  module OldFrames = Frames.WithSection 𝒯 p s ρ using (vertical-frame)
  module NewFrames = Frames.WithSection 𝒯 q j ρ′ using (vertical-frame)

  SectionMap : FunctorOver (id D) p
  SectionMap = record { lift = s ; comparison = ρ }
  Projection : FunctorOver p (id D)
  Projection = record { lift = p ; comparison = comp-unitˡ p }
  V : FunctorOver v (id D)
  V = record { lift = v ; comparison = comp-unitˡ v }
  U : FunctorOver (v ∘ q) p
  U = record { lift = u ; comparison = ω }
  Q₀ : FunctorOver (v ∘ q) v
  Q₀ = record { lift = q ; comparison = idIso (v ∘ q) }
  J : FunctorOver v (v ∘ q)
  J = record { lift = j ; comparison = comp-unitʳ v ∙ PS.lift-base v q j ρ′ }
  old-composite : FunctorOver p p
  old-composite = record { lift = s ∘ p ; comparison = OldFrames.vertical-frame }
  new-composite : FunctorOver q q
  new-composite = record { lift = j ∘ q ; comparison = NewFrames.vertical-frame }

  abstract
    old-normalization : FunctorOverIso old-composite (compose-over SectionMap Projection)
    old-normalization = triangle-identification _ _ _
      (isoComp-assoc-at (comp-unitˡ p) (ρ ▷ p) ((comp-assoc p s p) ⁻¹))

    section-square-compatible :
      (FunctorLift.comparison (compose-over SectionMap V) ∙ (p ◁ κ)) =₂
      FunctorLift.comparison (compose-over U J)
    section-square-compatible =
      isoComp-assoc-at (comp-unitʳ v) ((v ◁ ρ′) ∙ comp-assoc j q v)
        ((ω ▷ j) ∙ (comp-assoc j u p) ⁻¹) ⁻¹ ∙
      (isoComp-cong (idIso (comp-unitʳ v))
        (isoComp-assoc-at (v ◁ ρ′) (comp-assoc j q v) ((ω ▷ j) ∙ (comp-assoc j u p) ⁻¹) ⁻¹) ∙
      (isoComp-cong (idIso (comp-unitʳ v)) Changed.compatible ∙
      (isoComp-assoc-at (comp-unitʳ v) (Cone.match Changed.section-cone) (p ◁ κ) ∙
        isoComp-cong
          (cancel-inverse (comp-unitʳ v) (FunctorLift.comparison (compose-over SectionMap V)) ⁻¹)
          (idIso (p ◁ κ)))))

    section-square : FunctorOverIso (compose-over U J) (compose-over SectionMap V)
    section-square = record { underlying = κ ; compatible = section-square-compatible }

  private
    abstract
      unit-tail : {X Y Z : CAT} (h : MAP X Y) (k : MAP Y Z) →
        ((comp-unitˡ k ▷ h) ∙ (comp-assoc h k (id Z)) ⁻¹) =₂ comp-unitˡ (k ∘ h)
      unit-tail h k = cancel-right (comp-assoc h k _) (comp-unitˡ (k ∘ h)) ∙
        isoComp-cong (left-unitor-comp h k ⁻¹) (idIso ((comp-assoc h k _) ⁻¹))
      projection-normal : FunctorLift.comparison (compose-over Projection U) =₂ (ω ∙ comp-unitˡ (p ∘ u))
      projection-normal = isoComp-cong (idIso ω) (unit-tail u p)
      base-normal : FunctorLift.comparison (compose-over V Q₀) =₂ comp-unitˡ (v ∘ q)
      base-normal = unit-tail q v ∙ isoComp-unitˡ-at _

  abstract
    base-square : FunctorOverIso (compose-over Projection U) (compose-over V Q₀)
    base-square = record { underlying = ω
      ; compatible = projection-normal ⁻¹ ∙
          (postWhisker-id-at ω ∙ isoComp-cong base-normal (idIso (id D ◁ ω))) }

    postbase-normalization : FunctorLift.comparison (compose-over J Q₀) =₂
      FunctorLift.comparison (postbase v new-composite)
    postbase-normalization =
      isoComp-cong
        (postWhisker v ◁ (isoComp-assoc-at (comp-unitˡ q) (ρ′ ▷ q) ((comp-assoc q j q) ⁻¹) ⁻¹))
        (idIso (comp-assoc (j ∘ q) q v)) ∙
      (PS.lift-compose v q j q ρ′ (comp-unitˡ q) ∙
      (isoComp-cong (triangle-whiskered q v)
        (idIso ((PS.lift-base v q j ρ′ ▷ q) ∙ (comp-assoc q j (v ∘ q)) ⁻¹)) ∙
      (isoComp-assoc-at (comp-unitʳ v ▷ q) (PS.lift-base v q j ρ′ ▷ q)
        ((comp-assoc q j (v ∘ q)) ⁻¹) ∙
      (isoComp-cong (preWhisker-isoComp-at (comp-unitʳ v) (PS.lift-base v q j ρ′) q)
        (idIso ((comp-assoc q j (v ∘ q)) ⁻¹)) ∙ isoComp-unitˡ-at _))))

    normalized-square : FunctorOverIso (compose-over J Q₀) (postbase v new-composite)
    normalized-square = triangle-identification _ _ _ postbase-normalization

    source : FunctorOverIso (compose-over old-composite U) (compose-over U (postbase v new-composite))
    source = compose-iso-over (postwhisker-over U normalized-square)
      (compose-iso-over (associator-over Q₀ J U)
      (compose-iso-over (prewhisker-over Q₀ (inverse-iso-over section-square))
      (compose-iso-over (inverse-iso-over (associator-over Q₀ V SectionMap))
      (compose-iso-over (postwhisker-over SectionMap base-square)
      (compose-iso-over (associator-over U Projection SectionMap)
        (prewhisker-over U old-normalization))))))

    target : FunctorOverIso (compose-over (identity-over p) U)
      (compose-over U (postbase v (identity-over q)))
    target = compose-iso-over
      (postwhisker-over U (triangle-identification _ _ _ (right-unitor-comp q v)))
      (compose-iso-over (inverse-iso-over (right-unit-over U)) (left-unit-over U))
```
