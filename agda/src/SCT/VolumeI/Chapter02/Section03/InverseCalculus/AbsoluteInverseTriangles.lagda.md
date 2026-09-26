# Inverse witnesses from triangles with constant long edge

Move the constant long edge to the displayed endpoint of the given
morphism. The other corners then determine the endpoint frames of its
inverse. Constant-boundary naturality verifies the remaining corner.
This construction needs neither Segal nor Rezk.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.AbsoluteInverseTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.VertexTransport 𝒯 M ℱ P I E
  using (module ConstantBoundary)
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DegenerateCocones 𝒯 M ℱ P I E
  using (triangle-edges; triangle-source; upper-edges)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

vertex-equation : {C : CAT} {u v p q z : Obj-abs C}
  (α : p =₁ z) (β : q =₁ z) (L : u =₁ p) (R : v =₁ q) (δ : u =₁ v) →
  (α ∙ L) =₂ (β ∙ (R ∙ δ)) → ((β ⁻¹ ∙ α) ∙ L) =₂ (R ∙ δ)
vertex-equation α β L R δ ε = cancel-left β (R ∙ δ) ∙
  (isoComp-cong (idIso (β ⁻¹)) ε ∙ isoComp-assoc-at (β ⁻¹) α L)

module MoveConstant {C : CAT} {h : Mor C} {z y : Obj-abs C}
  (long : h =₁ const z) (ρ : z =₁ y) where
  comparison : h =₁ const y
  comparison = (ρ ▷ terminate [1]) ∙ long

  endpoint : (i : Obj-abs [1]) →
    (constant-boundary i y ∙ (comparison ▷ i)) =₂
      (ρ ∙ (constant-boundary i z ∙ (long ▷ i)))
  endpoint i = isoComp-assoc-at ρ (constant-boundary i z) (long ▷ i) ∙
    (isoComp-cong (ConstantBoundary.natural ρ i) (idIso (long ▷ i)) ∙
      ((isoComp-assoc-at (constant-boundary i y) ((ρ ▷ terminate [1]) ▷ i) (long ▷ i)) ⁻¹ ∙
        isoComp-cong (idIso (constant-boundary i y))
          (preWhisker-isoComp-at (ρ ▷ terminate [1]) long i)))

module Right {C : CAT} {x y z : Obj-abs C} (f : Morphism x y)
  (σ : Triangle C) (β : (σ ∘ d₀) =₁ Morphism.diagram f)
  (long : (σ ∘ d₁) =₁ const z) where
  private
    module F = Morphism f
    middle = Cocone.match (coconePost σ triangle-edges)
    source-corner = Cocone.match (coconePost σ triangle-source)
    target-corner = Cocone.match (coconePost σ upper-edges)
    target-value = (F.target-identification ∙ (β ▷ one)) ∙ target-corner ⁻¹
    long-target = constant-boundary one z ∙ (long ▷ one)
    module Moved = MoveConstant long (target-value ∙ long-target ⁻¹)
    source-value = constant-boundary zero y ∙ (Moved.comparison ▷ zero)
    inverse-source = source-value ∙ source-corner ⁻¹
    inverse-target = F.source-identification ∙ ((β ▷ zero) ∙ middle)

  inverse : Morphism y x
  inverse = record { diagram = σ ∘ d₂
    ; source-identification = inverse-source ; target-identification = inverse-target }

  private
    middle-equation : (inverse-target ∙ (idIso (σ ∘ d₂) ▷ one)) =₂
      (F.source-identification ∙ ((β ▷ zero) ∙ middle))
    middle-equation = isoComp-unitʳ-at inverse-target ∙
      isoComp-cong (idIso inverse-target) (preWhisker-idIso (σ ∘ d₂) one)

    source-equation : (constant-boundary zero y ∙ (Moved.comparison ▷ zero)) =₂
      (inverse-source ∙ ((idIso (σ ∘ d₂) ▷ zero) ∙ source-corner))
    source-equation = (cancel-inverse-tail source-value source-corner ∙
      isoComp-cong (idIso inverse-source) (isoComp-unitˡ-at source-corner ∙
        isoComp-cong (preWhisker-idIso (σ ∘ d₂) zero) (idIso source-corner))) ⁻¹

    moved-target : (constant-boundary one y ∙ (Moved.comparison ▷ one)) =₂ target-value
    moved-target = cancel-inverse-tail target-value long-target ∙ Moved.endpoint one

    target-equation : (F.target-identification ∙ (β ▷ one)) =₂
      (constant-boundary one y ∙ ((Moved.comparison ▷ one) ∙ target-corner))
    target-equation = (cancel-inverse-tail (F.target-identification ∙ (β ▷ one)) target-corner ∙
      (isoComp-cong moved-target (idIso target-corner) ∙
        (isoComp-assoc-at (constant-boundary one y) (Moved.comparison ▷ one) target-corner) ⁻¹)) ⁻¹

  witness : CompositeWitness inverse f (identity-morphism y)
  witness = record
    { triangle = σ ; first-edge = idIso (σ ∘ d₂) ; second-edge = β ; long-edge = Moved.comparison
    ; middle-vertex = vertex-equation inverse-target F.source-identification _ _ middle middle-equation
    ; source-vertex = vertex-equation (constant-boundary zero y) inverse-source _ _ source-corner source-equation
    ; target-vertex = vertex-equation F.target-identification (constant-boundary one y) _ _ target-corner target-equation }

module Left {C : CAT} {x y z : Obj-abs C} (f : Morphism x y)
  (σ : Triangle C) (α : (σ ∘ d₂) =₁ Morphism.diagram f)
  (long : (σ ∘ d₁) =₁ const z) where
  private
    module F = Morphism f
    middle = Cocone.match (coconePost σ triangle-edges)
    source-corner = Cocone.match (coconePost σ triangle-source)
    target-corner = Cocone.match (coconePost σ upper-edges)
    source-value = (F.source-identification ∙ (α ▷ zero)) ∙ source-corner
    long-source = constant-boundary zero z ∙ (long ▷ zero)
    module Moved = MoveConstant long (source-value ∙ long-source ⁻¹)
    target-value = constant-boundary one x ∙ (Moved.comparison ▷ one)
    inverse-source = (F.target-identification ∙ (α ▷ one)) ∙ middle ⁻¹
    inverse-target = target-value ∙ target-corner

  inverse : Morphism y x
  inverse = record { diagram = σ ∘ d₀
    ; source-identification = inverse-source ; target-identification = inverse-target }

  private
    middle-equation : (F.target-identification ∙ (α ▷ one)) =₂
      (inverse-source ∙ ((idIso (σ ∘ d₀) ▷ zero) ∙ middle))
    middle-equation = (cancel-inverse-tail (F.target-identification ∙ (α ▷ one)) middle ∙
      isoComp-cong (idIso inverse-source) (isoComp-unitˡ-at middle ∙
        isoComp-cong (preWhisker-idIso (σ ∘ d₀) zero) (idIso middle))) ⁻¹

    source-equation : (constant-boundary zero x ∙ (Moved.comparison ▷ zero)) =₂
      (F.source-identification ∙ ((α ▷ zero) ∙ source-corner))
    source-equation = isoComp-assoc-at F.source-identification (α ▷ zero) source-corner ∙
      (cancel-inverse-tail source-value long-source ∙ Moved.endpoint zero)

    target-equation : (inverse-target ∙ (idIso (σ ∘ d₀) ▷ one)) =₂
      (constant-boundary one x ∙ ((Moved.comparison ▷ one) ∙ target-corner))
    target-equation = isoComp-assoc-at (constant-boundary one x) (Moved.comparison ▷ one) target-corner ∙
      (isoComp-unitʳ-at inverse-target ∙
        isoComp-cong (idIso inverse-target) (preWhisker-idIso (σ ∘ d₀) one))

  witness : CompositeWitness f inverse (identity-morphism x)
  witness = record
    { triangle = σ ; first-edge = α ; second-edge = idIso (σ ∘ d₀) ; long-edge = Moved.comparison
    ; middle-vertex = vertex-equation F.target-identification inverse-source _ _ middle middle-equation
    ; source-vertex = vertex-equation (constant-boundary zero x) F.source-identification _ _ source-corner source-equation
    ; target-vertex = vertex-equation inverse-target (constant-boundary one x) _ _ target-corner target-equation }
```
