# Inverse triangles with specified endpoints

A triangle whose long edge is constant gives a one-sided inverse. Move
the constant center to the specified endpoint of the given edge, and use
the other two corners to frame the inverse. Segal uniqueness then gives
the inverse equation with both endpoint identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.InverseTriangleExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I
  using (constant-frame; constant-frame-natural)
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison as Constant
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

constant-expression : {Γ C : CAT} (x : MAP Γ C) → MorphismExpression x x
constant-expression x = record
  { arrow = identityArrow ∘ x
  ; source-frame = constant-frame ev₀ identity-source x
  ; target-frame = constant-frame ev₁ identity-target x }

module MoveConstant {Γ C : CAT} {h : MAP Γ (Ar C)} {z y : MAP Γ C}
  (long : h =₁ (identityArrow ∘ z)) (ρ : z =₁ y) where
  comparison : h =₁ (identityArrow ∘ y)
  comparison = (identityArrow ◁ ρ) ∙ long

  endpoint : (v : MAP (Ar C) C) (b : (v ∘ identityArrow) =₁ (id C)) →
    (constant-frame v b y ∙ (v ◁ comparison)) =₂
      (ρ ∙ (constant-frame v b z ∙ (v ◁ long)))
  endpoint v b = isoComp-assoc-at ρ (constant-frame v b z) (v ◁ long) ∙
    isoComp-cong (constant-frame-natural v b ρ) (idIso (v ◁ long)) ∙
    (isoComp-assoc-at (constant-frame v b y) (v ◁ (identityArrow ◁ ρ)) (v ◁ long)) ⁻¹ ∙
    isoComp-cong (idIso (constant-frame v b y)) (postWhisker-isoComp-at v (identityArrow ◁ ρ) long)

module Right {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (σ : MAP Γ (Triangles C))
  (β : (edge₀ ∘ σ) =₁ MorphismExpression.arrow f)
  (long : (edge₁ ∘ σ) =₁ (identityArrow ∘ z)) where
  private
    module F = MorphismExpression f
    middle = Cone.match (conePre σ (triangle-cone C))
    source-corner = Cone.match (conePre σ (source-cone C))
    target-corner = Cone.match (conePre σ (target-cone C))
    t = F.target-frame ∙ ((ev₁ ◁ β) ∙ target-corner)
    l = constant-frame ev₁ identity-target z ∙ (ev₁ ◁ long)
    ρ = t ∙ l ⁻¹
    module Moved = MoveConstant long ρ
    u = constant-frame ev₀ identity-source y ∙ (ev₀ ◁ Moved.comparison)
    v = (ev₀ ◁ β) ∙ middle

  inverse-expression : MorphismExpression y x
  inverse-expression = record
    { arrow = edge₂ ∘ σ ; source-frame = u ∙ source-corner ⁻¹
    ; target-frame = F.source-frame ∙ v }

  private
    short-edges : ConeIso (conePre σ (triangle-cone C)) (expression-pair inverse-expression f)
    short-edges = record
      { leftIso = idIso (edge₂ ∘ σ) ; rightIso = β
      ; compatible = cancel-left F.source-frame v ∙
          isoComp-unitʳ-at (F.source-frame ⁻¹ ∙ (F.source-frame ∙ v)) ∙
          isoComp-cong (idIso (F.source-frame ⁻¹ ∙ (F.source-frame ∙ v)))
            (postWhisker-idIso ev₁ (edge₂ ∘ σ)) }

    source-equation :
      (constant-frame ev₀ identity-source y ∙ (ev₀ ◁ Moved.comparison)) =₂
      ((u ∙ source-corner ⁻¹) ∙ ((ev₀ ◁ idIso (edge₂ ∘ σ)) ∙ source-corner))
    source-equation = (cancel-inverse-tail u source-corner ∙
      isoComp-cong (idIso (u ∙ source-corner ⁻¹))
        (isoComp-unitˡ-at source-corner ∙ isoComp-cong (postWhisker-idIso ev₀ (edge₂ ∘ σ)) (idIso source-corner))) ⁻¹

    target-equation :
      (constant-frame ev₁ identity-target y ∙ (ev₁ ◁ Moved.comparison)) =₂ t
    target-equation = cancel-inverse-tail t l ∙ Moved.endpoint ev₁ identity-target

  presentation : CompositePresentation inverse-expression f (constant-expression y)
  presentation = record { triangle = σ ; short-edges = short-edges
    ; long-edge = record { comparison = Moved.comparison
      ; source-compatible = source-equation ; target-compatible = target-equation } }

  inverse-law : ExpressionIso (compose-expression inverse-expression f) (identity-expression y)
  inverse-law = expressionIso-compose (Constant.At.comparison 𝒯 M ℱ P I E y)
    (recognize-composite presentation)

module Left {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (σ : MAP Γ (Triangles C))
  (α : (edge₂ ∘ σ) =₁ MorphismExpression.arrow f)
  (long : (edge₁ ∘ σ) =₁ (identityArrow ∘ z)) where
  private
    module F = MorphismExpression f
    middle = Cone.match (conePre σ (triangle-cone C))
    source-corner = Cone.match (conePre σ (source-cone C))
    target-corner = Cone.match (conePre σ (target-cone C))
    s = F.source-frame ∙ ((ev₀ ◁ α) ∙ source-corner)
    l = constant-frame ev₀ identity-source z ∙ (ev₀ ◁ long)
    ρ = s ∙ l ⁻¹
    module Moved = MoveConstant long ρ
    u = constant-frame ev₁ identity-target x ∙ (ev₁ ◁ Moved.comparison)
    v = F.target-frame ∙ (ev₁ ◁ α)
    frame = v ∙ middle ⁻¹

  inverse-expression : MorphismExpression y x
  inverse-expression = record
    { arrow = edge₀ ∘ σ ; source-frame = frame
    ; target-frame = u ∙ target-corner ⁻¹ }

  private
    middle-equation : ((frame ⁻¹ ∙ F.target-frame) ∙ (ev₁ ◁ α)) =₂
      ((ev₀ ◁ idIso (edge₀ ∘ σ)) ∙ middle)
    middle-equation =
      (isoComp-unitˡ-at middle ∙ isoComp-cong (postWhisker-idIso ev₀ (edge₀ ∘ σ)) (idIso middle)) ⁻¹ ∙
      cancel-left frame middle ∙
      isoComp-cong (idIso (frame ⁻¹)) ((cancel-inverse-tail v middle) ⁻¹) ∙
      isoComp-assoc-at (frame ⁻¹) F.target-frame (ev₁ ◁ α)

    short-edges : ConeIso (conePre σ (triangle-cone C)) (expression-pair f inverse-expression)
    short-edges = record { leftIso = α ; rightIso = idIso (edge₀ ∘ σ)
      ; compatible = middle-equation }

    source-equation :
      (constant-frame ev₀ identity-source x ∙ (ev₀ ◁ Moved.comparison)) =₂ s
    source-equation = cancel-inverse-tail s l ∙ Moved.endpoint ev₀ identity-source

    target-equation :
      (constant-frame ev₁ identity-target x ∙ (ev₁ ◁ Moved.comparison)) =₂
      ((u ∙ target-corner ⁻¹) ∙ ((ev₁ ◁ idIso (edge₀ ∘ σ)) ∙ target-corner))
    target-equation = (cancel-inverse-tail u target-corner ∙
      isoComp-cong (idIso (u ∙ target-corner ⁻¹))
        (isoComp-unitˡ-at target-corner ∙ isoComp-cong (postWhisker-idIso ev₁ (edge₀ ∘ σ)) (idIso target-corner))) ⁻¹

  presentation : CompositePresentation f inverse-expression (constant-expression x)
  presentation = record { triangle = σ ; short-edges = short-edges
    ; long-edge = record { comparison = Moved.comparison
      ; source-compatible = source-equation ; target-compatible = target-equation } }

  inverse-law : ExpressionIso (compose-expression f inverse-expression) (identity-expression x)
  inverse-law = expressionIso-compose (Constant.At.comparison 𝒯 M ℱ P I E x)
    (recognize-composite presentation)
```
