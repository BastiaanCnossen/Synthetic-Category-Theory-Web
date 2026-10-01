# Cancelling composition by an inverse

Compose twice, reassociate, use the given inverse triangle, and remove
the identity arrow. Every step keeps the source matching, which gives
a comparison of whole cones over the parameter category.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section03.CompositionCalculus.SourceCompositionInverse
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionParameterChanges 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q using (associativity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as Identity
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.SourceCompositionCones as Actions

module Inverse {B C : CAT} {x y : MAP B C}
  (f : MorphismExpression y x) (g : MorphismExpression x y)
  (law : ExpressionIso (compose-expression g f) (identity-expression x)) where
  private
    module F = Actions.Action 𝒯 M ℱ P I E S f
      using (act; input)
    module G = Actions.Action 𝒯 M ℱ P I E S g
      using (act; composite; input)

  module At {Γ : CAT} (t : Cone (ev₀ {C}) x Γ) where
    private
      q = Cone.right t
      u = F.input t
      fq = restrict-expression f q
      gq = restrict-expression g q
      fg = compose-expression fq u
      module FG = MorphismExpression fg
        using (arrow; source-frame; target-frame)
      w = G.composite (F.act t)

      input-comparison : ExpressionIso
        (retarget-expression (G.input (F.act t)) (idIso (y ∘ q)) FG.target-frame) fg
      input-comparison = record { comparison = idIso FG.arrow
        ; target-compatible = (isoComp-unitʳ-at FG.target-frame) ⁻¹ ∙
            isoComp-unitʳ-at FG.target-frame ∙
            isoComp-cong (idIso FG.target-frame) (postWhisker-idIso ev₁ FG.arrow)
        ; source-compatible = (isoComp-unitˡ-at FG.source-frame) ⁻¹ ∙
            isoComp-unitʳ-at FG.source-frame ∙
            isoComp-cong (idIso FG.source-frame) (postWhisker-idIso ev₀ FG.arrow) }

      first : ExpressionIso
        (retarget-expression w (idIso (x ∘ q)) FG.target-frame) (compose-expression gq fg)
      first = composition-square gq (G.input (F.act t)) gq fg
        (idIso (x ∘ q)) (idIso (y ∘ q)) FG.target-frame
        (retarget-id gq) input-comparison

      restricted-law : ExpressionIso (compose-expression gq fq) (identity-expression (x ∘ q))
      restricted-law = expressionIso-compose (Identity.Restrict.comparison 𝒯 M ℱ P I E x q)
        (expressionIso-compose (restrict-expressionIso law q) (restrict-composition g f q))

      reassociate : ExpressionIso (compose-expression gq fg)
        (compose-expression (compose-expression gq fq) u)
      reassociate = associativity gq fq u

      cancel : ExpressionIso (compose-expression (compose-expression gq fq) u) u
      cancel = expressionIso-compose (left-unit u)
        (compose-expression-cong restricted-law (expressionIso-id u))

      value : ExpressionIso (retarget-expression w (idIso (x ∘ q)) FG.target-frame) u
      value = expressionIso-compose cancel (expressionIso-compose reassociate first)

    comparison : ConeIso (G.act (F.act t)) t
    comparison = record { leftIso = ExpressionIso.comparison value ; rightIso = idIso q
      ; compatible = isoComp-cong ((postWhisker-idIso x q) ⁻¹)
          (idIso (MorphismExpression.source-frame w)) ∙ ExpressionIso.source-compatible value }

  inverse-law : {Γ : CAT} (t : Cone (ev₀ {C}) x Γ) → ConeIso (G.act (F.act t)) t
  inverse-law = At.comparison
```
