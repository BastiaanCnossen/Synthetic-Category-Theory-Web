# Cancelling composition by an inverse

Compose twice, reassociate, use the given inverse triangle, and remove
the identity arrow. Every step keeps the target matching, which gives
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

module SCT.VolumeI.Chapter02.Section03.CompositionCalculus.TargetCompositionInverse
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
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (right-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as Identity
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.TargetCompositionCones as Actions

module Inverse {B C : CAT} {x y : MAP B C}
  (f : MorphismExpression x y) (g : MorphismExpression y x)
  (law : ExpressionIso (compose-expression f g) (identity-expression x)) where
  private
    module F = Actions.Action 𝒯 M ℱ P I E S f
    module G = Actions.Action 𝒯 M ℱ P I E S g

  module At {Γ : CAT} (t : Cone (ev₁ {C}) x Γ) where
    private
      q = Cone.right t
      u = F.input t
      fq = restrict-expression f q
      gq = restrict-expression g q
      fg = compose-expression u fq
      module FG = MorphismExpression fg
      w = G.composite (F.act t)

      input-comparison : ExpressionIso
        (retarget-expression (G.input (F.act t)) FG.source-frame (idIso (y ∘ q))) fg
      input-comparison = record { comparison = idIso FG.arrow
        ; source-compatible = (isoComp-unitʳ-at FG.source-frame) ⁻¹ ∙
            isoComp-unitʳ-at FG.source-frame ∙
            isoComp-cong (idIso FG.source-frame) (postWhisker-idIso ev₀ FG.arrow)
        ; target-compatible = (isoComp-unitˡ-at FG.target-frame) ⁻¹ ∙
            isoComp-unitʳ-at FG.target-frame ∙
            isoComp-cong (idIso FG.target-frame) (postWhisker-idIso ev₁ FG.arrow) }

      first : ExpressionIso
        (retarget-expression w FG.source-frame (idIso (x ∘ q))) (compose-expression fg gq)
      first = composition-square (G.input (F.act t)) gq fg gq
        FG.source-frame (idIso (y ∘ q)) (idIso (x ∘ q))
        input-comparison (retarget-id gq)

      restricted-law : ExpressionIso (compose-expression fq gq) (identity-expression (x ∘ q))
      restricted-law = expressionIso-compose (Identity.Restrict.comparison 𝒯 M ℱ P I E x q)
        (expressionIso-compose (restrict-expressionIso law q) (restrict-composition f g q))

      reassociate : ExpressionIso (compose-expression fg gq)
        (compose-expression u (compose-expression fq gq))
      reassociate = expressionIso-inverse (associativity u fq gq)

      cancel : ExpressionIso (compose-expression u (compose-expression fq gq)) u
      cancel = expressionIso-compose (right-unit u)
        (compose-expression-cong (expressionIso-id u) restricted-law)

      value : ExpressionIso (retarget-expression w FG.source-frame (idIso (x ∘ q))) u
      value = expressionIso-compose cancel (expressionIso-compose reassociate first)

    comparison : ConeIso (G.act (F.act t)) t
    comparison = record { leftIso = ExpressionIso.comparison value ; rightIso = idIso q
      ; compatible = isoComp-cong ((postWhisker-idIso x q) ⁻¹)
          (idIso (MorphismExpression.target-frame w)) ∙ ExpressionIso.target-compatible value }

  inverse-law : {Γ : CAT} (t : Cone (ev₁ {C}) x Γ) → ConeIso (G.act (F.act t)) t
  inverse-law = At.comparison
```
