# Currying comparisons with specified endpoints

Currying respects identifications of framed transformations. The proof
retains the restriction square for each endpoint through both currying
operations. In particular, it does not replace endpoint compatibility by
an identification of the underlying diagrams alone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressionComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β; funReflect-Iso₂)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedExpressionComparisons as Uncurried
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)

private
  paste : {Y Z : CAT} {h₀ h₁ k₀ k₁ t : MAP Y Z}
    (u : h₀ =₁ k₀) (v : h₁ =₁ k₁) (p : h₀ =₁ h₁) (q : k₀ =₁ k₁)
    (r : h₁ =₁ t) (s : k₁ =₁ t) →
    (s ∙ v) =₂ r → (q ∙ u) =₂ (v ∙ p) →
    ((s ∙ q) ∙ u) =₂ (r ∙ p)
  paste u v p q r s upper lower =
    isoComp-cong upper (idIso p) ∙
    (isoComp-assoc-at s v p) ⁻¹ ∙
    isoComp-cong (idIso s) lower ∙ isoComp-assoc-at s q u

  reassociate : {Y Z : CAT} {h₀ h₁ h₂ h₃ h₄ h₅ : MAP Y Z}
    (v : h₄ =₁ h₅) (w : h₃ =₁ h₄) (x : h₂ =₁ h₃)
    (y : h₁ =₁ h₂) (z : h₀ =₁ h₁) →
    (v ∙ (w ∙ (x ∙ (y ∙ z)))) =₂ ((((v ∙ w) ∙ x) ∙ y) ∙ z)
  reassociate v w x y z =
    (isoComp-assoc-at ((v ∙ w) ∙ x) y z) ⁻¹ ∙
    (isoComp-assoc-at (v ∙ w) x (y ∙ z)) ⁻¹ ∙
    (isoComp-assoc-at v w (x ∙ (y ∙ z))) ⁻¹

module At {Γ X C : CAT} (f g : MAP Γ (Fun X C))
  {α β : MorphismExpression (funUncurry f) (funUncurry g)} (ξ : ExpressionIso α β) where
  module A = Currying.Curry 𝒯 M ℱ I f g α
  module B = Currying.Curry 𝒯 M ℱ I f g β
  module U = Uncurried.UncurryComparison 𝒯 M ℱ P I E ξ
  δ = U.underlying
  δ-diagram = δ ▷ A.permutation
  bA = funCurry-β A.diagram
  bB = funCurry-β B.diagram
  lifted = funIsoReflect A.first-curry B.first-curry (bB ⁻¹ ∙ (δ-diagram ∙ bA))

  abstract
    lifted-square : (bB ∙ funUncurryIso lifted) =₂ (δ-diagram ∙ bA)
    lifted-square = cancel-inverse bB (δ-diagram ∙ bA) ∙
      isoComp-cong (idIso bB) (funIsoReflect-β A.first-curry B.first-curry (bB ⁻¹ ∙ (δ-diagram ∙ bA)))

  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (p : (evaluate z ∘ MorphismExpression.arrow α) =₁ funUncurry h)
    (q : (evaluate z ∘ MorphismExpression.arrow β) =₁ funUncurry h)
    (compatible : (q ∙ (evaluate z ◁ ExpressionIso.comparison ξ)) =₂ p) where
    module AE = A.Endpoint z h p
    module BE = B.Endpoint z h q
    i = insert {X = Γ} z
    j = insert {X = Γ × X} z
    step = AE.step
    κ = AE.insertion-comparison
    frontA = p ∙ (evaluate-uncurry z (MorphismExpression.arrow α)) ⁻¹
    frontB = q ∙ (evaluate-uncurry z (MorphismExpression.arrow β)) ⁻¹
    tA = A.original ◁ κ
    tB = B.original ◁ κ
    aA = comp-assoc step A.permutation A.original
    aB = comp-assoc step B.permutation B.original
    rA = funUncurry-restrict A.first-curry i
    rB = funUncurry-restrict B.first-curry i

    abstract
      front-square : (frontB ∙ (δ ▷ j)) =₂ frontA
      front-square = U.Endpoint.comparison z p q compatible

      coordinate-square : ((frontB ∙ tB) ∙ (δ ▷ (A.permutation ∘ step))) =₂ (frontA ∙ tA)
      coordinate-square = paste _ _ tA tB frontA frontB front-square ((interchange-at δ κ) ⁻¹)

      diagram-square : (((frontB ∙ tB) ∙ aB) ∙ (δ-diagram ▷ step)) =₂ ((frontA ∙ tA) ∙ aA)
      diagram-square = paste _ _ aA aB _ _ coordinate-square (preWhisker-comp-at δ A.permutation step)

      beta-square : ((((frontB ∙ tB) ∙ aB) ∙ (bB ▷ step)) ∙ (funUncurryIso lifted ▷ step)) =₂
        (((frontA ∙ tA) ∙ aA) ∙ (bA ▷ step))
      beta-square = paste _ _ (bA ▷ step) (bB ▷ step) _ _ diagram-square
        (preWhisker-isoComp-at δ-diagram bA step ∙
          (preWhisker step ◁ lifted-square) ∙
          (preWhisker-isoComp-at bB (funUncurryIso lifted) step) ⁻¹)

      raw-square : (BE.raw ∙ funUncurryIso (lifted ▷ i)) =₂ AE.raw
      raw-square = (reassociate frontA tA aA (bA ▷ step) rA) ⁻¹ ∙
        paste _ _ rA rB _ _ beta-square (funUncurry-restrict-inputs lifted i) ∙
        isoComp-cong (reassociate frontB tB aB (bB ▷ step) rB) (idIso (funUncurryIso (lifted ▷ i)))

      comparison : (BE.reflected ∙ (lifted ▷ i)) =₂ AE.reflected
      comparison = funReflect-Iso₂ _ _
        ((AE.reflected-image) ⁻¹ ∙ raw-square ∙
          isoComp-cong BE.reflected-image (idIso (funUncurryIso (lifted ▷ i))) ∙
          funUncurryIso-comp BE.reflected (lifted ▷ i))

  value : ExpressionIso A.value B.value
  value = Diagrams.At.comparison 𝒯 M ℱ P I E A.first-curry B.first-curry lifted
    A.Source.reflected A.Target.reflected B.Source.reflected B.Target.reflected
    (Endpoint.comparison zero f (MorphismExpression.source-frame α) (MorphismExpression.source-frame β)
      (ExpressionIso.source-compatible ξ))
    (Endpoint.comparison one g (MorphismExpression.target-frame α) (MorphismExpression.target-frame β)
      (ExpressionIso.target-compatible ξ))
```
