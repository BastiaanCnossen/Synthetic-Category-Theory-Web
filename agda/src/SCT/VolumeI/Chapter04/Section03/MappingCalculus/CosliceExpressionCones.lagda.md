# Complete coslice cones from normalized arrow computations

A computation of the normalized universal arrow, together with its
specified target comparison, determines a comparison of endpoint cones.
The reconstruction retains both projections of that same comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I using (Coslice; coslice-projection)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Encoding
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-natural)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-cancel-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P using (pullbackCone)

module At {C : CAT} (x : Obj-abs C) where
  private
    module H = EndpointFiber (const {P = C} x) (id C)
    module Read = Reading.At 𝒯 M ℱ P I x using (read; module Read)
    module Lift = Lifting.At 𝒯 M ℱ P I x using (frame; module Change)
    module Encode = Encoding.Lifts 𝒯 M ℱ P I (const {P = C} x) (id C) using (encode-cong)
    module Decode = Fiber (const {P = C} x) (id C) using (encode-decode; read; decode-comparison; decode-encode)

  module Along {Γ : CAT} (h : MAP Γ (Coslice C x)) (q : MAP Γ C)
    (V : MorphismExpression (const x) q) (σ : (coslice-projection x ∘ h) =₁ q)
    (Φ : ExpressionIso (retarget-expression (Read.read h) (idIso (const x)) σ) V) where
    private
      module Changed = Lift.Change (Read.read h) V σ Φ using (cone-comparison)
      reconstructed : ConeIso (H.cone (H.base ∘ h) (Lift.frame (Read.read h)))
        (H.cone (H.base ∘ h) (Decode.read h))
      reconstructed = Encode.encode-cong (H.base ∘ h) (Read.Read.reconstruction-expression h)

    abstract
      comparison : ConeIso (conePre h (pullbackCone endpoints (pair (const x) (id C))))
        (H.cone q (Lift.frame V))
      comparison = coneIso-compose Changed.cone-comparison
        (coneIso-compose (coneIso-inverse reconstructed)
          (Decode.encode-decode (conePre h (pullbackCone endpoints (pair (const x) (id C))))))

  module FromCone {Γ : CAT} (h : MAP Γ (Coslice C x)) (q : MAP Γ C)
    (V : MorphismExpression (const x) q)
    (Φ : ConeIso (conePre h (pullbackCone endpoints (pair (const x) (id C))))
      (H.cone q (Lift.frame V))) where
    projection : (coslice-projection x ∘ h) =₁ q
    projection = ConeIso.rightIso Φ
    private
      a₀ = H.base ∘ h
      p = const-pre x a₀
      u = comp-unitˡ a₀
      p′ = const-pre x q
      u′ = comp-unitˡ q
      σ = projection
      d = Decode.read h
      s = const {P = C} x ◁ σ
      t = id C ◁ σ
      abstract
        decoded : ExpressionIso (retarget-expression d s t) (Lift.frame V)
        decoded = expressionIso-compose (Decode.decode-encode q (Lift.frame V)) (Decode.decode-comparison Φ)
        source-square : (idIso (const x) ∙ p) =₂ (p′ ∙ s)
        source-square = (const-pre-natural x σ) ⁻¹ ∙ isoComp-unitˡ-at p
        target-square : (σ ∙ u) =₂ (u′ ∙ t)
        target-square = (postWhisker-id-at σ) ⁻¹

    abstract
      comparison : ExpressionIso (retarget-expression (Read.read h) (idIso (const x)) projection) V
      comparison = expressionIso-compose (retarget-cancel-inverse V p′ u′)
        (expressionIso-compose (retarget-expressionIso decoded p′ u′)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc d s t p′ u′))
        (expressionIso-compose (retarget-cong d source-square target-square)
        (expressionIso-compose (retarget-assoc d p u (idIso (const x)) σ)
          (retarget-expressionIso (expressionIso-inverse (Read.Read.comparison h)) (idIso (const x)) σ)))))
```
