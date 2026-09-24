# Postcomposition of an evaluated square

Applying a functor to an evaluated square agrees with evaluating the
square by the composite functor. The displayed associators compare the
two parenthesizations on both sides.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section04.SquareEvaluationPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareEvaluation 𝒯 M using (evaluate-square)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (lift-base; post-inverse)
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (lift-assoc)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)

module At {X Y K L C D : CAT} (e : MAP L C) (F : MAP C D)
  (r : MAP X Y) (R : MAP K L) (i : MAP X K) (j : MAP Y L)
  (α : (j ∘ r) =₁ (R ∘ i)) where
  B = lift-base e j r α
  B′ = lift-base (F ∘ e) j r α
  A = comp-assoc (R ∘ i) e F
  U = comp-assoc i R e
  V = comp-assoc i (e ∘ R) F
  W = comp-assoc R e F ▷ i
  Z = comp-assoc i R (F ∘ e)
  J₀ = comp-assoc r (e ∘ j) F
  J₁ = comp-assoc j e F ▷ r
  J = J₀ ∙ J₁
  E = evaluate-square e r R i j α
  E′ = evaluate-square (F ∘ e) r R i j α

  abstract
    lifted : ((F ◁ B) ∙ J) =₂ (A ∙ B′)
    lifted = (lift-assoc j (R ∘ i) r α e F) ⁻¹ ∙
      (isoComp-assoc-at (F ◁ B) J₀ J₁) ⁻¹

    pentagon : ((F ◁ U) ⁻¹ ∙ A) =₂ ((V ∙ W) ∙ Z ⁻¹)
    pentagon = move-square (F ◁ U) (V ∙ W) A Z ((pentagon-whiskered i R e F) ⁻¹)

    comparison : ((F ◁ E) ∙ J) =₂ ((V ∙ W) ∙ E′)
    comparison = isoComp-assoc-at (V ∙ W) (Z ⁻¹) B′ ∙
      isoComp-cong pentagon (idIso B′) ∙
      (isoComp-assoc-at ((F ◁ U) ⁻¹) A B′) ⁻¹ ∙
      isoComp-cong (idIso ((F ◁ U) ⁻¹)) lifted ∙
      isoComp-assoc-at ((F ◁ U) ⁻¹) (F ◁ B) J ∙
      isoComp-cong (isoComp-cong (post-inverse F U) (idIso (F ◁ B)) ∙
        postWhisker-isoComp-at F (U ⁻¹) B) (idIso J)
```
