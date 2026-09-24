# Cancelling a restricted comparison

This calculation cancels the same intermediate comparison before and
after substitution. Stating it for arbitrary comparisons keeps the
calculation independent of the construction that selected them.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section04.ComparisonCancellation
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-left-reflect)

abstract
  cancel-forward : {X Y : CAT} {a b c : MAP X Y}
    (W : b =₁ c) (V : a =₁ c)
    → (W ∙ (W ⁻¹ ∙ V)) =₂ V
  cancel-forward W V = isoComp-unitˡ-at V ∙
    (isoComp-cong (isoComp-inverseʳ-at W) (idIso V) ∙
      (isoComp-assoc-at W (W ⁻¹) V) ⁻¹)

  cancel-restricted-comparison : {R X Y : CAT} (s : MAP R X)
    {a b c : MAP X Y} {t z k l : MAP R Y}
    (W : b =₁ c) (V : a =₁ c)
    (A : (b ∘ s) =₁ t) (B : z =₁ (a ∘ s))
    (P′ : (c ∘ s) =₁ k) (N : k =₁ l)
    →
        ((N ∙ (P′ ∙ ((W ▷ s) ∙ A ⁻¹))) ∙
          (A ∙ (((W ⁻¹ ∙ V) ▷ s) ∙ B))) =₂
        (N ∙ (P′ ∙ ((V ▷ s) ∙ B)))
  cancel-restricted-comparison s W V A B P′ N =
    let restricted = (W ⁻¹ ∙ V) ▷ s
        tail = restricted ∙ B
        cancelA = isoComp-cong (idIso (W ▷ s)) (cancel-left A tail) ∙
          isoComp-assoc-at (W ▷ s) (A ⁻¹) (A ∙ tail)
        cancelW = isoComp-cong (preWhisker s ◁ cancel-forward W V) (idIso B) ∙
          (isoComp-cong ((preWhisker-isoComp-at W (W ⁻¹ ∙ V) s) ⁻¹) (idIso B) ∙
            (isoComp-assoc-at (W ▷ s) restricted B) ⁻¹)
        reassociate = isoComp-assoc-at N P′ ((W ▷ s) ∙ tail) ∙
          isoComp-cong (idIso (N ∙ P′)) cancelA
    in isoComp-cong (idIso N) (isoComp-cong (idIso P′) cancelW) ∙
      (reassociate ∙
        (isoComp-assoc-at (N ∙ P′) ((W ▷ s) ∙ A ⁻¹) (A ∙ tail) ∙
          isoComp-cong ((isoComp-assoc-at N P′ ((W ▷ s) ∙ A ⁻¹)) ⁻¹) (idIso (A ∙ tail))))
```

Two routes transported through fixed endpoint comparisons agree under
parameter change when the two endpoint squares and the middle square
agree. This formulation keeps the selected endpoint comparisons out of
the general cancellation proof.

```agda
opaque
  transport-route-square : {X Y : CAT}
    {aQ bQ cQ dQ aP bP cP dP : MAP X Y}
    (lQ : aQ =₁ bQ) (rQ : dQ =₁ cQ) (AQ : bQ =₁ cQ)
    (routeQ : aQ =₁ dQ)
    (lP : aP =₁ bP) (rP : dP =₁ cP) (AP : bP =₁ cP)
    (routeP : aP =₁ dP)
    (κleft : aQ =₁ aP) (κright : dQ =₁ dP)
    (KL : bQ =₁ bP) (KR : cQ =₁ cP)
    → (rQ ∙ routeQ) =₂ (AQ ∙ lQ)
    → (rP ∙ routeP) =₂ (AP ∙ lP)
    → (KL ∙ lQ) =₂ (lP ∙ κleft)
    → (KR ∙ rQ) =₂ (rP ∙ κright)
    → (AP ∙ KL) =₂ (KR ∙ AQ)
    → (κright ∙ routeQ) =₂ (routeP ∙ κleft)
  transport-route-square lQ rQ AQ routeQ lP rP AP routeP κleft κright KL KR
    qSquare pSquare leftSquare rightSquare middleSquare =
    cancel-left-reflect rP
      (isoComp-assoc-at rP routeP κleft ∙
      (isoComp-cong (pSquare ⁻¹) (idIso κleft) ∙
      ((isoComp-assoc-at AP lP κleft) ⁻¹ ∙
      (isoComp-cong (idIso AP) leftSquare ∙
      (isoComp-assoc-at AP KL lQ ∙
      (isoComp-cong (middleSquare ⁻¹) (idIso lQ) ∙
      ((isoComp-assoc-at KR AQ lQ) ⁻¹ ∙
      (isoComp-cong (idIso KR) qSquare ∙
      (isoComp-assoc-at KR rQ routeQ ∙
      (isoComp-cong (rightSquare ⁻¹) (idIso routeQ) ∙
        (isoComp-assoc-at rP κright routeQ) ⁻¹))))))))))
```
