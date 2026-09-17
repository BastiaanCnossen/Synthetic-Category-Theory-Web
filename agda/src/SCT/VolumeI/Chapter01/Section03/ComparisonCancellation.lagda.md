# Cancelling a restricted comparison

This calculation cancels the same intermediate comparison before and
after substitution. Stating it for arbitrary comparisons keeps the
calculation independent of the construction that selected them.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.ComparisonCancellation
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-left-reflect)

abstract
  cancel-forward : {X Y : CAT} {a b c : MAP X Y}
    (W : NatIso b c) (V : NatIso a c)
    → Iso₂ (W ∙ (invIso W ∙ V)) V
  cancel-forward W V = isoComp-unitˡ-at V ∙
    (isoComp-cong (isoComp-inverseʳ-at W) (idIso V) ∙
      invIso (isoComp-assoc-at W (invIso W) V))

  cancel-restricted-comparison : {R X Y : CAT} (s : MAP R X)
    {a b c : MAP X Y} {t z k l : MAP R Y}
    (W : NatIso b c) (V : NatIso a c)
    (A : NatIso (b ∘ s) t) (B : NatIso z (a ∘ s))
    (P′ : NatIso (c ∘ s) k) (N : NatIso k l)
    → Iso₂
        ((N ∙ (P′ ∙ ((W ▷ s) ∙ invIso A))) ∙
          (A ∙ (((invIso W ∙ V) ▷ s) ∙ B)))
        (N ∙ (P′ ∙ ((V ▷ s) ∙ B)))
  cancel-restricted-comparison s W V A B P′ N =
    let restricted = (invIso W ∙ V) ▷ s
        tail = restricted ∙ B
        cancelA = isoComp-cong (idIso (W ▷ s)) (cancel-left A tail) ∙
          isoComp-assoc-at (W ▷ s) (invIso A) (A ∙ tail)
        cancelW = isoComp-cong (preWhisker s ◁ cancel-forward W V) (idIso B) ∙
          (isoComp-cong (invIso (preWhisker-isoComp-at W (invIso W ∙ V) s)) (idIso B) ∙
            invIso (isoComp-assoc-at (W ▷ s) restricted B))
        reassociate = isoComp-assoc-at N P′ ((W ▷ s) ∙ tail) ∙
          isoComp-cong (idIso (N ∙ P′)) cancelA
    in isoComp-cong (idIso N) (isoComp-cong (idIso P′) cancelW) ∙
      (reassociate ∙
        (isoComp-assoc-at (N ∙ P′) ((W ▷ s) ∙ invIso A) (A ∙ tail) ∙
          isoComp-cong (invIso (isoComp-assoc-at N P′ ((W ▷ s) ∙ invIso A))) (idIso (A ∙ tail))))
```

Two routes transported through fixed endpoint comparisons agree under
parameter change when the two endpoint squares and the middle square
agree. This formulation keeps the selected endpoint comparisons out of
the general cancellation proof.

```agda
opaque
  transport-route-square : {X Y : CAT}
    {aQ bQ cQ dQ aP bP cP dP : MAP X Y}
    (lQ : NatIso aQ bQ) (rQ : NatIso dQ cQ) (AQ : NatIso bQ cQ)
    (routeQ : NatIso aQ dQ)
    (lP : NatIso aP bP) (rP : NatIso dP cP) (AP : NatIso bP cP)
    (routeP : NatIso aP dP)
    (κleft : NatIso aQ aP) (κright : NatIso dQ dP)
    (KL : NatIso bQ bP) (KR : NatIso cQ cP)
    → Iso₂ (rQ ∙ routeQ) (AQ ∙ lQ)
    → Iso₂ (rP ∙ routeP) (AP ∙ lP)
    → Iso₂ (KL ∙ lQ) (lP ∙ κleft)
    → Iso₂ (KR ∙ rQ) (rP ∙ κright)
    → Iso₂ (AP ∙ KL) (KR ∙ AQ)
    → Iso₂ (κright ∙ routeQ) (routeP ∙ κleft)
  transport-route-square lQ rQ AQ routeQ lP rP AP routeP κleft κright KL KR
    qSquare pSquare leftSquare rightSquare middleSquare =
    cancel-left-reflect rP
      (isoComp-assoc-at rP routeP κleft ∙
      (isoComp-cong (invIso pSquare) (idIso κleft) ∙
      (invIso (isoComp-assoc-at AP lP κleft) ∙
      (isoComp-cong (idIso AP) leftSquare ∙
      (isoComp-assoc-at AP KL lQ ∙
      (isoComp-cong (invIso middleSquare) (idIso lQ) ∙
      (invIso (isoComp-assoc-at KR AQ lQ) ∙
      (isoComp-cong (idIso KR) qSquare ∙
      (isoComp-assoc-at KR rQ routeQ ∙
      (isoComp-cong (invIso rightSquare) (idIso routeQ) ∙
        invIso (isoComp-assoc-at rP κright routeQ)))))))))))
```
