# Pullback data and cone factorization

The first part of `post:Pullback_Of_Categories` supplies a chosen cone and
a factorization of any other cone, with both projection comparisons and
their matching compatibility. The isomorphism-anima equivalence is added
only after its actual comparison functor has been constructed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.PullbackData
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯

record PullbackData : Set (c ⊔ m ⊔ a) where
  field
    Pullback : {C D E : CAT} → MAP C E → MAP D E → CAT
    pbCone : {C D E : CAT} (f : MAP C E) (g : MAP D E) → Cone f g (Pullback f g)
    pullback-isAn : {C D E : CAT} (f : MAP C E) (g : MAP D E)
      → isAn C → isAn D → isAn E → isAn (Pullback f g)
    pbLift : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
      → Cone f g T → MAP T (Pullback f g)
    pbLift-β : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
      → ConeIso (conePre (pbLift s) (pbCone f g)) s

  pb₁ : {C D E : CAT} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) C
  pb₁ {f = f} {g} = Cone.left (pbCone f g)

  pb₂ : {C D E : CAT} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) D
  pb₂ {f = f} {g} = Cone.right (pbCone f g)

  pbMatch : {C D E : CAT} {f : MAP C E} {g : MAP D E} → =₁ (f ∘ pb₁) (g ∘ pb₂)
  pbMatch {f = f} {g} = Cone.match (pbCone f g)

  pbLift-β₁ : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
    → =₁ (pb₁ ∘ pbLift s) (Cone.left s)
  pbLift-β₁ s = ConeIso.leftIso (pbLift-β s)

  pbLift-β₂ : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
    → =₁ (pb₂ ∘ pbLift s) (Cone.right s)
  pbLift-β₂ s = ConeIso.rightIso (pbLift-β s)
```
