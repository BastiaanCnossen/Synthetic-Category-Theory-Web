# Pullback data and cone factorization

The first part of `post:Pullback_Of_Categories` supplies a chosen cone and
a factorization of any other cone.
`pullbackCone` is the chosen cone, `pullback₁` and `pullback₂` its projections, and `pullbackMatch`
its matching isomorphism.

For another cone `s`, `pullbackLift s` is its factorization through the chosen
pullback. `pullbackLift-β s` compares the whole resulting cone with `s`, including
both projection comparisons and their matching compatibility. The
isomorphism-anima equivalence is added in `PullbackLaws`, after its actual
comparison functor has been constructed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section06.PullbackData
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

record PullbackData : Set (c ⊔ m ⊔ a) where
  field
    Pullback : {C D E : CAT} → MAP C E → MAP D E → CAT
    pullbackCone : {C D E : CAT} (f : MAP C E) (g : MAP D E) → Cone f g (Pullback f g)
    pullback-isAn : {C D E : CAT} (f : MAP C E) (g : MAP D E)
      → isAn C → isAn D → isAn E → isAn (Pullback f g)
    pullbackLift : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
      → Cone f g T → MAP T (Pullback f g)
    pullbackLift-β : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
      → ConeIso (conePre (pullbackLift s) (pullbackCone f g)) s

  pullback₁ : {C D E : CAT} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) C
  pullback₁ {f = f} {g} = Cone.left (pullbackCone f g)

  pullback₂ : {C D E : CAT} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) D
  pullback₂ {f = f} {g} = Cone.right (pullbackCone f g)

  pullbackMatch : {C D E : CAT} {f : MAP C E} {g : MAP D E} → (f ∘ pullback₁) =₁ (g ∘ pullback₂)
  pullbackMatch {f = f} {g} = Cone.match (pullbackCone f g)

  pullbackLift-β₁ : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
    → (pullback₁ ∘ pullbackLift s) =₁ (Cone.left s)
  pullbackLift-β₁ s = ConeIso.leftIso (pullbackLift-β s)

  pullbackLift-β₂ : {C D E T : CAT} {f : MAP C E} {g : MAP D E} (s : Cone f g T)
    → (pullback₂ ∘ pullbackLift s) =₁ (Cone.right s)
  pullbackLift-β₂ s = ConeIso.rightIso (pullbackLift-β s)
```
