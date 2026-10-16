# Chosen pullbacks

The chosen pullback has a cone and a factorization of every supplied cone.
Its beta is a complete cone identification. The first five contextual
assumptions are precisely these choices and preservation of animae.
The sixth field concerns the actual identification restriction constructed
below. Its new specified matching was approved by the author on 6 October
2026. Agreement with the first rebuild's matching is not asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.Pullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (module ConeAction)

module _ {Γ : Context} where
  postulate
    Pullback : {C D E : CAT Γ} → MAP C E → MAP D E → CAT Γ
    pullback-cone : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
      → Cone f g (Pullback f g)
    pullback-isAn : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
      → isAn C → isAn D → isAn E → isAn (Pullback f g)
    pullback-factor : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
      → Cone f g T → MAP T (Pullback f g)
    pullback-factor-β : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
      (s : Cone f g T)
      → ConeIdentification₁ (cone-restrict (pullback-factor s) (pullback-cone f g)) s

  pullback₁ : {C D E : CAT Γ} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) C
  pullback₁ {f = f} {g} = Cone.left (pullback-cone f g)

  pullback₂ : {C D E : CAT Γ} {f : MAP C E} {g : MAP D E} → MAP (Pullback f g) D
  pullback₂ {f = f} {g} = Cone.right (pullback-cone f g)

  pullback-match : {C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    → (f ∘ pullback₁) =₁ (g ∘ pullback₂)
  pullback-match {f = f} {g} = Cone.match (pullback-cone f g)

  pullback-factor-β₁ : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → (pullback₁ ∘ pullback-factor s) =₁ Cone.left s
  pullback-factor-β₁ s = ConeIdentification₁.left (pullback-factor-β s)

  pullback-factor-β₂ : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → (pullback₂ ∘ pullback-factor s) =₁ Cone.right s
  pullback-factor-β₂ s = ConeIdentification₁.right (pullback-factor-β s)

  pullback-factor-identification : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T)
    → ConeIdentification One (cone-restrict (pullback-factor s) (pullback-cone f g)) s
  pullback-factor-identification s = cone-identification (pullback-factor-β s)
```

## Restriction on identification animae

For two vertex maps, the cone action determines a cone with the two
postwhiskering functors as legs and its specified matching. Its chosen
factorization defines the newly selected identification restriction. The
identification-boundary animae, legs and hypotheses are unchanged. The new
diagram-derived matching replaces the old selected witness; no old/new
comparison is assumed.

```agda
  module PullbackIdentifications {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (h k : MAP T (Pullback f g)) where
    module Action = ConeAction (pullback-cone f g) h k
    module Boundary = Action.Boundary

    Target : CAT Γ
    Target = Pullback Boundary.left-map Boundary.right-map

    target-isAn : isAn Target
    target-isAn = pullback-isAn Boundary.left-map Boundary.right-map
      (＝-isAn _ _) (＝-isAn _ _) (＝-isAn _ _)

    identification-cone : Cone Boundary.left-map Boundary.right-map (h ＝ k)
    identification-cone = Action.identification-cone

    restriction : MAP (h ＝ k) Target
    restriction = pullback-factor identification-cone

  postulate
    pullback-identifications-isEquiv : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
      (h k : MAP T (Pullback f g)) → IsEquiv (PullbackIdentifications.restriction h k)
```
