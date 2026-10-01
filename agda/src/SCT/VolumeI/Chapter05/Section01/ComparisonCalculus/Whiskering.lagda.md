# Evaluating operation comparisons

Evaluation of a comparison on an absolute term includes the terminal comparison and all associators. Applying it to the primitive operations yields the corresponding term-level formulas.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Whiskering where

open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence

module Evaluation {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

  -- Evaluate an actual natural comparison, retaining every associator.
  application : {X Y : S.CAT} {X' Y' Z : T.CAT}
    (q : S.MAP X Y) (alpha : S.MAP S.One X)
    (sx : T.MAP (cat X) X') (sy : T.MAP (cat Y) Y')
    (a : T.MAP Y' Z) (b : T.MAP X' Z)
    → T._=₁_ (a ∘ (sy ∘ map q)) (b ∘ sx)
    → T._=₁_ (a ∘ ((sy ∘ map (S._∘_ q alpha)) ∘ back))
              (b ∘ ((sx ∘ map alpha) ∘ back))
  application q alpha sx sy a b square =
    T.comp-assoc back (sx ∘ map alpha) b ∙
    (T.comp-assoc (map alpha) sx b ▷ back) ∙
    ((square ▷ map alpha) ▷ back) ∙
    ((T.comp-assoc (map q) sy a ▷ map alpha) ▷ back) ∙
    ((T.comp-assoc (map alpha) (map q) (a ∘ sy)) ⁻¹ ▷ back) ∙
    ((T.comp-assoc (map q ∘ map alpha) sy a) ⁻¹ ▷ back) ∙
    (T.comp-assoc back (sy ∘ (map q ∘ map alpha)) a) ⁻¹ ∙
    (a ◁ ((sy ◁ comp alpha q) ▷ back))

module Normalized {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open Boundaries W
  open Evaluation W

  post-identification : {C D E : S.CAT} {f g : S.MAP C D}
    (u : S.MAP D E) (alpha : S._=₁_ f g)
    → T._=₁_ (T._∘_ (conjugate (comp f u) (comp g u)) (term (S._◁_ u alpha)))
              (T._◁_ (map u) (term alpha))
  post-identification {f = f} {g} u alpha =
    application (S.postWhisker u) alpha (phi f g) (phi (S._∘_ u f) (S._∘_ u g))
      (conjugate (comp f u) (comp g u)) (T.postWhisker (map u))
      (OperationCompatibility.post K f g u)

  pre-identification : {B C D : S.CAT} {f g : S.MAP C D}
    (k : S.MAP B C) (alpha : S._=₁_ f g)
    → T._=₁_ (T._∘_ (conjugate (comp k f) (comp k g)) (term (S._▷_ alpha k)))
              (T._▷_ (term alpha) (map k))
  pre-identification {f = f} {g} k alpha =
    application (S.preWhisker k) alpha (phi f g) (phi (S._∘_ f k) (S._∘_ g k))
      (conjugate (comp k f) (comp k g)) (T.preWhisker (map k))
      (OperationCompatibility.pre K f g k)
```
