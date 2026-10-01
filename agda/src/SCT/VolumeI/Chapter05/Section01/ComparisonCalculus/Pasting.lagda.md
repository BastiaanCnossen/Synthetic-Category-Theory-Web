# Pasting comparison squares

Commuting comparison squares can be pasted vertically and whiskered. The formulas keep the precise source and target identifications used in subsequent witness transport.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pasting {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T

vertical : {C D : S.CAT} {f g h : S.MAP C D}
  {f' g' h' : T.MAP (cat C) (cat D)}
  (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g') (r : T._=₁_ (map h) h')
  (alpha : S._=₁_ f g) (beta : S._=₁_ g h)
  (alpha' : T._=₁_ f' g') (beta' : T._=₁_ g' h')
  → T._=₂_ (q ∙ term alpha) (alpha' ∙ p)
  → T._=₂_ (r ∙ term beta) (beta' ∙ q)
  → T._=₂_ (r ∙ term (S._∙_ beta alpha)) ((beta' ∙ alpha') ∙ p)
vertical p q r alpha beta alpha' beta' first second =
  isoComp-cong (T.idIso _) (Operations.vertical-term W K beta alpha) then
  (isoComp-assoc-at r (term beta) (term alpha)) ⁻¹ then
  isoComp-cong second (T.idIso _) then
  isoComp-assoc-at beta' q (term alpha) then
  isoComp-cong (T.idIso _) first then
  (isoComp-assoc-at beta' alpha' p) ⁻¹

pre : {B C D : S.CAT} {f g : S.MAP C D} {f' g' : T.MAP (cat C) (cat D)}
  (k : S.MAP B C) (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g')
  (alpha : S._=₁_ f g) (beta : T._=₁_ f' g')
  → T._=₂_ (q ∙ term alpha) (beta ∙ p)
  → T._=₂_ (((q ▷ map k) ∙ comp k g) ∙ term (S._▷_ alpha k))
      ((beta ▷ map k) ∙ ((p ▷ map k) ∙ comp k f))
pre {f = f} {g} k p q alpha beta square =
  isoComp-assoc-at (q ▷ map k) (comp k g) (term (S._▷_ alpha k)) then
  isoComp-cong (T.idIso _) (Operations.pre-term-square W K k alpha) then
  (isoComp-assoc-at (q ▷ map k) (term alpha ▷ map k) (comp k f)) ⁻¹ then
  isoComp-cong ((preWhisker-isoComp-at q (term alpha) (map k)) ⁻¹ then
    (T.preWhisker (map k) ◁ square) then preWhisker-isoComp-at beta p (map k)) (T.idIso _) then
  isoComp-assoc-at (beta ▷ map k) (p ▷ map k) (comp k f)

post : {C D E : S.CAT} {f g : S.MAP C D} {f' g' : T.MAP (cat C) (cat D)}
  (u : S.MAP D E) (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g')
  (alpha : S._=₁_ f g) (beta : T._=₁_ f' g')
  → T._=₂_ (q ∙ term alpha) (beta ∙ p)
  → T._=₂_ (((map u ◁ q) ∙ comp g u) ∙ term (S._◁_ u alpha))
      ((map u ◁ beta) ∙ ((map u ◁ p) ∙ comp f u))
post {f = f} {g} u p q alpha beta square =
  isoComp-assoc-at (map u ◁ q) (comp g u) (term (S._◁_ u alpha)) then
  isoComp-cong (T.idIso _) (Operations.post-term-square W K u alpha) then
  (isoComp-assoc-at (map u ◁ q) (map u ◁ term alpha) (comp f u)) ⁻¹ then
  isoComp-cong ((postWhisker-isoComp-at (map u) q (term alpha)) ⁻¹ then
    (T.postWhisker (map u) ◁ square) then postWhisker-isoComp-at (map u) beta p) (T.idIso _) then
  isoComp-assoc-at (map u ◁ beta) (map u ◁ p) (comp f u)
```
