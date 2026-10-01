# Calculus for interpreted identification terms

Local composition and whiskering calculations are combined with the corresponding weak-change comparisons. They supply the recursive clauses for identification expressions.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.VerticalBoundary as VerticalBoundary
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalSquares as HorizontalSquares
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module Local {l : Level} (T : Theory l l l) where
  open View T
  open Calculus T public
  open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering public
    using (hcomp-isoComp; hcomp-idIso; reassociateFour; cancel-inverse)

  opaque
    horizontal-square : {B C D : CAT} {f f' F F' : MAP B C} {g g' G G' : MAP C D}
      (u : f =₁ F) (v : f' =₁ F') (p : g =₁ G) (q : g' =₁ G')
      (alpha : f =₁ f') (alpha' : F =₁ F') (beta : g =₁ g') (beta' : G =₁ G')
      → (v ∙ alpha) =₂ (alpha' ∙ u) → (q ∙ beta) =₂ (beta' ∙ p)
      → ((q ⋆ v) ∙ (beta ⋆ alpha)) =₂ ((beta' ⋆ alpha') ∙ (p ⋆ u))
    horizontal-square u v p q alpha alpha' beta beta' first second =
      isoComp-cong ((const-One (q ⋆ v)) ⁻¹) (idIso _) then
      HorizontalSquares.horizontal-square T u v p q alpha alpha' beta beta'
        (isoComp-cong (const-One v) (idIso _) then first then isoComp-cong (idIso _) ((const-One u) ⁻¹))
        (isoComp-cong (const-One q) (idIso _) then second then isoComp-cong (idIso _) ((const-One p) ⁻¹)) then
      isoComp-cong (idIso _) (const-One (p ⋆ u))

    paste : {C D : CAT} {f₀ f₁ f₂ g₀ g₁ g₂ : MAP C D}
      (p : f₀ =₁ f₁) (p' : f₁ =₁ f₂) (q : g₀ =₁ g₁) (q' : g₁ =₁ g₂)
      (alpha : f₀ =₁ g₀) (beta : f₁ =₁ g₁) (gamma : f₂ =₁ g₂)
      → (q ∙ alpha) =₂ (beta ∙ p) → (q' ∙ beta) =₂ (gamma ∙ p')
      → ((q' ∙ q) ∙ alpha) =₂ (gamma ∙ (p' ∙ p))
    paste p p' q q' alpha beta gamma first second =
      isoComp-assoc-at q' q alpha then isoComp-cong (idIso _) first then
      (isoComp-assoc-at q' beta p) ⁻¹ then isoComp-cong second (idIso _) then
      isoComp-assoc-at gamma p' p

    inverse-square : {C D : CAT} {f f' g g' : MAP C D}
      (p : f =₁ f') (q : g =₁ g') (alpha : f =₁ g) (beta : f' =₁ g')
      → (q ∙ alpha) =₂ (beta ∙ p) → (p ∙ (alpha ⁻¹)) =₂ ((beta ⁻¹) ∙ q)
    inverse-square p q alpha beta square =
      isoComp-cong
        ((isoComp-unitˡ-at p) ⁻¹ then
          isoComp-cong ((isoComp-inverseˡ-at beta) ⁻¹) (idIso _) then
          isoComp-assoc-at (beta ⁻¹) beta p then
          isoComp-cong (idIso _) (square ⁻¹) then
          (isoComp-assoc-at (beta ⁻¹) q alpha) ⁻¹) (idIso _) then
      isoComp-assoc-at ((beta ⁻¹) ∙ q) alpha (alpha ⁻¹) then
      isoComp-cong (idIso _) (isoComp-inverseʳ-at alpha) then isoComp-unitʳ-at _

module Transport {l : Level} {S T : Theory l l l} (W : Weakening S T) (K : OperationCompatibility W) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∙_; _⋆_; _◁_; _▷_; _⁻¹)
  open Local T
  opaque
    identity-square : {C D : S.CAT} (f : S.MAP C D) {f' : T.MAP (cat C) (cat D)}
      (p : T._=₁_ (map f) f')
      → T._=₂_ (p ∙ term (S.idIso f)) (T.idIso f' ∙ p)
    identity-square f p = isoComp-cong (T.idIso _) (OperationCompatibility.identityIso K f) then
      isoComp-unitʳ-at p then (isoComp-unitˡ-at p) ⁻¹

    inverse-term : {C D : S.CAT} {f g : S.MAP C D} (alpha : S._=₁_ f g)
      → T._=₂_ (term (S._⁻¹ alpha)) ((term alpha) ⁻¹)
    inverse-term alpha = (VerticalBoundary.inverse-family W K alpha ▷ back) then
      ⁻¹-pre (Operations.family W alpha) back

    inverse : {C D : S.CAT} {f g : S.MAP C D} {f' g' : T.MAP (cat C) (cat D)}
      (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g') (alpha : S._=₁_ f g) (beta : T._=₁_ f' g')
      → T._=₂_ (q ∙ term alpha) (beta ∙ p)
      → T._=₂_ (p ∙ term (S._⁻¹ alpha)) ((beta ⁻¹) ∙ q)
    inverse p q alpha beta square = isoComp-cong (T.idIso _) (inverse-term alpha) then
      inverse-square p q (term alpha) beta square

    horizontal-term : {B C D : S.CAT} {f f' : S.MAP B C} {g g' : S.MAP C D}
      (beta : S._=₁_ g g') (alpha : S._=₁_ f f')
      → T._=₂_ (comp f' g' ∙ term (S._⋆_ beta alpha)) ((term beta ⋆ term alpha) ∙ comp f g)
    horizontal-term {f = f} {f'} {g} {g'} beta alpha =
      Pasting.vertical W K (comp f g) (comp f' g) (comp f' g')
        (S._◁_ g alpha) (S._▷_ beta f') (map g ◁ term alpha) (term beta ▷ map f')
        (Operations.post-term-square W K g alpha) (Operations.pre-term-square W K f' beta)

    horizontal : {B C D : S.CAT} {f f' : S.MAP B C} {g g' : S.MAP C D}
      {F F' : T.MAP (cat B) (cat C)} {G G' : T.MAP (cat C) (cat D)}
      (u : T._=₁_ (map f) F) (v : T._=₁_ (map f') F')
      (p : T._=₁_ (map g) G) (q : T._=₁_ (map g') G')
      (alpha : S._=₁_ f f') (alpha' : T._=₁_ F F') (beta : S._=₁_ g g') (beta' : T._=₁_ G G')
      → T._=₂_ (v ∙ term alpha) (alpha' ∙ u) → T._=₂_ (q ∙ term beta) (beta' ∙ p)
      → T._=₂_ (((q ⋆ v) ∙ comp f' g') ∙ term (S._⋆_ beta alpha))
        ((beta' ⋆ alpha') ∙ ((p ⋆ u) ∙ comp f g))
    horizontal {f = f} {f'} {g} {g'} u v p q alpha alpha' beta beta' first second =
      paste (comp f g) (p ⋆ u) (comp f' g') (q ⋆ v) (term (S._⋆_ beta alpha))
        (term beta ⋆ term alpha) (beta' ⋆ alpha') (horizontal-term beta alpha)
        (horizontal-square u v p q (term alpha) alpha' (term beta) beta' first second)
```
