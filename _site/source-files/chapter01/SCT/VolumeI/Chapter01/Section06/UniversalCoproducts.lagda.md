# Universality of coproducts

A copair retains its functor and both specified triangles. Prescribed
restriction recovery compares any two such choices. Its image laws compute
the entire inverse triangle after changing the copairing arrow, which is
the matching required by the inclusion cones.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.UniversalCoproducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp-inv-right)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport)
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing using (copair; copair-β₁; copair-β₂)
open import SCT.VolumeI.Chapter01.Section05.IdentificationRestriction
  using (module IdentificationFromRestrictions)
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions using (coproductMap)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
  using (cone-change-right; cone-retarget-match-identification)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (Pullback; pullback₁)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
  using (isPullback-cone-identification; module RightArrowChange)

module _ {Γ : Context} where
  record Copair {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) : Set m where
    field
      functor : MAP (C ⊔ D) E
      left-triangle : (functor ∘ in₁) =₁ f
      right-triangle : (functor ∘ in₂) =₁ g

  chosen-copair : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) → Copair f g
  chosen-copair f g = record
    { functor = copair f g
    ; left-triangle = copair-β₁ f g
    ; right-triangle = copair-β₂ f g }
```

## Changing the chosen copair

The comparison has prescribed restrictions: the inverse target triangle
followed by the source triangle. Composing with the inverse source triangle
then cancels that pair and leaves the inverse target triangle. This
compares complete matchings without identifying the triangle witnesses.
Equivalence of the copairing functor also transfers along the comparison.

```agda
  module CopairComparison {C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s t : Copair f g) where
    module Recovery = IdentificationFromRestrictions
      (Copair.functor s) (Copair.functor t)
      ((Copair.left-triangle t) ⁻¹ ∙ Copair.left-triangle s)
      ((Copair.right-triangle t) ⁻¹ ∙ Copair.right-triangle s)

    identification : Copair.functor s =₁ Copair.functor t
    identification = Recovery.identification

    left-matching :
      ((identification ▷ in₁) ∙ (Copair.left-triangle s) ⁻¹) =₂
        (Copair.left-triangle t) ⁻¹
    left-matching =
      comp-inv-right ((Copair.left-triangle t) ⁻¹) (Copair.left-triangle s) ∙
        comp₌-cong Recovery.restriction₁ (id₌ ((Copair.left-triangle s) ⁻¹))

    right-matching :
      ((identification ▷ in₂) ∙ (Copair.right-triangle s) ⁻¹) =₂
        (Copair.right-triangle t) ⁻¹
    right-matching =
      comp-inv-right ((Copair.right-triangle t) ⁻¹) (Copair.right-triangle s) ∙
        comp₌-cong Recovery.restriction₂ (id₌ ((Copair.right-triangle s) ⁻¹))

    transfer-isEquiv : IsEquiv (Copair.functor s) → IsEquiv (Copair.functor t)
    transfer-isEquiv = equiv-transport identification
```

## The inclusion cones

For a copair of the two target inclusion composites, the two source
summands form cones. Their matchings are exactly the inverse triangles.
Changing the chosen copairing arrow and applying the prescribed matching
comparison gives a complete identification of each transported cone with
its target, including the square between the matchings.

```agda
  copairSquare₁ : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
    (s : Copair (in₁ {C = P} {D = Q} ∘ f) (in₂ ∘ g))
    → Cone (in₁ {C = P} {D = Q}) (Copair.functor s) C
  copairSquare₁ f g s = record
    { left = f; right = in₁; match = (Copair.left-triangle s) ⁻¹ }

  copairSquare₂ : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
    (s : Copair (in₁ {C = P} {D = Q} ∘ f) (in₂ ∘ g))
    → Cone (in₂ {C = P} {D = Q}) (Copair.functor s) D
  copairSquare₂ f g s = record
    { left = g; right = in₂; match = (Copair.right-triangle s) ⁻¹ }

  module CopairSquareComparison {C D P Q : CAT Γ}
    (f : MAP C P) (g : MAP D Q)
    (s t : Copair (in₁ {C = P} {D = Q} ∘ f) (in₂ ∘ g)) where
    module Comparison = CopairComparison s t

    left : ConeIdentification₁
      (cone-change-right Comparison.identification (copairSquare₁ f g s))
      (copairSquare₁ f g t)
    left = cone-retarget-match-identification
      (cone-change-right Comparison.identification (copairSquare₁ f g s))
      ((Copair.left-triangle t) ⁻¹) Comparison.left-matching

    right : ConeIdentification₁
      (cone-change-right Comparison.identification (copairSquare₂ f g s))
      (copairSquare₂ f g t)
    right = cone-retarget-match-identification
      (cone-change-right Comparison.identification (copairSquare₂ f g s))
      ((Copair.right-triangle t) ⁻¹) Comparison.right-matching

    left-isPullback : IsPullback (copairSquare₁ f g s) → IsPullback (copairSquare₁ f g t)
    left-isPullback e = isPullback-cone-identification left
      (RightArrowChange.isPullback Comparison.identification (copairSquare₁ f g s) e)

    right-isPullback : IsPullback (copairSquare₂ f g s) → IsPullback (copairSquare₂ f g t)
    right-isPullback e = isPullback-cone-identification right
      (RightArrowChange.isPullback Comparison.identification (copairSquare₂ f g s) e)

  coproductSquare₁ : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
    → Cone (in₁ {C = P} {D = Q}) (coproductMap f g) C
  coproductSquare₁ f g = copairSquare₁ f g (chosen-copair (in₁ ∘ f) (in₂ ∘ g))

  coproductSquare₂ : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
    → Cone (in₂ {C = P} {D = Q}) (coproductMap f g) D
  coproductSquare₂ f g = copairSquare₂ f g (chosen-copair (in₁ ∘ f) (in₂ ∘ g))
```

## Reassembly

Base change along the two inclusions gives two projections to the source
of h. Reassembly is their actual chosen copair.

```agda
  reassemble : {E P Q : CAT Γ} (h : MAP E (P ⊔ Q))
    → MAP (Pullback h in₁ ⊔ Pullback h in₂) E
  reassemble h = copair pullback₁ pullback₁
```

## The supplied universality clauses

The two inclusion cones are pullbacks and reassembly is an equivalence.
These are the three original contextual assumptions. Their cones retain
the specified inverse beta matchings. The derived comparisons above
transfer inclusion universality to any other copair with its own two
triangles; equivalence of reassembly likewise transfers along the copair
comparison. No equality of the chosen triangle witnesses is assumed.

```agda
  postulate
    inclusion₁-isPullback : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
      → IsPullback (coproductSquare₁ f g)
    inclusion₂-isPullback : {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D Q)
      → IsPullback (coproductSquare₂ f g)
    reassemble-isEquiv : {E P Q : CAT Γ} (h : MAP E (P ⊔ Q)) → IsEquiv (reassemble h)
```
