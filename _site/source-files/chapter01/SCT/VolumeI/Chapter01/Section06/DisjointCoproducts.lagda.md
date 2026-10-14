# Disjoint coproducts

Initiality compares the actual maps from the initial vertex. The specified
cospan equivalence retains the disjoint cone orientation (in2,in1).
The proof uses the actual inclusion pullback and coproduct right-unit
comparison. It requires no strictness or initial-anima assumption.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.DisjointCoproducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions using (IsContractible; terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section05.Initial
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
  using (left-isEquiv-from-isPullback)

module _ {Γ : Context} where
  disjoint-cone : (C D : CAT Γ) → Cone (in₂ {C = C} {D = D}) in₁ Zero
  disjoint-cone C D = record { left = initiate D ; right = initiate C ; match = initial-unique _ _ }

  module Disjointness (C D : CAT Γ) where

    H : MAP (C ⊔ Zero) (C ⊔ D)
    H = coproductMap (id C) (initiate D)
    unit : MAP (C ⊔ Zero) C
    unit = coproduct-unitʳ C
    inclusion-law : (in₁ ∘ unit) =₁ H
    inclusion-law = copair-cong (id₌ (in₁ ∘ id C)) (initial-unique _ _) ∙
      copair-post (id C) (initiate C) in₁

    cospan : CospanMap (in₂ {C = C} {D = D}) H in₂ in₁
    cospan = record
      { left = id D ; right = unit ; base = id (C ⊔ D)
      ; left-square = (comp-unitˡ in₂) ⁻¹ ∙ comp-unitʳ in₂
      ; right-square = (comp-unitˡ H) ⁻¹ ∙ inclusion-law }
    module F = CospanMap cospan
    module E = CospanEquivalence cospan (id-isEquiv D) (coproduct-unitʳ-isEquiv C) (id-isEquiv (C ⊔ D))
      using (pullback-map-isEquiv)

    initial-source-law :
      ((pullback-map cospan) ∘ pullback-factor (coproductSquare₂ (id C) (initiate D))) =₁
        pullback-factor (disjoint-cone C D)
    initial-source-law = initial-unique _ _

    isPullback : IsPullback (disjoint-cone C D)
    isPullback = equiv-transport initial-source-law
      (equiv-compose (pullback-factor (coproductSquare₂ (id C) (initiate D))) (pullback-map cospan)
        (inclusion₂-isPullback (id C) (initiate D)) E.pullback-map-isEquiv)

  disjoint-isPullback : (C D : CAT Γ) → IsPullback (disjoint-cone C D)
  disjoint-isPullback = Disjointness.isPullback
```

## Universality of the empty category

For any functor `g : D → E`, the square with both upper vertices Zero is
a pullback (`lem:Canonical_Pullback_Square`). Its factor and first projection
compose to a functor into Zero. Strictness and cancellation prove that the
factor is an equivalence. This consequence needs no anima hypothesis.

```agda
module _ {Γ : Context} where
  empty-cone : {D E : CAT Γ} (g : MAP D E) → Cone (initiate E) g Zero
  empty-cone g = record
    { left = id Zero
    ; right = initiate _
    ; match = initial-unique _ _ }

  empty-isPullback : {D E : CAT Γ} (g : MAP D E) → IsPullback (empty-cone g)
  empty-isPullback {E = E} g =
    equiv-cancel-left (pullback-factor (empty-cone g)) projection
      (into-zero-isEquiv projection)
      (into-zero-isEquiv (projection ∘ pullback-factor (empty-cone g)))
    where
    projection : MAP (Pullback (initiate E) g) Zero
    projection = pullback₁
```

## Collapse when the two-point category is contractible

If `One ⊔ One` is contractible, its first inclusion is an equivalence.
Disjointness makes the initial-to-terminal functor an equivalence as well.
Its inverse gives every category a functor into Zero; strictness then makes
every category contractible. The converse is the instance `One ⊔ One`.
This proves `lem:2_Contractible_Implies_Everything_Contractible`.

```agda
module _ {Γ : Context} where
  two-contractible-implies-all : IsContractible (One ⊔ One)
    → (C : CAT Γ) → IsContractible C
  two-contractible-implies-all two-contractible C =
    contractible-source to-zero (into-zero-isEquiv to-zero) zero-contractible
    where
    inclusion : MAP One (One ⊔ One)
    inclusion = in₁
    inclusion-isEquiv : IsEquiv inclusion
    inclusion-isEquiv = equiv-cancel-left inclusion (terminate (One ⊔ One))
      two-contractible
      (equiv-transport (terminal-identification (id One) _ ) (id-isEquiv One))
    initial-terminal-isEquiv : IsEquiv (initiate One)
    initial-terminal-isEquiv = left-isEquiv-from-isPullback
      inclusion-isEquiv (disjoint-cone One One) (disjoint-isPullback One One)
    zero-contractible : IsContractible Zero
    zero-contractible = equiv-transport
      (terminal-identification (initiate One) (terminate Zero)) initial-terminal-isEquiv
    to-zero : MAP C Zero
    to-zero = IsEquiv.inverse initial-terminal-isEquiv ∘ terminate C
```
