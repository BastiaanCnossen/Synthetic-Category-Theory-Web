# Restriction of the projection triangle

The projection-naturality triangle restricts to the terminal comparison
in the local theory. The formula includes the associator between
`(generic ∘ terminate C) ∘ f` and `generic ∘ (terminate C ∘ f)`.
It computes the specified triangle without replacing its witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumPostcomposition as Postcomposition
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumComposition as Composition
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point

module SCT.VolumeI.Chapter05.Section03.MappingOverBaseCalculus.ProjectionNaturality
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : Coherence.OperationCompatibility W)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A)) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Point W P Q A e using (generic; projection; projection-β; projection-natural)
open Action W P Q using (Σ-map; Σ-map-comp; Σ-map-cong)
open Calculus T using (_then_)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T using (isoComp-cong; isoComp-assoc-at)
open Identifications W K P Q using (action; action-comp)
open Action W P Q using (flatten-local-pre)

projection-flat-naturality : {B C : T.CAT} (f : T.MAP B C)
  → T._=₂_ (projection-β B ∙ action (projection-natural f))
    ((generic ◁ T.terminal-iso (T.terminate C ∘ f) (T.terminate B)) ∙
      (T.comp-assoc f (T.terminate C) generic ∙
        ((projection-β C ▷ f) ∙ flatten-local-pre (projection C) f)))
projection-flat-naturality {B} {C} f =
  isoComp-cong (T.idIso (projection-β B))
    (action-comp a₂ (S._∙_ a₁ a₀) then
      isoComp-cong (T.idIso (action a₂)) (action-comp a₁ a₀)) then
  (isoComp-assoc-at (projection-β B) (action a₂) (action a₁ ∙ action a₀)) ⁻¹ then
  isoComp-cong (Postcomposition.local-functor-naturality W K P Q h τ) (T.idIso _) then
  isoComp-assoc-at (generic ◁ τ) (flatten-local-pre h (T.terminate C ∘ f))
    (action a₁ ∙ action a₀) then
  isoComp-cong (T.idIso (generic ◁ τ))
    ((isoComp-assoc-at (flatten-local-pre h (T.terminate C ∘ f)) (action a₁) (action a₀)) ⁻¹ then
      Composition.Restriction.Postcomposition.comparison W K P Q f (T.terminate C) h)
  where
  h = S.Equiv.functor e
  τ = T.terminal-iso (T.terminate C ∘ f) (T.terminate B)
  a₂ = S._◁_ h (Σ-map-cong τ)
  a₁ = S._◁_ h (S._⁻¹ (Σ-map-comp f (T.terminate C)))
  a₀ = S.comp-assoc (Σ-map f) (Σ-map (T.terminate C)) h
```
