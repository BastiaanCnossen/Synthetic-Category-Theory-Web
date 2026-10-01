# Substitution and weakening

Substitution is a specified change between the two extended theories.
Its comparison with weakening has category, functor, and identification
components. Compatibility with the generic point uses the inverse of the
substitution's terminal comparison; the two terminal categories are not
identified in Agda.

The records used for route comparisons presently express these first
layers. They do not identify transported pentagon witnesses along
different routes.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point

module SCT.VolumeI.Chapter05.Section04.Substitution
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) where

open ContextualTheories C
open Changes.Changes D
open ContextTheory C D using (W)
open ContextTheory.ContextualConstructions K

module At (Γ : Context) where
  private
    module S = View (at Γ)

  module Local (A : S.AN) where
    open Point (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
      public using (generic)

  record Substitution : Set l where
    field
      substitute : {A B : S.AN} → S.MAP (S.AN.category B) (S.AN.category A)
        → Change (extend Γ A) (extend Γ B)

    pull : {A B : S.AN} → S.MAP (S.AN.category B) (S.AN.category A)
      → Weakening (Local Γ A) (Local Γ B)
    pull {A} {B} g = underlying (substitute {A} {B} g)

    field
      constant : {A B : S.AN} (g : S.MAP (S.AN.category B) (S.AN.category A))
        → Routes.Comparison (compose (pull {A} {B} g) (W Γ A)) (W Γ B)
      constant-paths : {A B : S.AN} (g : S.MAP (S.AN.category B) (S.AN.category A))
        → Routes.PathCompatibility (constant {A} {B} g)

  module Generic (R : Substitution) {A B : S.AN}
    (g : S.MAP (S.AN.category B) (S.AN.category A)) where
    open Substitution R
    private
      module T = View (Local Γ B)
      module G = Weakening (pull {A} {B} g)
      module V = Weakening (W Γ B)

    transported : T.MAP T.One (V.cat (S.AN.category A))
    transported = T._∘_ (T.Equiv.functor (Routes.Comparison.component (constant {A} {B} g) (S.AN.category A)))
      (T._∘_ (G.map (Local.generic A)) G.back)

    represented : T.MAP T.One (V.cat (S.AN.category A))
    represented = T._∘_ (V.map g) (Local.generic B)

  record GenericCompatibility (R : Substitution) : Set l where
    field
      generic-point : {A B : S.AN} (g : S.MAP (S.AN.category B) (S.AN.category A))
        → In._=₁_ (extend Γ B) (Generic.transported R {A} {B} g) (Generic.represented R {A} {B} g)
```
