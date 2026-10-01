# Identifications under dependent uncurrying

The action below uses postwhiskering after transport. Its comparison with
the action of the universal-property functor retains both associators.
Consequently the reflection computation also applies to this expression.
Reflection of a further identification uses the same universal property
with the identification anima as its source.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductReflection as Reflection
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.CurryingLifting as Lifting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskerEquiv

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open WhiskerEquiv T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (preWhisker-lift)

action : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  → S._=₁_ h k → T._=₁_ (uncurry h) (uncurry k)
action {B = B} α = evaluation B ◁ W.term α

action-comparison : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  (α : S._=₁_ h k) → T._=₂_ (Reflection.action W P α) (action α)
action-comparison {B = B} {h} {k} α =
  (T.comp-assoc (W.map α) (W.phi h k) (T.postWhisker (evaluation B)) ▷ W.back) then
  T.comp-assoc W.back (W.phi h k ∘ W.map α) (T.postWhisker (evaluation B))

reflect : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  → T._=₁_ (uncurry h) (uncurry k) → S._=₁_ h k
reflect = Action.reflect W P

reflect-β : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  (α : T._=₁_ (uncurry h) (uncurry k)) → T._=₂_ (action (reflect α)) α
reflect-β α = (action-comparison (reflect α)) ⁻¹ then Reflection.reflect-β W P α

reflect₂ : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  {α β : S._=₁_ h k} → T._=₂_ (action α) (action β) → S._=₂_ α β
reflect₂ {h = h} {k} {α} {β} p = Lifting.Along.reflect W P
  (uncurry-family h k) (comparison-isEquiv h k)
  (T.FunctorLift.lift (preWhisker-lift W.back
    (T.equiv-inverse (T.Equiv.isEquiv W.terminal))
    (action-comparison α then p then (action-comparison β) ⁻¹)))

action₂ : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  {α β : S._=₁_ h k} → S._=₂_ α β → T._=₂_ (action α) (action β)
action₂ {B = B} p = T.postWhisker (evaluation B) ◁ W.cell2 p

action-comp : {X : S.CAT} {B : T.CAT} {h k j : S.MAP X (Π B)}
  (β : S._=₁_ k j) (α : S._=₁_ h k)
  → T._=₂_ (action (S._∙_ β α)) (action β ∙ action α)
action-comp {B = B} β α =
  (T.postWhisker (evaluation B) ◁ Operations.vertical-term W K β α) then
  postWhisker-isoComp-at (evaluation B) (W.term β) (W.term α)
```
