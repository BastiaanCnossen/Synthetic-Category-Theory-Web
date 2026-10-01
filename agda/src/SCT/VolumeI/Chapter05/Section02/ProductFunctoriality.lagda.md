# Functoriality of dependent products

The identification-anima axiom reflects local identifications between
uncurried functors. This gives uniqueness of currying and the identity and
composition comparisons for the action of the dependent product.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.ProductFunctoriality
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

reflect : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  → T._=₁_ (uncurry h) (uncurry k) → S._=₁_ h k
reflect {h = h} {k} α = S._∘_ (S.IsEquiv.inverse (comparison-isEquiv h k))
  (curry (α ∘ T.terminate (W.cat S.One)))

curry-η : {X : S.CAT} {B : T.CAT} (h : S.MAP X (Π B))
  → S._=₁_ (curry (uncurry h)) h
curry-η h = reflect ((curry-β (uncurry h)) ⁻¹)

curry-cong : {X : S.CAT} {B : T.CAT} {f g : T.MAP (W.cat X) B}
  → T._=₁_ f g → S._=₁_ (curry f) (curry g)
curry-cong {f = f} {g} α = reflect ((curry-β f) ⁻¹ then α then curry-β g)

uncurry-pre : {X Y : S.CAT} {B : T.CAT} (h : S.MAP Y (Π B)) (r : S.MAP X Y)
  → T._=₁_ (uncurry (S._∘_ h r)) (uncurry h ∘ W.map r)
uncurry-pre {B = B} h r = (evaluation B ◁ W.comp r h) then
  (T.comp-assoc (W.map r) (W.map h) (evaluation B)) ⁻¹

curry-pre : {X Y : S.CAT} {B : T.CAT} (f : T.MAP (W.cat Y) B) (r : S.MAP X Y)
  → S._=₁_ (curry (f ∘ W.map r)) (S._∘_ (curry f) r)
curry-pre f r = reflect ((curry-β (f ∘ W.map r)) ⁻¹ then
  (curry-β f ▷ W.map r) then (uncurry-pre (curry f) r) ⁻¹)

Π-map : {B C : T.CAT} → T.MAP B C → S.MAP (Π B) (Π C)
Π-map {B} f = curry (f ∘ evaluation B)

Π-map-β : {B C : T.CAT} (f : T.MAP B C)
  → T._=₁_ (f ∘ evaluation B) (uncurry (Π-map f))
Π-map-β {B} f = curry-β (f ∘ evaluation B)

Π-map-cong : {B C : T.CAT} {f g : T.MAP B C}
  → T._=₁_ f g → S._=₁_ (Π-map f) (Π-map g)
Π-map-cong {B} α = curry-cong (α ▷ evaluation B)

Π-map-id : (B : T.CAT) → S._=₁_ (Π-map (T.id B)) (S.id (Π B))
Π-map-id B = reflect ((Π-map-β (T.id B)) ⁻¹ then T.comp-unitˡ (evaluation B) then
  (T.comp-unitʳ (evaluation B)) ⁻¹ then (evaluation B ◁ (W.unit (Π B)) ⁻¹))

Π-map-comp : {B C D : T.CAT} (f : T.MAP B C) (g : T.MAP C D)
  → S._=₁_ (Π-map (g ∘ f)) (S._∘_ (Π-map g) (Π-map f))
Π-map-comp {B} {C} f g = reflect ((Π-map-β (g ∘ f)) ⁻¹ then
  T.comp-assoc (evaluation B) f g then (g ◁ Π-map-β f) then
  (T.comp-assoc (W.map (Π-map f)) (evaluation C) g) ⁻¹ then
  (Π-map-β g ▷ W.map (Π-map f)) then (uncurry-pre (Π-map g) (Π-map f)) ⁻¹)
```
