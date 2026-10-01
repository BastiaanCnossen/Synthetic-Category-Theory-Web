# Functoriality of dependent sums

Extension reflects identifications by the sum universal property. The
functor on total categories and its comparison identifications are derived
from this reflection; they are not further fields of the sum axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.SumFunctoriality
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
module P = Products.DependentProducts P
open Sums.DependentSums Q
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

reflect : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  → T._=₁_ (flatten h) (flatten k) → S._=₁_ h k
reflect {h = h} {k} α = S._∘_ (S.IsEquiv.inverse (comparison-isEquiv h k))
  (P.curry (α ∘ T.terminate (W.cat S.One)))

extend-η : {B : T.CAT} {D : S.CAT} (h : S.MAP (Σ B) D)
  → S._=₁_ (extend (flatten h)) h
extend-η h = reflect ((extend-β (flatten h)) ⁻¹)

extend-cong : {B : T.CAT} {D : S.CAT} {f g : T.MAP B (W.cat D)}
  → T._=₁_ f g → S._=₁_ (extend f) (extend g)
extend-cong {f = f} {g} α = reflect ((extend-β f) ⁻¹ then α then extend-β g)

flatten-post : {B : T.CAT} {D E : S.CAT} (h : S.MAP D E) (k : S.MAP (Σ B) D)
  → T._=₁_ (flatten (S._∘_ h k)) (W.map h ∘ flatten k)
flatten-post {B} h k = (W.comp k h ▷ pair B) then
  T.comp-assoc (pair B) (W.map k) (W.map h)

extend-post : {B : T.CAT} {D E : S.CAT} (h : S.MAP D E) (f : T.MAP B (W.cat D))
  → S._=₁_ (extend (W.map h ∘ f)) (S._∘_ h (extend f))
extend-post h f = reflect ((extend-β (W.map h ∘ f)) ⁻¹ then
  (W.map h ◁ extend-β f) then (flatten-post h (extend f)) ⁻¹)

Σ-map : {B C : T.CAT} → T.MAP B C → S.MAP (Σ B) (Σ C)
Σ-map {C = C} f = extend (pair C ∘ f)

Σ-map-β : {B C : T.CAT} (f : T.MAP B C)
  → T._=₁_ (pair C ∘ f) (flatten (Σ-map f))
Σ-map-β {C = C} f = extend-β (pair C ∘ f)

Σ-map-cong : {B C : T.CAT} {f g : T.MAP B C}
  → T._=₁_ f g → S._=₁_ (Σ-map f) (Σ-map g)
Σ-map-cong {C = C} α = extend-cong (pair C ◁ α)

Σ-map-id : (B : T.CAT) → S._=₁_ (Σ-map (T.id B)) (S.id (Σ B))
Σ-map-id B = reflect ((Σ-map-β (T.id B)) ⁻¹ then T.comp-unitʳ (pair B) then
  (T.comp-unitˡ (pair B)) ⁻¹ then ((W.unit (Σ B)) ⁻¹ ▷ pair B))

Σ-map-comp : {B C D : T.CAT} (f : T.MAP B C) (g : T.MAP C D)
  → S._=₁_ (Σ-map (g ∘ f)) (S._∘_ (Σ-map g) (Σ-map f))
Σ-map-comp {B} {C} {D} f g = reflect ((Σ-map-β (g ∘ f)) ⁻¹ then
  (T.comp-assoc f g (pair D)) ⁻¹ then (Σ-map-β g ▷ f) then
  T.comp-assoc f (pair C) (W.map (Σ-map g)) then
  (W.map (Σ-map g) ◁ Σ-map-β f) then (flatten-post (Σ-map g) (Σ-map f)) ⁻¹)

extend-local-pre : {B C : T.CAT} {D : S.CAT} (f : T.MAP C (W.cat D)) (r : T.MAP B C)
  → S._=₁_ (S._∘_ (extend f) (Σ-map r)) (extend (f ∘ r))
extend-local-pre {C = C} f r = reflect (flatten-post (extend f) (Σ-map r) then
  (W.map (extend f) ◁ (Σ-map-β r) ⁻¹) then
  (T.comp-assoc r (pair C) (W.map (extend f))) ⁻¹ then
  ((extend-β f) ⁻¹ ▷ r) then extend-β (f ∘ r))

counit : (D : S.CAT) → S.MAP (Σ (W.cat D)) D
counit D = extend (T.id (W.cat D))

counit-β : (D : S.CAT) → T._=₁_ (T.id (W.cat D)) (flatten (counit D))
counit-β D = extend-β (T.id (W.cat D))

flatten-local-pre : {B C : T.CAT} {D : S.CAT} (h : S.MAP (Σ C) D) (r : T.MAP B C)
  → T._=₁_ (flatten (S._∘_ h (Σ-map r))) (flatten h ∘ r)
flatten-local-pre {C = C} h r = flatten-post h (Σ-map r) then
  (W.map h ◁ (Σ-map-β r) ⁻¹) then (T.comp-assoc r (pair C) (W.map h)) ⁻¹

counit-natural : {C D : S.CAT} (f : S.MAP C D)
  → S._=₁_ (S._∘_ (counit D) (Σ-map (W.map f))) (S._∘_ f (counit C))
counit-natural {C} {D} f = S._∙_ (extend-post f (T.id (W.cat C)))
  (S._∙_ (extend-cong ((T.comp-unitʳ (W.map f)) ⁻¹))
    (S._∙_ (extend-cong (T.comp-unitˡ (W.map f)))
      (extend-local-pre (T.id (W.cat D)) (W.map f))))
```
