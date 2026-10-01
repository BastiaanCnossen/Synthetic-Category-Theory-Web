# Compared category and functor expressions

A compared category carries an equivalence between its weakened source and target interpretations. A compared functor carries a square with these equivalences. Products and identification animae then construct further compared expressions.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths as Rebased
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductConstructions

-- A comparison carries its endpoints. The cartesian expression interpreter
-- uses these records; the remaining constructors are supplied separately.
module SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (P : PreservesProducts W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Rebased T using (join; paths)
open ProductConstructions T.vocabulary T.terminal T.products T.productLaws T.composition
  using (productMap; productMap-id; productMap-comp)

record Object : Set l where
  field
    source : S.CAT
    target : T.CAT
    comparison : T.Equiv (cat source) target
  arrow = T.Equiv.functor comparison

record Arrow (C D : Object) : Set l where
  field
    source : S.MAP (Object.source C) (Object.source D)
    target : T.MAP (Object.target C) (Object.target D)
    square : T._=₁_ (Object.arrow D ∘ map source) (target ∘ Object.arrow C)

identity : (C : Object) → Arrow C C
identity C = record
  { source = S.id (Object.source C) ; target = T.id (Object.target C)
  ; square = (Object.arrow C ◁ unit (Object.source C)) then T.comp-unitʳ (Object.arrow C) then
      (T.comp-unitˡ (Object.arrow C)) ⁻¹ }

compose : {C D E : Object} → Arrow D E → Arrow C D → Arrow C E
compose {C} {D} {E} g f = record
  { source = S._∘_ (Arrow.source g) (Arrow.source f)
  ; target = Arrow.target g ∘ Arrow.target f
  ; square = (Object.arrow E ◁ comp (Arrow.source f) (Arrow.source g)) then
      (T.comp-assoc (map (Arrow.source f)) (map (Arrow.source g)) (Object.arrow E)) ⁻¹ then
      (Arrow.square g ▷ map (Arrow.source f)) then
      T.comp-assoc (map (Arrow.source f)) (Object.arrow D) (Arrow.target g) then
      (Arrow.target g ◁ Arrow.square f) then
      (T.comp-assoc (Object.arrow C) (Arrow.target f) (Arrow.target g)) ⁻¹ }

one : Object
one = record { source = S.One ; target = T.One ; comparison = terminal }

terminate : (C : Object) → Arrow C one
terminate C = record
  { source = S.terminate (Object.source C) ; target = T.terminate (Object.target C)
  ; square = T.terminal-iso _ _ }

opaque
  product-certificate : {C C' D D' : T.CAT} → T.Equiv C C' → T.Equiv D D'
    → T.Equiv (T._×_ C D) (T._×_ C' D')
  product-certificate {C} {C'} {D} {D'} e d = record
    { functor = productMap f g
    ; isEquiv = record
        { inverse = productMap F G
        ; sectionIso = (productMap-id C D) ⁻¹ then pair-cong
            ((T.IsEquiv.sectionIso (T.Equiv.isEquiv e)) ▷ T.pr₁)
            ((T.IsEquiv.sectionIso (T.Equiv.isEquiv d)) ▷ T.pr₂) then
            (productMap-comp f F g G) ⁻¹
        ; retractionIso = (productMap-id C' D') ⁻¹ then pair-cong
            ((T.IsEquiv.retractionIso (T.Equiv.isEquiv e)) ▷ T.pr₁)
            ((T.IsEquiv.retractionIso (T.Equiv.isEquiv d)) ▷ T.pr₂) then
            (productMap-comp F f G g) ⁻¹ } }
    where
    f : T.MAP C C'
    f = T.Equiv.functor e
    g : T.MAP D D'
    g = T.Equiv.functor d
    F : T.MAP C' C
    F = T.IsEquiv.inverse (T.Equiv.isEquiv e)
    G : T.MAP D' D
    G = T.IsEquiv.inverse (T.Equiv.isEquiv d)

  product-isEquiv : {C C' D D' : T.CAT} (e : T.Equiv C C') (d : T.Equiv D D')
    → T.IsEquiv (productMap (T.Equiv.functor e) (T.Equiv.functor d))
  product-isEquiv e d = T.Equiv.isEquiv (product-certificate e d)

product-equivalence : {C C' D D' : T.CAT} → T.Equiv C C' → T.Equiv D D'
  → T.Equiv (T._×_ C D) (T._×_ C' D')
product-equivalence e d = record
  { functor = productMap (T.Equiv.functor e) (T.Equiv.functor d)
  ; isEquiv = product-isEquiv e d }

-- Expose the comparison functor, seal only its proof of being an equivalence.
product : Object → Object → Object
product C D = record
  { source = S._×_ (Object.source C) (Object.source D)
  ; target = T._×_ (Object.target C) (Object.target D)
  ; comparison = join
      (record { functor = Products.Comparison.comparison W (Object.source C) (Object.source D)
              ; isEquiv = PreservesProducts.comparison-isEquiv P (Object.source C) (Object.source D) })
      (product-equivalence (Object.comparison C) (Object.comparison D)) }

opaque
  first-square : (C D : Object) → T._=₁_ (Object.arrow C ∘ map (S.pr₁ {Object.source C} {Object.source D}))
    (T.pr₁ ∘ Object.arrow (product C D))
  first-square C D = ((T.comp-assoc chi Q T.pr₁) ⁻¹ then
    (T.pair-β₁ (Object.arrow C ∘ T.pr₁) (Object.arrow D ∘ T.pr₂) ▷ chi) then
    T.comp-assoc chi T.pr₁ (Object.arrow C) then
    (Object.arrow C ◁ T.pair-β₁ (map S.pr₁) (map S.pr₂))) ⁻¹
    where
    chi : T.MAP (cat (S._×_ (Object.source C) (Object.source D))) (T._×_ (cat (Object.source C)) (cat (Object.source D)))
    chi = Products.Comparison.comparison W (Object.source C) (Object.source D)
    Q : T.MAP (T._×_ (cat (Object.source C)) (cat (Object.source D))) (T._×_ (Object.target C) (Object.target D))
    Q = productMap (Object.arrow C) (Object.arrow D)

  second-square : (C D : Object) → T._=₁_ (Object.arrow D ∘ map (S.pr₂ {Object.source C} {Object.source D}))
    (T.pr₂ ∘ Object.arrow (product C D))
  second-square C D = ((T.comp-assoc chi Q T.pr₂) ⁻¹ then
    (T.pair-β₂ (Object.arrow C ∘ T.pr₁) (Object.arrow D ∘ T.pr₂) ▷ chi) then
    T.comp-assoc chi T.pr₂ (Object.arrow D) then
    (Object.arrow D ◁ T.pair-β₂ (map S.pr₁) (map S.pr₂))) ⁻¹
    where
    chi : T.MAP (cat (S._×_ (Object.source C) (Object.source D))) (T._×_ (cat (Object.source C)) (cat (Object.source D)))
    chi = Products.Comparison.comparison W (Object.source C) (Object.source D)
    Q : T.MAP (T._×_ (cat (Object.source C)) (cat (Object.source D))) (T._×_ (Object.target C) (Object.target D))
    Q = productMap (Object.arrow C) (Object.arrow D)

first : (C D : Object) → Arrow (product C D) C
first C D = record { source = S.pr₁ ; target = T.pr₁ ; square = first-square C D }
second : (C D : Object) → Arrow (product C D) D
second C D = record { source = S.pr₂ ; target = T.pr₂ ; square = second-square C D }

opaque
  pairing-square : {C D E : Object} (f : Arrow C D) (g : Arrow C E)
    → T._=₁_ (Object.arrow (product D E) ∘ map (S.pair (Arrow.source f) (Arrow.source g)))
      (T.pair (Arrow.target f) (Arrow.target g) ∘ Object.arrow C)
  pairing-square {C} {D} {E} f g =
    T.comp-assoc (map (S.pair (Arrow.source f) (Arrow.source g))) chi Q then
    (Q ◁ Products.Comparison.pairing W (Arrow.source f) (Arrow.source g)) then
    pair-pre (Object.arrow D ∘ T.pr₁) (Object.arrow E ∘ T.pr₂) (T.pair (map (Arrow.source f)) (map (Arrow.source g))) then
    pair-cong
      (T.comp-assoc (T.pair (map (Arrow.source f)) (map (Arrow.source g))) T.pr₁ (Object.arrow D) then
        (Object.arrow D ◁ T.pair-β₁ (map (Arrow.source f)) (map (Arrow.source g))) then Arrow.square f)
      (T.comp-assoc (T.pair (map (Arrow.source f)) (map (Arrow.source g))) T.pr₂ (Object.arrow E) then
        (Object.arrow E ◁ T.pair-β₂ (map (Arrow.source f)) (map (Arrow.source g))) then Arrow.square g) then
    (pair-pre (Arrow.target f) (Arrow.target g) (Object.arrow C)) ⁻¹
    where
    chi : T.MAP (cat (S._×_ (Object.source D) (Object.source E))) (T._×_ (cat (Object.source D)) (cat (Object.source E)))
    chi = Products.Comparison.comparison W (Object.source D) (Object.source E)
    Q : T.MAP (T._×_ (cat (Object.source D)) (cat (Object.source E))) (T._×_ (Object.target D) (Object.target E))
    Q = productMap (Object.arrow D) (Object.arrow E)

pair : {C D E : Object} → Arrow C D → Arrow C E → Arrow C (product D E)
pair f g = record { source = S.pair (Arrow.source f) (Arrow.source g)
  ; target = T.pair (Arrow.target f) (Arrow.target g) ; square = pairing-square f g }

identifications : {C D : Object} → Arrow C D → Arrow C D → Object
identifications {C} {D} f g = record
  { source = S._＝_ (Arrow.source f) (Arrow.source g)
  ; target = T._＝_ (Arrow.target f) (Arrow.target g)
  ; comparison = join (path (Arrow.source f) (Arrow.source g))
      (paths (Object.comparison C) (Object.comparison D) (map (Arrow.source f)) (map (Arrow.source g))
        (Arrow.target f) (Arrow.target g) (record { comparison = Arrow.square f }) (record { comparison = Arrow.square g })) }

-- Supplying all remaining functors and all selected coherence laws on these
-- records would give a comparison algebra for the complete term syntax.
-- No claim is made that the present finite weakening package already does so.
```
