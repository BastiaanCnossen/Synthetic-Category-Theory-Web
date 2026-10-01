# Identifications under restriction to a local category

Restriction of an absolute identification is prewhiskering its weakened
image by the pair functor. Comparing this expression with the action of
the universal-property functor gives the reflection computation at the
next level. It also permits reflection of identifications between
identifications.

In particular, the chosen action of dependent sum on an identification
has the computation obtained by conjugating with the two extension
computation witnesses. This retains the chosen witnesses needed in
subsequent comparisons with total categories.
Restriction also commutes with inversion and with change of endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumReflection as Reflection
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.CurryingLifting as Lifting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport as Endpoints
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Terms
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskerEquiv

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q
module QA = SumAction W P Q using (reflect; extend-cong; Σ-map; Σ-map-cong)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open WhiskerEquiv T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (preWhisker-lift)

action : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  → S._=₁_ h k → T._=₁_ (flatten h) (flatten k)
action {B} α = W.term α ▷ pair B

action-comparison : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  (α : S._=₁_ h k) → T._=₂_ (Reflection.action W P Q α) (action α)
action-comparison {B} {h = h} {k} α =
  (T.comp-assoc (W.map α) (W.phi h k) (T.preWhisker (pair B)) ▷ W.back) then
  T.comp-assoc W.back (W.phi h k ∘ W.map α) (T.preWhisker (pair B))

reflect-β : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  (α : T._=₁_ (flatten h) (flatten k)) → T._=₂_ (action (QA.reflect α)) α
reflect-β α = (action-comparison (QA.reflect α)) ⁻¹ then Reflection.reflect-β W P Q α

reflect₂ : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  {α β : S._=₁_ h k} → T._=₂_ (action α) (action β) → S._=₂_ α β
reflect₂ {h = h} {k} {α} {β} p = Lifting.Along.reflect W P
  (flatten-family h k) (comparison-isEquiv h k)
  (T.FunctorLift.lift (preWhisker-lift W.back
    (T.equiv-inverse (T.Equiv.isEquiv W.terminal))
    (action-comparison α then p then (action-comparison β) ⁻¹)))

action₂ : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  {α β : S._=₁_ h k} → S._=₂_ α β → T._=₂_ (action α) (action β)
action₂ {B} p = T.preWhisker (pair B) ◁ W.cell2 p

action-comp : {B : T.CAT} {D : S.CAT} {h k j : S.MAP (Σ B) D}
  (β : S._=₁_ k j) (α : S._=₁_ h k)
  → T._=₂_ (action (S._∙_ β α)) (action β ∙ action α)
action-comp {B} β α =
  (T.preWhisker (pair B) ◁ Operations.vertical-term W K β α) then
  preWhisker-isoComp-at (W.term β) (W.term α) (pair B)

action-id : {B : T.CAT} {D : S.CAT} (h : S.MAP (Σ B) D)
  → T._=₂_ (action (S.idIso h)) (T.idIso (flatten h))
action-id {B} h =
  (T.preWhisker (pair B) ◁ OperationCompatibility.identityIso K h) then
  T.preWhisker-idIso (W.map h) (pair B)

action-inverse : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  (α : S._=₁_ h k) → T._=₂_ (action (S._⁻¹ α)) ((action α) ⁻¹)
action-inverse {B} α = (T.preWhisker (pair B) ◁ Terms.Transport.inverse-term W K α) then
  Inverses.pre-inverse T (W.term α) (pair B)

action-endpoints : {B : T.CAT} {D : S.CAT} {h h' k k' : S.MAP (Σ B) D}
  (p : S._=₁_ h h') (q : S._=₁_ k k') (α : S._=₁_ h k)
  → T._=₂_ (action (Endpoints.changeEndpoints S p q α))
    (Endpoints.changeEndpoints T (action p) (action q) (action α))
action-endpoints p q α = action-comp q (S._∙_ α (S._⁻¹ p)) then
  isoComp-cong (T.idIso (action q))
    (action-comp α (S._⁻¹ p) then isoComp-cong (T.idIso (action α)) (action-inverse p))

reflect-cong : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  {α β : T._=₁_ (flatten h) (flatten k)} → T._=₂_ α β
  → S._=₂_ (QA.reflect α) (QA.reflect β)
reflect-cong {α = α} {β} p = reflect₂ (reflect-β α then p then (reflect-β β) ⁻¹)

reflect-comp : {B : T.CAT} {D : S.CAT} {h k j : S.MAP (Σ B) D}
  (β : T._=₁_ (flatten k) (flatten j)) (α : T._=₁_ (flatten h) (flatten k))
  → S._=₂_ (QA.reflect (β ∙ α)) (S._∙_ (QA.reflect β) (QA.reflect α))
reflect-comp β α = reflect₂ (reflect-β (β ∙ α) then
  isoComp-cong ((reflect-β β) ⁻¹) ((reflect-β α) ⁻¹) then
  (action-comp (QA.reflect β) (QA.reflect α)) ⁻¹)

reflect-id : {B : T.CAT} {D : S.CAT} (h : S.MAP (Σ B) D)
  → S._=₂_ (QA.reflect (T.idIso (flatten h))) (S.idIso h)
reflect-id h = reflect₂ (reflect-β (T.idIso (flatten h)) then (action-id h) ⁻¹)

extend-cong-image : {B : T.CAT} {D : S.CAT} {f g : T.MAP B (W.cat D)}
  (α : T._=₁_ f g) → T._=₂_ (action (QA.extend-cong α))
    ((extend-β f) ⁻¹ then α then extend-β g)
extend-cong-image {f = f} {g} α = reflect-β ((extend-β f) ⁻¹ then α then extend-β g)

extend-β-natural : {B : T.CAT} {D : S.CAT} {f g : T.MAP B (W.cat D)}
  (α : T._=₁_ f g)
  → T._=₂_ (extend-β g ∙ α) (action (QA.extend-cong α) ∙ extend-β f)
extend-β-natural {f = f} {g} α = Endpoints.changeEndpoints-to-square T
  (extend-β f) (extend-β g) α (action (QA.extend-cong α)) ((extend-cong-image α) ⁻¹)

sum-cong-image : {B C : T.CAT} {f g : T.MAP B C} (α : T._=₁_ f g)
  → T._=₂_ (action (QA.Σ-map-cong α))
    ((extend-β (pair C ∘ f)) ⁻¹ then (pair C ◁ α) then extend-β (pair C ∘ g))
sum-cong-image {C = C} α = extend-cong-image (pair C ◁ α)

sum-β-natural : {B C : T.CAT} {f g : T.MAP B C} (α : T._=₁_ f g)
  → T._=₂_ (extend-β (pair C ∘ g) ∙ (pair C ◁ α))
      (action (QA.Σ-map-cong α) ∙ extend-β (pair C ∘ f))
sum-β-natural {C = C} α = extend-β-natural (pair C ◁ α)

extend-cong-cong : {B : T.CAT} {D : S.CAT} {f g : T.MAP B (W.cat D)}
  {α β : T._=₁_ f g} → T._=₂_ α β → S._=₂_ (QA.extend-cong α) (QA.extend-cong β)
extend-cong-cong {f = f} {g} {α} {β} p = reflect₂
  (extend-cong-image α then Endpoints.changeEndpoints-cong T (extend-β f) (extend-β g) p then
    (extend-cong-image β) ⁻¹)

extend-cong-comp : {B : T.CAT} {D : S.CAT} {f g h : T.MAP B (W.cat D)}
  (β : T._=₁_ g h) (α : T._=₁_ f g)
  → S._=₂_ (QA.extend-cong (β ∙ α)) (S._∙_ (QA.extend-cong β) (QA.extend-cong α))
extend-cong-comp {f = f} {g} {h} β α = reflect₂
  (extend-cong-image (β ∙ α) then
    (Endpoints.changeEndpoints-comp T (extend-β f) (extend-β g) (extend-β h) β α) ⁻¹ then
    isoComp-cong ((extend-cong-image β) ⁻¹) ((extend-cong-image α) ⁻¹) then
    (action-comp (QA.extend-cong β) (QA.extend-cong α)) ⁻¹)

extend-cong-id : {B : T.CAT} {D : S.CAT} (f : T.MAP B (W.cat D))
  → S._=₂_ (QA.extend-cong (T.idIso f)) (S.idIso (extend f))
extend-cong-id f = reflect₂
  (extend-cong-image (T.idIso f) then Endpoints.changeEndpoints-id T (extend-β f) then
    (action-id (extend f)) ⁻¹)

sum-cong-comp : {B C : T.CAT} {f g h : T.MAP B C}
  (β : T._=₁_ g h) (α : T._=₁_ f g)
  → S._=₂_ (QA.Σ-map-cong (β ∙ α)) (S._∙_ (QA.Σ-map-cong β) (QA.Σ-map-cong α))
sum-cong-comp {C = C} β α = S._∙_
  (extend-cong-comp (pair C ◁ β) (pair C ◁ α))
  (extend-cong-cong (postWhisker-isoComp-at (pair C) β α))

sum-cong-id : {B C : T.CAT} (f : T.MAP B C)
  → S._=₂_ (QA.Σ-map-cong (T.idIso f)) (S.idIso (QA.Σ-map f))
sum-cong-id {C = C} f = S._∙_ (extend-cong-id (pair C ∘ f))
  (extend-cong-cong (T.postWhisker-idIso (pair C) f))
```
