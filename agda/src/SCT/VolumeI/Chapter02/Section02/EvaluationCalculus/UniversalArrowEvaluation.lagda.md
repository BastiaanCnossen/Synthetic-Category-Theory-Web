# Evaluating the universal arrow

The universal arrow is the identity of `Ar C`. Its endpoint frames are the
external right unitors. The calculation below compares those frames with
evaluation of its uncurried diagram, retaining the chosen product unitor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.UniversalArrowEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where


open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-Iso₂; pair-cong-triangle₁; pair-cong-triangle₂)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-right; project-composite; pre-square-projection; move-square)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-id; preWhisker-id-reflect; triangle-whiskered; right-unitor-comp)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp; pair-pre-cong-triangle₁; pair-pre-cong-triangle₂;
    productMap-id-triangle₁; productMap-id-triangle₂)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at; whisker-mixed-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse; reassociateFour)

abstract
  identity-unitors : (X : CAT) → (comp-unitˡ (id X)) =₂ (comp-unitʳ (id X))
  identity-unitors X = preWhisker-id-reflect
    ((triangle-whiskered (id X) (id X)) ⁻¹ ∙
      (isoComp-cong ((cancel-left-reflect (comp-unitˡ (id X))
        (postWhisker-id-at (comp-unitˡ (id X)))) ⁻¹) (idIso (comp-assoc (id X) (id X) (id X))) ∙
        (left-unitor-comp (id X) (id X)) ⁻¹))

  constant-identity : {X A : CAT} (x : Obj-abs A) →
    (const-pre x (id X)) =₂ (comp-unitʳ (const x))
  constant-identity {X} x = (right-unitor-comp (terminate X) x) ⁻¹ ∙
    isoComp-cong (postWhisker x ◁ terminal-Iso₂
      (terminal-iso (terminate X ∘ id X) (terminate X)) (comp-unitʳ (terminate X)))
      (idIso (comp-assoc (id X) (terminate X) x))

unit-pair-projection : {R K A : CAT} (π : MAP K A) (h h′ : MAP R K)
  (J : MAP K K) (δ : J =₁ (id K)) (u : MAP R A)
  (b : (π ∘ h) =₁ u) (b′ : (π ∘ h′) =₁ (id A ∘ u))
  (bJ : (π ∘ J) =₁ (id A ∘ π))
  (out : h′ =₁ h) (step : (J ∘ h) =₁ h′) →
  (comp-unitʳ π ∙ (π ◁ δ)) =₂ (comp-unitˡ π ∙ bJ) →
  (b ∙ (π ◁ out)) =₂ (comp-unitˡ u ∙ b′) →
  (b′ ∙ (π ◁ step)) =₂
    (((id A ◁ b) ∙ comp-assoc h π (id A)) ∙
      ((bJ ▷ h) ∙ (comp-assoc h J π) ⁻¹)) →
  (π ◁ (out ∙ step)) =₂ (π ◁ (comp-unitˡ h ∙ (δ ▷ h)))
unit-pair-projection {A = A} π h h′ J δ u b b′ bJ out step unit-triangle out-triangle step-triangle =
  let transport = (bJ ▷ h) ∙ (comp-assoc h J π) ⁻¹
      e = (id A ◁ b) ∙ comp-assoc h π (id A)
      coordinate : (comp-unitˡ u ∙ e) =₂ (b ∙ (comp-unitˡ π ▷ h))
      coordinate = isoComp-cong (idIso b) (left-unitor-comp h π) ∙
        (isoComp-assoc-at b (comp-unitˡ (π ∘ h)) (comp-assoc h π (id A)) ∙
        (isoComp-cong (postWhisker-id-at b) (idIso (comp-assoc h π (id A))) ∙
          (isoComp-assoc-at (comp-unitˡ u) (id A ◁ b) (comp-assoc h π (id A))) ⁻¹))
      left-normal = isoComp-assoc-at b (comp-unitˡ π ▷ h) transport ∙
        (isoComp-cong coordinate (idIso transport) ∙
        ((isoComp-assoc-at (comp-unitˡ u) e transport) ⁻¹ ∙
        (isoComp-cong (idIso (comp-unitˡ u)) step-triangle ∙
        (isoComp-assoc-at (comp-unitˡ u) b′ (π ◁ step) ∙
        (isoComp-cong out-triangle (idIso (π ◁ step)) ∙
          project-composite π out step b)))))
      assoc = comp-assoc h (id _) π
      triangle-solved =
        (cancel-right assoc (π ◁ comp-unitˡ h) ∙
          isoComp-cong (triangle-whiskered h π) (idIso (assoc ⁻¹))) ⁻¹
      pre-square = pre-square-projection π δ (comp-unitˡ π) bJ (comp-unitʳ π) h unit-triangle
      right-normal = isoComp-cong (idIso b)
        (pre-square ∙ isoComp-cong triangle-solved (idIso (π ◁ (δ ▷ h)))) ∙
        (isoComp-assoc-at b (π ◁ comp-unitˡ h) (π ◁ (δ ▷ h)) ∙
          project-composite π (comp-unitˡ h) (δ ▷ h) b)
  in cancel-left-reflect b (right-normal ⁻¹ ∙ left-normal)

abstract
  product-pair-unit : {R A B : CAT} (u : MAP R A) (v : MAP R B) →
    (pair-cong (comp-unitˡ u) (comp-unitˡ v) ∙ productMap-pair (id A) (id B) u v) =₂
    (comp-unitˡ (pair u v) ∙ (productMap-id A B ▷ pair u v))
  product-pair-unit {R} {A} {B} u v = pair-iso-extensionality
    (unit-pair-projection pr₁ h h′ J δ u
      (pair-β₁ u v) (pair-β₁ (id A ∘ u) (id B ∘ v)) (pair-β₁ (id A ∘ pr₁) (id B ∘ pr₂))
      out step (productMap-id-triangle₁ A B)
      (pair-cong-triangle₁ (comp-unitˡ u) (comp-unitˡ v))
      (pair-pre-cong-triangle₁ (id A ∘ pr₁) (id B ∘ pr₂) h first second))
    (unit-pair-projection pr₂ h h′ J δ v
      (pair-β₂ u v) (pair-β₂ (id A ∘ u) (id B ∘ v)) (pair-β₂ (id A ∘ pr₁) (id B ∘ pr₂))
      out step (productMap-id-triangle₂ A B)
      (pair-cong-triangle₂ (comp-unitˡ u) (comp-unitˡ v))
      (pair-pre-cong-triangle₂ (id A ∘ pr₁) (id B ∘ pr₂) h first second))
    where
    h : MAP R (A × B)
    h = pair u v
    h′ : MAP R (A × B)
    h′ = pair (id A ∘ u) (id B ∘ v)
    J : MAP (A × B) (A × B)
    J = productMap (id A) (id B)
    δ : J =₁ (id (A × B))
    δ = productMap-id A B
    out : h′ =₁ h
    out = pair-cong (comp-unitˡ u) (comp-unitˡ v)
    step : (J ∘ h) =₁ h′
    step = productMap-pair (id A) (id B) u v
    first : ((id A ∘ pr₁) ∘ h) =₁ (id A ∘ u)
    first = (id A ◁ pair-β₁ u v) ∙ comp-assoc h pr₁ (id A)
    second : ((id B ∘ pr₂) ∘ h) =₁ (id B ∘ v)
    second = (id B ◁ pair-β₂ u v) ∙ comp-assoc h pr₂ (id B)

module IdentityInsertion {A : CAT} (X : CAT) (x : Obj-abs A) where
  i = insert {X = X} x
  δ = productMap-id X A
  incoming = pair-cong (comp-unitˡ (id X)) (const-pre x (id X)) ∙ pair-pre (id X) (const x) (id X)
  outgoing = pair-cong (comp-unitʳ (id X)) (comp-unitˡ (const x)) ∙
    productMap-pair (id X) (id A) (id X) (const x)

  abstract
    incoming-unit : incoming =₂ (comp-unitʳ i)
    incoming-unit = pair-pre-id (id X) (const x) ∙
      isoComp-cong (pair-cong-Iso₂ (identity-unitors X) (constant-identity x))
        (idIso (pair-pre (id X) (const x) (id X)))

    outgoing-unit : outgoing =₂ (comp-unitˡ i ∙ (δ ▷ i))
    outgoing-unit = product-pair-unit (id X) (const x) ∙
      isoComp-cong (pair-cong-Iso₂ ((identity-unitors X) ⁻¹) (idIso (comp-unitˡ (const x))))
        (idIso (productMap-pair (id X) (id A) (id X) (const x)))

    law : (comp-unitˡ i ∙ ((δ ▷ i) ∙ insert-natural (id X) x)) =₂ (comp-unitʳ i)
    law = incoming-unit ∙
      (cancel-inverse outgoing incoming ∙
      (isoComp-cong (outgoing-unit ⁻¹) (idIso (insert-natural (id X) x)) ∙
        (isoComp-assoc-at (comp-unitˡ i) (δ ▷ i) (insert-natural (id X) x)) ⁻¹))
```


```agda
module Universal {A C : CAT} (x : Obj-abs A) where
  X = Fun A C
  i = insert {X = X} x
  e = funEval {A} {C}
  K = productMap (id X) (id A)
  δ = productMap-id X A
  n = insert-natural (id X) x
  r = comp-unitʳ e
  assoc = comp-assoc i K e
  identity-assoc = comp-assoc i (id (X × A)) e
  tail = comp-assoc (id X) i e

  abstract
    beta-slide : ((funUncurry-id A C ▷ i) ∙ assoc ⁻¹) =₂
      ((e ◁ comp-unitˡ i) ∙ (e ◁ (δ ▷ i)))
    beta-slide = isoComp-cong
        (cancel-right identity-assoc (e ◁ comp-unitˡ i) ∙
          isoComp-cong (triangle-whiskered i e) (idIso (identity-assoc ⁻¹)))
        (idIso (e ◁ (δ ▷ i))) ∙
      ((isoComp-assoc-at (r ▷ i) (identity-assoc ⁻¹) (e ◁ (δ ▷ i))) ⁻¹ ∙
      (isoComp-cong (idIso (r ▷ i))
        ((move-square identity-assoc ((e ◁ δ) ▷ i) (e ◁ (δ ▷ i)) assoc
          (whisker-mixed-at δ i e)) ⁻¹) ∙
      (isoComp-assoc-at (r ▷ i) ((e ◁ δ) ▷ i) (assoc ⁻¹) ∙
        isoComp-cong (preWhisker-isoComp-at r (e ◁ δ) i) (idIso (assoc ⁻¹)))))

    finish :
      (((e ◁ comp-unitˡ i) ∙ (e ◁ (δ ▷ i))) ∙ ((e ◁ n) ∙ tail)) =₂
        (comp-unitʳ (evaluate {C = C} x))
    finish = (right-unitor-comp i e) ⁻¹ ∙
      (isoComp-cong (postWhisker e ◁ IdentityInsertion.law X x) (idIso tail) ∙
      (isoComp-cong
        ((postWhisker-isoComp-at e (comp-unitˡ i) ((δ ▷ i) ∙ n)) ⁻¹ ∙
          isoComp-cong (idIso (e ◁ comp-unitˡ i))
            ((postWhisker-isoComp-at e (δ ▷ i) n) ⁻¹)) (idIso tail) ∙
      ((isoComp-assoc-at (e ◁ comp-unitˡ i) ((e ◁ (δ ▷ i)) ∙ (e ◁ n)) tail) ⁻¹ ∙
        reassociateFour (e ◁ comp-unitˡ i) (e ◁ (δ ▷ i)) (e ◁ n) tail)))

    endpoint :
      ((funUncurry-id A C ▷ i) ∙ evaluate-uncurry x (id X)) =₂
        (comp-unitʳ (evaluate {C = C} x))
    endpoint = finish ∙
      (isoComp-cong beta-slide (idIso ((e ◁ n) ∙ tail)) ∙
        (isoComp-assoc-at (funUncurry-id A C ▷ i) (assoc ⁻¹) ((e ◁ n) ∙ tail)) ⁻¹)
```
