# Restricting a diagram at a vertex

The insertion comparison below is the product comparison used literally in
`evaluate-pre`. Its composition law retains the associator of the vertex
and both specified product projections. This is the product calculation
needed when evaluating a face of the universal degenerate triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductRestrictionAssociativity 𝒯 M
  using (module Coordinates; constant-normalization)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductCompositionAssociativity 𝒯 M
  using (module CoordinateAssociativity)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (module PairingAssembly)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp; pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at; preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

insertion : {A B : CAT} (X : CAT) (f : MAP A B) (x : Obj-abs A) →
  (productMap (id X) f ∘ insert x) =₁ (insert (f ∘ x))
insertion X f x =
  pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x f) ⁻¹) ∙
    productMap-pair (id X) f (id X) (const x)

module At {A B : CAT} (X : CAT) (f : MAP A B) (x : Obj-abs A) where
  i = insert {X = X} x
  first : ((id X ∘ pr₁) ∘ i) =₁ (id X)
  first = comp-unitˡ (id X) ∙
    ((id X ◁ pair-β₁ (id X) (const x)) ∙ comp-assoc i pr₁ (id X))
  second : ((f ∘ pr₂) ∘ i) =₁ (const (f ∘ x))
  second = (comp-assoc (terminate X) x f) ⁻¹ ∙
    ((f ◁ pair-β₂ (id X) (const x)) ∙ comp-assoc i pr₂ f)
  normalized = pair-cong first second ∙ pair-pre (id X ∘ pr₁) (f ∘ pr₂) i

  normalization : (insertion X f x) =₂ normalized
  normalization = isoComp-cong
    ((pair-cong-comp (comp-unitˡ (id X))
      ((id X ◁ pair-β₁ (id X) (const x)) ∙ comp-assoc i pr₁ (id X))
      ((comp-assoc (terminate X) x f) ⁻¹)
      ((f ◁ pair-β₂ (id X) (const x)) ∙ comp-assoc i pr₂ f)) ⁻¹)
    (idIso (pair-pre (id X ∘ pr₁) (f ∘ pr₂) i)) ∙
    (isoComp-assoc-at
      (pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x f) ⁻¹))
      _ _) ⁻¹

  first-normalization : first =₂
    (pair-β₁ (id X) (const x) ∙ (comp-unitˡ pr₁ ▷ i))
  first-normalization = isoComp-cong (idIso (pair-β₁ (id X) (const x)))
    (left-unitor-comp i pr₁) ∙
    (isoComp-assoc-at (pair-β₁ (id X) (const x)) (comp-unitˡ (pr₁ ∘ i)) (comp-assoc i pr₁ (id X)) ∙
    (isoComp-cong (postWhisker-id-at (pair-β₁ (id X) (const x))) (idIso (comp-assoc i pr₁ (id X))) ∙
      (isoComp-assoc-at (comp-unitˡ (id X)) (id X ◁ pair-β₁ (id X) (const x))
        (comp-assoc i pr₁ (id X))) ⁻¹))

  projection₁ :
    (pair-β₁ (id X) (const (f ∘ x)) ∙ (pr₁ ◁ insertion X f x)) =₂
    (first ∙ ((pair-β₁ (id X ∘ pr₁) (f ∘ pr₂) ▷ i) ∙
      (comp-assoc i (productMap (id X) f) pr₁) ⁻¹))
  projection₁ = pair-pre-cong-triangle₁ (id X ∘ pr₁) (f ∘ pr₂) i first second ∙
    isoComp-cong (idIso (pair-β₁ (id X) (const (f ∘ x)))) (postWhisker pr₁ ◁ normalization)

  projection₂ :
    (pair-β₂ (id X) (const (f ∘ x)) ∙ (pr₂ ◁ insertion X f x)) =₂
    (second ∙ ((pair-β₂ (id X ∘ pr₁) (f ∘ pr₂) ▷ i) ∙
      (comp-assoc i (productMap (id X) f) pr₂) ⁻¹))
  projection₂ = pair-pre-cong-triangle₂ (id X ∘ pr₁) (f ∘ pr₂) i first second ∙
    isoComp-cong (idIso (pair-β₂ (id X) (const (f ∘ x)))) (postWhisker pr₂ ◁ normalization)

module Successive {A B D : CAT} (X : CAT)
  (x : Obj-abs A) (f : MAP A B) (g : MAP B D) where
  s = productMap (id X) f
  t = insert {X = X} x
  st = insert {X = X} (f ∘ x)
  κ = insertion X f x
  q : MAP (X × B) X
  q = id X ∘ pr₁
  v : q =₁ pr₁
  v = comp-unitˡ pr₁
  b : (pr₁ ∘ s) =₁ (id X ∘ pr₁)
  b = pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)
  bst = pair-β₁ (id X) (const (f ∘ x))
  S = Coordinates.first X g f
  T = At.first X (g ∘ f) x
  Aq = comp-assoc t s q
  Aπ = comp-assoc t s pr₁
  vv = (v ▷ s) ▷ t
  normalized = T ∙ (S ▷ t)

  first-coordinate :
    (At.first X g (f ∘ x) ∙ ((q ◁ κ) ∙ Aq)) =₂ (idIso (id X) ∙ normalized)
  first-coordinate =
    let
      leftStart :
        (At.first X g (f ∘ x) ∙ ((q ◁ κ) ∙ Aq)) =₂
        ((bst ∙ (pr₁ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq))
      leftStart = (isoComp-assoc-at bst (pr₁ ◁ κ) ((v ▷ (s ∘ t)) ∙ Aq)) ⁻¹ ∙
        (isoComp-cong (idIso bst) (isoComp-assoc-at (pr₁ ◁ κ) (v ▷ (s ∘ t)) Aq) ∙
        (isoComp-cong (idIso bst) (isoComp-cong (interchange-at v κ) (idIso Aq)) ∙
        (reassociateFour bst (v ▷ st) (q ◁ κ) Aq ∙
          isoComp-cong (At.first-normalization X g (f ∘ x)) (idIso ((q ◁ κ) ∙ Aq)))))

      middle :
        ((bst ∙ (pr₁ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq)) =₂
        ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv))
      middle = isoComp-cong (At.projection₁ X f x)
        ((preWhisker-comp-at v s t) ⁻¹)

      cancellation :
        ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv)) =₂
        (T ∙ ((b ▷ t) ∙ vv))
      cancellation = isoComp-cong (idIso T)
          (isoComp-cong (idIso (b ▷ t))
            (isoComp-unitˡ-at vv ∙
              (isoComp-cong (isoComp-inverseˡ-at Aπ) (idIso vv) ∙
                (isoComp-assoc-at (Aπ ⁻¹) Aπ vv) ⁻¹)) ∙
            isoComp-assoc-at (b ▷ t) (Aπ ⁻¹) (Aπ ∙ vv)) ∙
        isoComp-assoc-at T ((b ▷ t) ∙ Aπ ⁻¹) (Aπ ∙ vv)

      rightFinish : (T ∙ ((b ▷ t) ∙ vv)) =₂ normalized
      rightFinish = isoComp-cong (idIso T)
        ((preWhisker t ◁ (constant-normalization X g f) ⁻¹) ∙
          (preWhisker-isoComp-at b (v ▷ s) t) ⁻¹)

      insertIdentity : normalized =₂ (idIso (id X) ∙ normalized)
      insertIdentity =
        (isoComp-unitˡ-at normalized) ⁻¹
    in insertIdentity ∙ (rightFinish ∙ (cancellation ∙ (middle ∙ leftStart)))


  second-coordinate :
    (At.second X g (f ∘ x) ∙
      (((g ∘ pr₂) ◁ κ) ∙ comp-assoc t s (g ∘ pr₂))) =₂
    ((comp-assoc x f g ▷ terminate X) ∙
      (At.second X (g ∘ f) x ∙ (Coordinates.second X g f ▷ t)))
  second-coordinate = CoordinateAssociativity.comparison
    (terminate X) pr₂ pr₂ x f g s t st κ
    (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂))
    (pair-β₂ (id X) (const x)) (pair-β₂ (id X) (const (f ∘ x)))
    (At.projection₂ X f x)

  abstract
    law :
      (insertion X g (f ∘ x) ∙
        ((productMap (id X) g ◁ insertion X f x) ∙ comp-assoc t s (productMap (id X) g))) =₂
      (pair-cong (idIso (id X)) (comp-assoc x f g ▷ terminate X) ∙
        (insertion X (g ∘ f) x ∙ (productRestriction-comp X f g ▷ t)))
    law = isoComp-cong (idIso (pair-cong (idIso (id X)) (comp-assoc x f g ▷ terminate X)))
        (isoComp-cong ((At.normalization X (g ∘ f) x) ⁻¹)
          (preWhisker t ◁ (Coordinates.normalization X g f) ⁻¹)) ∙
      (PairingAssembly.assemble (id X ∘ pr₁) (g ∘ pr₂) s t st κ
        S (Coordinates.second X g f) T (At.second X (g ∘ f) x)
        (At.first X g (f ∘ x)) (At.second X g (f ∘ x))
        (idIso (id X)) (comp-assoc x f g ▷ terminate X)
        first-coordinate second-coordinate ∙
      isoComp-cong (At.normalization X g (f ∘ x))
        (idIso ((productMap (id X) g ◁ κ) ∙ comp-assoc t s (productMap (id X) g))))
```


Applying evaluation to this product equation retains the three external
associators. This proves the comparison between the two product-evaluation
routes. `RestrictionParameterEvaluation` proves compatibility with family
restriction, and `RestrictionEndpointComposition` identifies the resulting
routes with the restrictions of `evaluate-pre`.

```agda
open import SCT.VolumeI.Chapter01.Section04.Substitution.IteratedCompatibility 𝒯 M
  using (evaluation-step; evaluation-step-iterated)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairNaturality
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pre-inverse-at; solve-pentagon)
open PairNaturality vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)

module Evaluated {A B D Z : CAT} (X : CAT)
  (x : Obj-abs A) (f : MAP A B) (g : MAP B D) (e : MAP (X × D) Z) where
  t = insert {X = X} x
  s = productMap (id X) f
  p = productMap (id X) g
  st = insert {X = X} (f ∘ x)
  ps = productMap (id X) (g ∘ f)
  κ01 = insertion X f x
  κ12 = productRestriction-comp X f g
  κ012-left = insertion X (g ∘ f) x
  κ012-right = insertion X g (f ∘ x)
  associator = pair-cong (idIso (id X)) (comp-assoc x f g ▷ terminate X)
  firstStep = evaluation-step e p s (κ12 ⁻¹)
  secondStep = evaluation-step e ps t (κ012-left ⁻¹)
  combinedStep = evaluation-step e p st (κ012-right ⁻¹)
  together = combinedStep ∙ (e ◁ associator)
  successively = ((e ∘ p) ◁ κ01) ∙
    (comp-assoc t s (e ∘ p) ∙ ((firstStep ▷ t) ∙ secondStep))
  abstract
    law : together =₂ successively
    law =
      (let a = κ12 ⁻¹
           b = κ012-left ⁻¹
           inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
           outside = (comp-assoc st p e) ⁻¹
           middle = (comp-assoc (s ∘ t) p e) ⁻¹
           whiskered-κ = p ◁ κ01
           commute = (move-square (comp-assoc st p e)
             ((e ∘ p) ◁ κ01) (e ◁ whiskered-κ) (comp-assoc (s ∘ t) p e)
             (postWhisker-comp-at κ01 p e)) ⁻¹
           solve = solve-pentagon κ012-right
             (whiskered-κ ∙ comp-assoc t s p) associator κ012-left (κ12 ▷ t) (Successive.law X x f g) ∙
             ((isoComp-assoc-at whiskered-κ (comp-assoc t s p) ((κ12 ▷ t) ⁻¹ ∙ b)) ⁻¹ ∙
              isoComp-cong (idIso whiskered-κ)
                (isoComp-cong (idIso (comp-assoc t s p))
                  (isoComp-cong (pre-inverse-at κ12 t) (idIso b))))
       in (isoComp-assoc-at outside (e ◁ κ012-right ⁻¹) (e ◁ associator)) ⁻¹ ∙
         (isoComp-cong (idIso outside) (postWhisker-isoComp-at e (κ012-right ⁻¹) associator) ∙
         (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
         (isoComp-cong (idIso outside) ((postWhisker-isoComp-at e whiskered-κ inner) ⁻¹) ∙
         (isoComp-assoc-at outside (e ◁ whiskered-κ) (e ◁ inner) ∙
         (isoComp-cong commute (idIso (e ◁ inner)) ∙
         ((isoComp-assoc-at ((e ∘ p) ◁ κ01) middle (e ◁ inner)) ⁻¹ ∙
           isoComp-cong (idIso ((e ∘ p) ◁ κ01))
             (evaluation-step-iterated e p s t a b)))))))) ⁻¹
```
