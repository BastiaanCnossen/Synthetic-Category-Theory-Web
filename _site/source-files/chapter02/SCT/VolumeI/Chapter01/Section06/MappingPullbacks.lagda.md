# Mapping animae preserve and detect pullback squares

The mapped cone is the specified evaluation followed by currying. Its
complete matching remains part of the construction. Currying and reflection
use an anima witness for the categorical term source; uncurrying and
restriction do not. Detection tests every categorical T.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.MappingPullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; product-unitʳ-inverse; product-unitʳ-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; changeEndpoints-iterated; transport-square;
    reflect-transported-square; restore-boundaries)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-transport; equiv-compose; equiv-cancel-left)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (factor-through-preWhisker)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
  using (Map; map-isAn; mapEval; uncurry; mapCurry; mapCurry-β)
open import SCT.VolumeI.Chapter01.Section04.Currying
  using (uncurry⁼; uncurry⁼-cong; uncurry⁼-composition; uncurry⁼-identity;
    uncurry-reflect; uncurry-reflect-β; uncurry⁼-reflect; uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section04.Functoriality
  using (mapPost; mapPost-β; mapPost-uncurry; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
  using (mapPost-uncurry-inputs; mapPost-uncurry-restrict; uncurry-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection using (post-tests-all)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
  using (cone-change-legs; cone-change-legs-β; cone-retarget-match-identification)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  private
    module _ {A C D X : CAT Γ} where
      open Terms.InContext A using (Term)
      open Terms.Equalities X using (_＝_)

      uncurry⁼-inverse : {x y : Term (Map C D)} (α : x ＝ y)
        → uncurry⁼ (α ⁻¹) =₁ ((uncurry⁼ α) ⁻¹)
      uncurry⁼-inverse {x = x} α =
        (inverse-unique (uncurry⁼ α) (uncurry⁼ (α ⁻¹))
          (uncurry⁼-identity x ∙
            (uncurry⁼-cong (comp₌-inverseˡ α) ∙
              (uncurry⁼-composition (α ⁻¹) α) ⁻¹))) ⁻¹

    replace-cone-identification : {C D E X : CAT Γ}
      {f : MAP C E} {g : MAP D E} {s t : Cone f g X}
      (Φ : ConeIdentification₁ s t)
      (α : Cone.left s =₁ Cone.left t) (β : Cone.right s =₁ Cone.right t)
      → ConeIdentification₁.left Φ =₂ α → ConeIdentification₁.right Φ =₂ β
      → ConeIdentification₁ s t
    replace-cone-identification {f = f} {g} Φ α β p q = record
      { left = α; right = β
      ; compatible = replace-edges₌ (postWhisker f ◁ p) (postWhisker g ◁ q)
          (ConeIdentification₁.compatible Φ) }
```

## Uncurrying and currying cones

The four actual postcomposition comparisons transport the matching square.
CurriedCone retains the chosen legs, reflected matching and complete
uncurrying law. ReflectedCone uses the specified images of its recovered
legs before reflecting full compatibility.

```agda
  uncurry-cone : {X T C D E : CAT Γ} {f : MAP C E} {g : MAP D E} →
    Cone (mapPost {C = T} f) (mapPost g) X → Cone f g (X × T)
  uncurry-cone {f = f} {g} s = record
    { left = uncurry (Cone.left s) ; right = uncurry (Cone.right s)
    ; match = mapPost-uncurry g (Cone.right s) ∙
        (uncurry⁼ (Cone.match s) ∙ (mapPost-uncurry f (Cone.left s)) ⁻¹) }

  uncurry-cone-identification : {X T C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone (mapPost {C = T} f) (mapPost g) X} → ConeIdentification₁ s t → ConeIdentification₁ (uncurry-cone s) (uncurry-cone t)
  uncurry-cone-identification {X} {T} {C} {D} {E} {f} {g} {s} {t} Φ = record
    { left = uncurry⁼ α ; right = uncurry⁼ β
    ; compatible = transport-square fs ft gs gt τs τt raw-left raw-right native-left native-right
        (unconst-sides₌ (mapPost-uncurry-inputs f α)) (unconst-sides₌ (mapPost-uncurry-inputs g β)) rawSquare }
    where
    α : (Cone.left s) =₁ (Cone.left t)
    α = ConeIdentification₁.left Φ
    β : (Cone.right s) =₁ (Cone.right t)
    β = ConeIdentification₁.right Φ
    fs : (uncurry (mapPost f ∘ Cone.left s)) =₁ (f ∘ uncurry (Cone.left s))
    fs = mapPost-uncurry f (Cone.left s)
    ft : (uncurry (mapPost f ∘ Cone.left t)) =₁ (f ∘ uncurry (Cone.left t))
    ft = mapPost-uncurry f (Cone.left t)
    gs : (uncurry (mapPost g ∘ Cone.right s)) =₁ (g ∘ uncurry (Cone.right s))
    gs = mapPost-uncurry g (Cone.right s)
    gt : (uncurry (mapPost g ∘ Cone.right t)) =₁ (g ∘ uncurry (Cone.right t))
    gt = mapPost-uncurry g (Cone.right t)
    τs : (uncurry (mapPost f ∘ Cone.left s)) =₁ (uncurry (mapPost g ∘ Cone.right s))
    τs = uncurry⁼ (Cone.match s)
    τt : (uncurry (mapPost f ∘ Cone.left t)) =₁ (uncurry (mapPost g ∘ Cone.right t))
    τt = uncurry⁼ (Cone.match t)
    native-left : (f ∘ uncurry (Cone.left s)) =₁ (f ∘ uncurry (Cone.left t))
    native-left = f ◁ uncurry⁼ α
    raw-left : (uncurry (mapPost f ∘ Cone.left s)) =₁ (uncurry (mapPost f ∘ Cone.left t))
    raw-left = uncurry⁼ (mapPost f ◁ α)
    raw-right : (uncurry (mapPost g ∘ Cone.right s)) =₁ (uncurry (mapPost g ∘ Cone.right t))
    raw-right = uncurry⁼ (mapPost g ◁ β)
    native-right : (g ∘ uncurry (Cone.right s)) =₁ (g ∘ uncurry (Cone.right t))
    native-right = g ◁ uncurry⁼ β
    rawSquare : (τt ∙ raw-left) =₂ (raw-right ∙ τs)
    rawSquare = uncurry⁼-composition (mapPost g ◁ β) (Cone.match s) ∙
      ((uncurry⁼-cong (ConeIdentification₁.compatible Φ)) ∙
        (uncurry⁼-composition (Cone.match t) (mapPost f ◁ α)) ⁻¹)

  module CurriedCone {X T C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    (xAn : isAn X) (s : Cone f g (X × T)) where

    left : MAP X (Map T C)
    left = mapCurry xAn (Cone.left s)
    right : MAP X (Map T D)
    right = mapCurry xAn (Cone.right s)
    left-β : (uncurry left) =₁ (Cone.left s)
    left-β = mapCurry-β xAn (Cone.left s)
    right-β : (uncurry right) =₁ (Cone.right s)
    right-β = mapCurry-β xAn (Cone.right s)
    wanted : Cone f g (X × T)
    wanted = cone-change-legs s (uncurry left) (uncurry right) (left-β ⁻¹) (right-β ⁻¹)
    desired : (f ∘ uncurry left) =₁ (g ∘ uncurry right)
    desired = Cone.match wanted
    leftChange : (uncurry (mapPost f ∘ left)) =₁ (f ∘ uncurry left)
    leftChange = mapPost-uncurry f left
    rightChange : (uncurry (mapPost g ∘ right)) =₁ (g ∘ uncurry right)
    rightChange = mapPost-uncurry g right
    rawMatch : (uncurry (mapPost f ∘ left)) =₁ (uncurry (mapPost g ∘ right))
    rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

    value : Cone (mapPost f) (mapPost g) X
    value = record
      { left = left ; right = right
      ; match = uncurry-reflect xAn _ _ rawMatch }

    match-β : (Cone.match (uncurry-cone value)) =₂ desired
    match-β = restore-boundaries leftChange rightChange desired
      (uncurry⁼ (Cone.match value))
      (uncurry-reflect-β xAn _ _ rawMatch)

    abstract
      uncurry-law : ConeIdentification₁ (uncurry-cone value) s
      uncurry-law = cone-compose
        (cone-inverse (cone-change-legs-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
        (cone-retarget-match-identification (uncurry-cone value) desired match-β)

  module ReflectedCone {X T C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    (xAn : isAn X) (s t : Cone (mapPost {C = T} f) (mapPost g) X)
    (Φ : ConeIdentification₁ (uncurry-cone s) (uncurry-cone t)) where

    left : (Cone.left s) =₁ (Cone.left t)
    left = uncurry-reflect xAn _ _ (ConeIdentification₁.left Φ)
    right : (Cone.right s) =₁ (Cone.right t)
    right = uncurry-reflect xAn _ _ (ConeIdentification₁.right Φ)
    adjusted : ConeIdentification₁ (uncurry-cone s) (uncurry-cone t)
    adjusted = replace-cone-identification Φ (uncurry⁼ left) (uncurry⁼ right)
      ((uncurry-reflect-β xAn _ _ (ConeIdentification₁.left Φ)) ⁻¹)
      ((uncurry-reflect-β xAn _ _ (ConeIdentification₁.right Φ)) ⁻¹)
    fs : (uncurry (mapPost f ∘ Cone.left s)) =₁ (f ∘ uncurry (Cone.left s))
    fs = mapPost-uncurry f (Cone.left s)
    ft : (uncurry (mapPost f ∘ Cone.left t)) =₁ (f ∘ uncurry (Cone.left t))
    ft = mapPost-uncurry f (Cone.left t)
    gs : (uncurry (mapPost g ∘ Cone.right s)) =₁ (g ∘ uncurry (Cone.right s))
    gs = mapPost-uncurry g (Cone.right s)
    gt : (uncurry (mapPost g ∘ Cone.right t)) =₁ (g ∘ uncurry (Cone.right t))
    gt = mapPost-uncurry g (Cone.right t)
    τs : (uncurry (mapPost f ∘ Cone.left s)) =₁ (uncurry (mapPost g ∘ Cone.right s))
    τs = uncurry⁼ (Cone.match s)
    τt : (uncurry (mapPost f ∘ Cone.left t)) =₁ (uncurry (mapPost g ∘ Cone.right t))
    τt = uncurry⁼ (Cone.match t)
    α : (uncurry (mapPost f ∘ Cone.left s)) =₁ (uncurry (mapPost f ∘ Cone.left t))
    α = uncurry⁼ (mapPost f ◁ left)
    β : (uncurry (mapPost g ∘ Cone.right s)) =₁ (uncurry (mapPost g ∘ Cone.right t))
    β = uncurry⁼ (mapPost g ◁ right)

    rawSquare : (τt ∙ α) =₂ (β ∙ τs)
    rawSquare = reflect-transported-square fs gs ft gt τs τt
      α β (f ◁ uncurry⁼ left) (g ◁ uncurry⁼ right)
      (unconst-sides₌ (mapPost-uncurry-inputs f left)) (unconst-sides₌ (mapPost-uncurry-inputs g right))
      (ConeIdentification₁.compatible adjusted)

    identification : ConeIdentification₁ s t
    identification = record
      { left = left ; right = right
      ; compatible = uncurry⁼-reflect xAn _ _
          ((uncurry⁼-composition (mapPost g ◁ right) (Cone.match s)) ⁻¹ ∙
            (rawSquare ∙ uncurry⁼-composition (Cone.match t) (mapPost f ◁ left))) }
```

## Restriction of uncurried cones

Both leg comparisons are the selected uncurrying restriction. Their full
matching square uses the actual postcomposition restriction routes and the
uncurrying input square. Intermediate endpoint normalizations are explicit.

```agda
  module UncurriedRestriction {X Y T C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) where

    p : MAP X (Map T C)
    p = Cone.left s
    q : MAP X (Map T D)
    q = Cone.right s
    F : MAP (Map T C) (Map T E)
    F = mapPost {C = T} f
    G : MAP (Map T D) (Map T E)
    G = mapPost {C = T} g
    τ : (F ∘ p) =₁ (G ∘ q)
    τ = Cone.match s
    R : MAP (Y × T) (X × T)
    R = productMap r (id T)
    af : ((F ∘ p) ∘ r) =₁ (F ∘ (p ∘ r))
    af = comp-assoc r p F
    ag : ((G ∘ q) ∘ r) =₁ (G ∘ (q ∘ r))
    ag = comp-assoc r q G
    bf : (uncurry ((F ∘ p) ∘ r)) =₁ (uncurry (F ∘ p) ∘ R)
    bf = uncurry-restrict {C = T} {D = E} (F ∘ p) r
    bg : (uncurry ((G ∘ q) ∘ r)) =₁ (uncurry (G ∘ q) ∘ R)
    bg = uncurry-restrict {C = T} {D = E} (G ∘ q) r
    Ef : (uncurry ((F ∘ p) ∘ r)) =₁ (f ∘ uncurry (p ∘ r))
    Ef = mapPost-uncurry {C = T} f (p ∘ r) ∙ uncurry⁼ {C = T} {D = E} af
    Eg : (uncurry ((G ∘ q) ∘ r)) =₁ (g ∘ uncurry (q ∘ r))
    Eg = mapPost-uncurry {C = T} g (q ∘ r) ∙ uncurry⁼ {C = T} {D = E} ag
    Ef′ : (uncurry (F ∘ p) ∘ R) =₁ (f ∘ (uncurry p ∘ R))
    Ef′ = comp-assoc R (uncurry p) f ∙ (mapPost-uncurry {C = T} f p ▷ R)
    Eg′ : (uncurry (G ∘ q) ∘ R) =₁ (g ∘ (uncurry q ∘ R))
    Eg′ = comp-assoc R (uncurry q) g ∙ (mapPost-uncurry {C = T} g q ▷ R)
    ℓ : (uncurry (p ∘ r)) =₁ (uncurry p ∘ R)
    ℓ = uncurry-restrict p r
    ρ : (uncurry (q ∘ r)) =₁ (uncurry q ∘ R)
    ρ = uncurry-restrict q r
    source : Cone f g (Y × T)
    source = uncurry-cone {f = f} {g = g} (cone-restrict r s)
    target : Cone f g (Y × T)
    target = cone-restrict R (uncurry-cone {f = f} {g = g} s)
    rawSource : (f ∘ uncurry (p ∘ r)) =₁ (g ∘ uncurry (q ∘ r))
    rawSource = changeEndpoints Ef Eg (uncurry⁼ {C = T} {D = E} (τ ▷ r))
    rawTarget : (f ∘ (uncurry p ∘ R)) =₁ (g ∘ (uncurry q ∘ R))
    rawTarget = changeEndpoints Ef′ Eg′ (uncurry⁼ {C = T} {D = E} τ ▷ R)

    abstract
      source-normal : (Cone.match source) =₂ rawSource
      source-normal = changeEndpoints-iterated (uncurry⁼ {C = T} {D = E} af) (uncurry⁼ {C = T} {D = E} ag)
          (mapPost-uncurry {C = T} f (p ∘ r)) (mapPost-uncurry {C = T} g (q ∘ r)) (uncurry⁼ {C = T} {D = E} (τ ▷ r)) ∙
        comp₌-cong (id₌ (mapPost-uncurry {C = T} g (q ∘ r)))
          (comp₌-cong
            (comp₌-cong (id₌ (uncurry⁼ {C = T} {D = E} ag))
              (comp₌-cong (id₌ (uncurry⁼ {C = T} {D = E} (τ ▷ r))) (uncurry⁼-inverse {C = T} {D = E} af) ∙
                uncurry⁼-composition {C = T} {D = E} (τ ▷ r) (af ⁻¹)) ∙
              uncurry⁼-composition {C = T} {D = E} ag ((τ ▷ r) ∙ af ⁻¹))
            (id₌ ((mapPost-uncurry {C = T} f (p ∘ r)) ⁻¹)))

      target-normal : (Cone.match target) =₂ rawTarget
      target-normal = changeEndpoints-iterated (mapPost-uncurry {C = T} f p ▷ R) (mapPost-uncurry {C = T} g q ▷ R)
          (comp-assoc R (uncurry p) f) (comp-assoc R (uncurry q) g) (uncurry⁼ {C = T} {D = E} τ ▷ R) ∙
        comp₌-cong (id₌ (comp-assoc R (uncurry q) g))
          (comp₌-cong
            (comp₌-cong (id₌ (mapPost-uncurry {C = T} g q ▷ R))
              (comp₌-cong (id₌ (uncurry⁼ {C = T} {D = E} τ ▷ R)) (preWhisker-inverse (mapPost-uncurry {C = T} f p) R) ∙
                preWhisker-comp₌ (uncurry⁼ {C = T} {D = E} τ) ((mapPost-uncurry {C = T} f p) ⁻¹) R) ∙
              preWhisker-comp₌ (mapPost-uncurry {C = T} g q) (uncurry⁼ {C = T} {D = E} τ ∙ (mapPost-uncurry {C = T} f p) ⁻¹) R)
            (id₌ ((comp-assoc R (uncurry p) f) ⁻¹)))

    abstract
      rawSquare : (rawTarget ∙ (f ◁ ℓ)) =₂ ((g ◁ ρ) ∙ rawSource)
      rawSquare = transport-square Ef Ef′ Eg Eg′
        (uncurry⁼ (τ ▷ r)) (uncurry⁼ τ ▷ R) bf bg (f ◁ ℓ) (g ◁ ρ)
        (((mapPost-uncurry-restrict f p r) ⁻¹) ∙
          comp₌-assoc (comp-assoc R (uncurry p) f) (mapPost-uncurry f p ▷ R) bf)
        (((mapPost-uncurry-restrict g q r) ⁻¹) ∙
          comp₌-assoc (comp-assoc R (uncurry q) g) (mapPost-uncurry g q ▷ R) bg)
        (transpose-square₌ (unconst-sides₌ (uncurry-restrict-inputs τ r)))

    identification : ConeIdentification₁ source target
    identification = record { left = ℓ ; right = ρ
      ; compatible = comp₌-cong (id₌ (g ◁ ρ)) (source-normal ⁻¹) ∙
        (rawSquare ∙ comp₌-cong target-normal (id₌ (f ◁ ℓ))) }

  uncurry-cone-restrict : {X Y T C D E : CAT Γ} {f : MAP C E} {g : MAP D E}
    (r : MAP Y X) (s : Cone (mapPost {C = T} f) (mapPost g) X) →
    ConeIdentification₁ (uncurry-cone (cone-restrict r s)) (cone-restrict (productMap r (id T)) (uncurry-cone s))
  uncurry-cone-restrict = UncurriedRestriction.identification
```

## The mapped cone and its actual evaluation

Evaluation followed by chosen currying supplies the matching. The evaluation
comparison retains the complete cone law at every categorical probe source.

```agda
  module MappedCone {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (T : CAT Γ) (s : Cone f g S) where

    module Curried = CurriedCone (map-isAn T S) (cone-restrict mapEval s)
    value : Cone (mapPost {C = T} f) (mapPost g) (Map T S)
    value = Curried.value

    opaque
      evaluate : {X : CAT Γ} (h : MAP X (Map T S)) →
        ConeIdentification₁ (uncurry-cone (cone-restrict h value)) (cone-restrict (uncurry h) s)
      evaluate h = cone-compose (cone-restrict-assoc (productMap h (id T)) mapEval s)
        (cone-compose (cone-identification-restrict-One (productMap h (id T)) Curried.uncurry-law)
          (uncurry-cone-restrict {f = f} {g = g} h value))

  mapped-cone : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (T : CAT Γ) → Cone f g S → Cone (mapPost {C = T} f) (mapPost g) (Map T S)
  mapped-cone = MappedCone.value

  opaque
    mapped-cone-identification : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
      (T : CAT Γ) {s t : Cone f g S} → ConeIdentification₁ s t → ConeIdentification₁ (mapped-cone T s) (mapped-cone T t)
    mapped-cone-identification {S = S} {f = f} {g = g} T {s} {t} Φ = ReflectedCone.identification {f = f} {g = g}
      (map-isAn T S) (mapped-cone T s) (mapped-cone T t)
      (cone-compose (cone-inverse (MappedCone.Curried.uncurry-law T t))
        (cone-compose (cone-identification-restrict-One mapEval Φ) (MappedCone.Curried.uncurry-law T s)))

  opaque
    mapped-cone-restrict : {C D E S R : CAT Γ} {f : MAP C E} {g : MAP D E}
      (T : CAT Γ) (r : MAP R S) (s : Cone f g S) →
      ConeIdentification₁ (cone-restrict (mapPost r) (mapped-cone T s)) (mapped-cone T (cone-restrict r s))
    mapped-cone-restrict {R = R} {f = f} {g = g} T r s = ReflectedCone.identification {f = f} {g = g} (map-isAn T R)
      (cone-restrict (mapPost r) (mapped-cone T s)) (mapped-cone T (cone-restrict r s))
      (cone-compose (cone-inverse (MappedCone.Curried.uncurry-law T (cone-restrict r s)))
        (cone-compose (cone-inverse (cone-restrict-assoc mapEval r s))
          (cone-compose (cone-action-One s (mapPost-β r)) (MappedCone.evaluate T s (mapPost r)))))
```

## Preservation and all-category detection

The inverse factors the uncurried cone and curries that factor. Recognition
uses reflection only at the mapped vertex, where its anima hypothesis holds.
The factorization comparison then proves preservation and all-category
detection through post-tests-all.

```agda
  module MappingPullback {C D E : CAT Γ} (T : CAT Γ) (f : MAP C E) (g : MAP D E) where

    S : CAT Γ
    S = Map T (Pullback f g)
    F : MAP (Map T C) (Map T E)
    F = mapPost {C = T} f
    G : MAP (Map T D) (Map T E)
    G = mapPost {C = T} g
    R : CAT Γ
    R = Pullback F G
    original : Cone f g (Pullback f g)
    original = pullback-cone f g
    square : Cone F G S
    square = mapped-cone T original

    module FactorCone {X : CAT Γ} (xAn : isAn X) (s : Cone F G X) where
      uncurried : Cone f g (X × T)
      uncurried = uncurry-cone {f = f} {g = g} s
      uncurried-factor : MAP (X × T) (Pullback f g)
      uncurried-factor = pullback-factor uncurried
      factor : MAP X S
      factor = mapCurry xAn uncurried-factor

      abstract
        factor-law : ConeIdentification₁ (cone-restrict factor square) s
        factor-law = ReflectedCone.identification {f = f} {g = g} xAn (cone-restrict factor square) s
          (cone-compose (pullback-factor-β uncurried)
            (cone-compose (cone-action-One original (mapCurry-β xAn uncurried-factor)) (MappedCone.evaluate T original factor)))

    opaque
      reflect : {X : CAT Γ} → isAn X → (h k : MAP X S) →
        ConeIdentification₁ (cone-restrict h square) (cone-restrict k square) → h =₁ k
      reflect xAn h k Φ = uncurry-reflect xAn h k (pullback-reflect {f = f} {g = g} (uncurry h) (uncurry k)
        (cone-compose (MappedCone.evaluate T original k)
          (cone-compose (uncurry-cone-identification {f = f} {g = g} Φ) (cone-inverse (MappedCone.evaluate T original h)))))

    forward : MAP S R
    forward = pullback-factor square
    module Inverse = FactorCone (pullback-isAn F G (map-isAn T C) (map-isAn T D) (map-isAn T E)) (pullback-cone F G)
    inverse : MAP R S
    inverse = Inverse.factor

    opaque
      square-isPullback : IsPullback square
      square-isPullback = isPullback-from-factor-and-reflection square inverse Inverse.factor-law
        (reflect (map-isAn T (Pullback f g)))

  mapped-cone-factorization : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (T : CAT Γ) (s : Cone f g S) →
    (pullback-factor (mapped-cone T s)) =₁ (pullback-factor (mapped-cone T (pullback-cone f g)) ∘ mapPost (pullback-factor s))
  mapped-cone-factorization {f = f} {g} T s = pullback-factor-restrict (mapPost (pullback-factor s)) (mapped-cone T (pullback-cone f g)) ∙
    (pullback-factor-cong (cone-compose (mapped-cone-identification T (pullback-factor-β s))
      (mapped-cone-restrict T (pullback-factor s) (pullback-cone f g)))) ⁻¹

  map-preserves-pullback : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (T : CAT Γ) (s : Cone f g S) → IsPullback s → IsPullback (mapped-cone T s)
  map-preserves-pullback {f = f} {g} T s es = equiv-transport ((mapped-cone-factorization T s) ⁻¹)
    (equiv-compose (mapPost (pullback-factor s)) (pullback-factor (mapped-cone T (pullback-cone f g)))
      (mapPost-isEquiv (pullback-factor s) es) (MappingPullback.square-isPullback T f g))

  map-detects-pullback : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) → ((T : CAT Γ) → IsPullback (mapped-cone T s)) → IsPullback s
  map-detects-pullback {f = f} {g} s tests = post-tests-all (pullback-factor s) (λ T →
    equiv-cancel-left (mapPost (pullback-factor s)) (pullback-factor (mapped-cone T (pullback-cone f g)))
      (MappingPullback.square-isPullback T f g)
      (equiv-transport (mapped-cone-factorization T s) (tests T)))
```

## The terminal mapping test

A pullback after Map One supplies factorization, its full beta and reflection
for anima sources X. This retains the selected right-unit insertion and its
projection law, and asserts only this consequence of the single test.

```agda
  module TerminalTest {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) (mapped-isPullback : IsPullback (mapped-cone One s)) where

    module U = UniversalCone (mapped-cone One s) mapped-isPullback

    module Factor {X : CAT Γ} (xAn : isAn X) (t : Cone f g X) where
      module Curried = CurriedCone xAn (cone-restrict (pr₁ {C = X} {D = One}) t)
      mapped-factor : MAP X (Map One S)
      mapped-factor = U.factor Curried.value
      factor : MAP X S
      factor = uncurry mapped-factor ∘ product-unitʳ-inverse X

      abstract
        factor-law : ConeIdentification₁ (cone-restrict factor s) t
        factor-law = cone-compose (cone-restrict-id t)
          (cone-compose (cone-action-One t (pair-β₁ (id X) (terminate X)))
          (cone-compose (cone-restrict-assoc (product-unitʳ-inverse X) pr₁ t)
          (cone-compose (cone-identification-restrict-One (product-unitʳ-inverse X)
            (cone-compose Curried.uncurry-law
              (cone-compose (uncurry-cone-identification (U.β Curried.value))
                (cone-inverse (MappedCone.evaluate One s mapped-factor)))))
            (cone-inverse (cone-restrict-assoc (product-unitʳ-inverse X) (uncurry mapped-factor) s)))))

    factor : {X : CAT Γ} → isAn X → Cone f g X → MAP X S
    factor = Factor.factor

    factor-β : {X : CAT Γ} (xAn : isAn X) (t : Cone f g X) →
      ConeIdentification₁ (cone-restrict (factor xAn t) s) t
    factor-β = Factor.factor-law

    module Reflection {X : CAT Γ} (xAn : isAn X) (h k : MAP X S)
      (Φ : ConeIdentification₁ (cone-restrict h s) (cone-restrict k s)) where
      curried-h : MAP X (Map One S)
      curried-h = mapCurry xAn (h ∘ pr₁ {C = X} {D = One})
      curried-k : MAP X (Map One S)
      curried-k = mapCurry xAn (k ∘ pr₁ {C = X} {D = One})
      evaluate : (z : MAP X S) → ConeIdentification₁
        (uncurry-cone (cone-restrict (mapCurry xAn (z ∘ pr₁ {C = X} {D = One})) (mapped-cone One s)))
        (cone-restrict pr₁ (cone-restrict z s))
      evaluate z = cone-compose (cone-inverse (cone-restrict-assoc pr₁ z s))
        (cone-compose (cone-action-One s (mapCurry-β xAn (z ∘ pr₁)))
          (MappedCone.evaluate One s (mapCurry xAn (z ∘ pr₁))))

      curried-identification : curried-h =₁ curried-k
      curried-identification = U.reflect curried-h curried-k (ReflectedCone.identification xAn _ _
        (cone-compose (cone-inverse (evaluate k))
          (cone-compose (cone-identification-restrict-One pr₁ Φ) (evaluate h))))

      identification : h =₁ k
      identification = Fact.factor (factor-through-preWhisker (pr₁ {C = X} {D = One})
        (product-unitʳ-isEquiv X)
        (mapCurry-β xAn (k ∘ pr₁) ∙
          (uncurry⁼ curried-identification ∙ (mapCurry-β xAn (h ∘ pr₁)) ⁻¹)))

    reflect : {X : CAT Γ} (xAn : isAn X) (h k : MAP X S) →
      ConeIdentification₁ (cone-restrict h s) (cone-restrict k s) → h =₁ k
    reflect = Reflection.identification
```
