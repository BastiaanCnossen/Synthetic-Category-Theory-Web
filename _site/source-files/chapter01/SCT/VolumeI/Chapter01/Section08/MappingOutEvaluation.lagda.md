# Complete evaluation of mapping-out cones

The represented cocone retains its whole matching and independent family
image. Actual precomposition evaluation supports complete square recovery.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section08.MappingOutEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (preWhisker-id; postWhisker-id)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong₂; productMap-cong-triangle₁; productMap-cong-triangle₂;
    productMap-cong-comp; productMap-cong-id-One; productMap-cong-square)
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square; comp-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-unique; inverse-composite; inverse-inverse; postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; comp₌-inverseˡ-One; cancel-left; cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (pentagon-whiskered-right; whisker-mixed-One; postWhisker-comp-One; preWhisker-comp-One;
    triangle-whiskered; identity-unitors; right-unitor-comp; left-unitor-comp; postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; post-square-cell; post-square-cell-id; post-square-cell-comp;
    lies-over-comp; restrict-triangle; restrict-triangle-assoc; restrict-change-square-One; restrict-square-One)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate; productMap-first-comp; productMap-comp-natural-outer-One; productMap-comp-natural-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-unique)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; square-to-changeEndpoints; transport-square; reflect-transported-square; changeEndpoints-extend-square)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map; map-isAn; mapEval; uncurry)
open import SCT.VolumeI.Chapter01.Section04.Currying
  using (curry⁼-cong; uncurry⁼; uncurry⁼-cong; uncurry⁼-composition; uncurry⁼-constant; uncurry⁼-identity; uncurry⁼-evaluate;
    uncurry-reflect; uncurry-reflect-β; uncurry⁼-reflect; uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre-uncurry; mapPre-β; mapPre-comp; mapPre⁼; mapPre-β-natural)
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction using (uncurry-restrict-inputs; uncurry-restrict-iterated)
open import SCT.VolumeI.Chapter01.Section04.Precomposition using (mapPre-uncurry-inputs)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate⁼-absolute)
import SCT.VolumeI.Chapter01.Section07.PreEvaluationSubstitution as Pre
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section08.Cocones
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares using (mappingOut; IsPushout)

open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change)

private
  module _ {Γ : Context} where
    module RestrictionEvaluationAction (P : CAT Γ) where
      J : {A B : CAT Γ} → MAP A B → MAP (P × A) (P × B)
      J = product-restriction {P = P}
      R : {A B : CAT Γ} {f g : MAP A B} → f =₁ g → J f =₁ J g
      R = productMap-cong (id₌ (id P))
      K : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) → (J g ∘ J f) =₁ J (g ∘ f)
      K = restriction-compositor {P = P}
      R-comp : {A B : CAT Γ} {f g h : MAP A B}
        (β : g =₁ h) (α : f =₁ g) → R (β ∙ α) =₂ (R β ∙ R α)
      R-comp = restriction-action-composition
      R-id : {A B : CAT Γ} (f : MAP A B) → R (id₌ f) =₂ id₌ (J f)
      R-id = productMap-cong-id-One (id P)
      outer-natural : {A B C : CAT Γ} (f : MAP A B) {g h : MAP B C} (α : g =₁ h)
        → SquareCell₌ (R α ▷ J f) (R (α ▷ f)) (K f g) (K f h)
      outer-natural = restriction-compositor-outer-natural
      inner-natural : {A B C : CAT Γ} {f g : MAP A B} (α : f =₁ g) (h : MAP B C)
        → SquareCell₌ (J h ◁ R α) (R (h ◁ α)) (K f h) (K g h)
      inner-natural = restriction-compositor-inner-natural

private
  uncurry-inverse : {Γ : Context} {P C E : CAT Γ} {f g : MAP P (Map C E)} (α : f =₁ g) →
    uncurry⁼ (α ⁻¹) =₂ (uncurry⁼ α) ⁻¹
  uncurry-inverse {f = f} α =
    (inverse-unique (uncurry⁼ α) (uncurry⁼ (α ⁻¹))
      (uncurry⁼-identity f ∙
        (uncurry⁼-cong (comp₌-inverseˡ α) ∙
          (uncurry⁼-composition (α ⁻¹) α) ⁻¹))) ⁻¹


module _ {Γ : Context} where
  module MappingOutEvaluation {P A B C E : CAT Γ}
    (u : MAP A B) (l : MAP A C) where

    Ju : MAP (P × A) (P × B)
    Ju = productMap (id P) u
    Jl : MAP (P × A) (P × C)
    Jl = productMap (id P) l

    represented : Cone (mapPre {D = E} u) (mapPre l) P → Cocone Ju Jl E
    represented s = record
      { left = uncurry (Cone.left s) ; right = uncurry (Cone.right s)
      ; match = changeEndpoints (mapPre-uncurry u (Cone.left s))
          (mapPre-uncurry l (Cone.right s)) (uncurry⁼ (Cone.match s)) }

    private
      module _ {X : CAT Γ} where
        open Terms.Equalities X using (_＝_)

        matching-frame : (s : Cone (mapPre {D = E} u) (mapPre l) P) →
          changeEndpoints (const {P = X} (mapPre-uncurry u (Cone.left s)))
            (const (mapPre-uncurry l (Cone.right s)))
            (uncurry⁼ (const (Cone.match s))) =₁ const (Cocone.match (represented s))
        matching-frame s = const-comp gs (uncurry⁼ τ ∙ fs ⁻¹) ∙
          comp₌-cong (id₌ (const gs))
            (const-comp (uncurry⁼ τ) (fs ⁻¹) ∙
              comp₌-cong (uncurry⁼-constant τ) ((const-inv fs) ⁻¹))
          where
          fs = mapPre-uncurry u (Cone.left s)
          gs = mapPre-uncurry l (Cone.right s)
          τ = Cone.match s

    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      evaluate-identification : {s t : Cone (mapPre {D = E} u) (mapPre l) P} →
        ConeIdentification X s t → CoconeIdentification X (represented s) (represented t)
      evaluate-identification {s} {t} Φ = record
        { left = uncurry⁼ α ; right = uncurry⁼ β
        ; compatible = replace-sides₌ (matching-frame {X = X} s) (matching-frame {X = X} t)
            (transport-square fs ft gs gt τs τt raw-left raw-right native-left native-right
              (mapPre-uncurry-inputs u α) (mapPre-uncurry-inputs l β) raw-square) }
        where
        α = ConeIdentification.left Φ
        β = ConeIdentification.right Φ
        fs : uncurry (mapPre u ∘ Cone.left s) ＝ (uncurry (Cone.left s) ∘ Ju)
        fs = const {P = X} (mapPre-uncurry u (Cone.left s))
        ft : uncurry (mapPre u ∘ Cone.left t) ＝ (uncurry (Cone.left t) ∘ Ju)
        ft = const {P = X} (mapPre-uncurry u (Cone.left t))
        gs : uncurry (mapPre l ∘ Cone.right s) ＝ (uncurry (Cone.right s) ∘ Jl)
        gs = const {P = X} (mapPre-uncurry l (Cone.right s))
        gt : uncurry (mapPre l ∘ Cone.right t) ＝ (uncurry (Cone.right t) ∘ Jl)
        gt = const {P = X} (mapPre-uncurry l (Cone.right t))
        τs : uncurry (mapPre u ∘ Cone.left s) ＝ uncurry (mapPre l ∘ Cone.right s)
        τs = uncurry⁼ (const {P = X} (Cone.match s))
        τt : uncurry (mapPre u ∘ Cone.left t) ＝ uncurry (mapPre l ∘ Cone.right t)
        τt = uncurry⁼ (const {P = X} (Cone.match t))
        raw-left = uncurry⁼ (mapPre u ◁ α)
        raw-right = uncurry⁼ (mapPre l ◁ β)
        native-left = uncurry⁼ α ▷ Ju
        native-right = uncurry⁼ β ▷ Jl
        raw-square : (τt ∙ raw-left) =₁ (raw-right ∙ τs)
        raw-square = uncurry⁼-composition (mapPre l ◁ β) (const (Cone.match s)) ∙
          (uncurry⁼-cong (ConeIdentification.compatible Φ) ∙
            (uncurry⁼-composition (const (Cone.match t)) (mapPre u ◁ α)) ⁻¹)

      module RecoveredIdentification (pAn : isAn P)
        (s t : Cone (mapPre {D = E} u) (mapPre l) P)
        (Φ : CoconeIdentification X (represented s) (represented t)) where

        left : Cone.left s ＝ Cone.left t
        left = uncurry-reflect pAn _ _ (CoconeIdentification.left Φ)
        right : Cone.right s ＝ Cone.right t
        right = uncurry-reflect pAn _ _ (CoconeIdentification.right Φ)

        left-image : uncurry⁼ left =₁ CoconeIdentification.left Φ
        left-image = uncurry-reflect-β pAn _ _ (CoconeIdentification.left Φ)
        right-image : uncurry⁼ right =₁ CoconeIdentification.right Φ
        right-image = uncurry-reflect-β pAn _ _ (CoconeIdentification.right Φ)

        private
          adjusted : CoconeIdentification X (represented s) (represented t)
          adjusted = record
            { left = uncurry⁼ left ; right = uncurry⁼ right
            ; compatible = replace-edges₌
                ((preWhisker Ju ◁ left-image) ⁻¹)
                ((preWhisker Jl ◁ right-image) ⁻¹)
                (CoconeIdentification.compatible Φ) }

          fs : uncurry (mapPre u ∘ Cone.left s) ＝ (uncurry (Cone.left s) ∘ Ju)
          fs = const {P = X} (mapPre-uncurry u (Cone.left s))
          ft : uncurry (mapPre u ∘ Cone.left t) ＝ (uncurry (Cone.left t) ∘ Ju)
          ft = const {P = X} (mapPre-uncurry u (Cone.left t))
          gs : uncurry (mapPre l ∘ Cone.right s) ＝ (uncurry (Cone.right s) ∘ Jl)
          gs = const {P = X} (mapPre-uncurry l (Cone.right s))
          gt : uncurry (mapPre l ∘ Cone.right t) ＝ (uncurry (Cone.right t) ∘ Jl)
          gt = const {P = X} (mapPre-uncurry l (Cone.right t))
          τs : uncurry (mapPre u ∘ Cone.left s) ＝ uncurry (mapPre l ∘ Cone.right s)
          τs = uncurry⁼ (const {P = X} (Cone.match s))
          τt : uncurry (mapPre u ∘ Cone.left t) ＝ uncurry (mapPre l ∘ Cone.right t)
          τt = uncurry⁼ (const {P = X} (Cone.match t))
          α : uncurry (mapPre u ∘ Cone.left s) ＝ uncurry (mapPre u ∘ Cone.left t)
          α = uncurry⁼ (mapPre u ◁ left)
          β : uncurry (mapPre l ∘ Cone.right s) ＝ uncurry (mapPre l ∘ Cone.right t)
          β = uncurry⁼ (mapPre l ◁ right)

          raw-square : (τt ∙ α) =₁ (β ∙ τs)
          raw-square = reflect-transported-square fs gs ft gt τs τt α β
            (uncurry⁼ left ▷ Ju) (uncurry⁼ right ▷ Jl)
            (mapPre-uncurry-inputs u left) (mapPre-uncurry-inputs l right)
            (replace-sides₌ ((matching-frame {X = X} s) ⁻¹) ((matching-frame {X = X} t) ⁻¹)
              (CoconeIdentification.compatible adjusted))

        identification : ConeIdentification X s t
        identification = record
          { left = left ; right = right
          ; compatible = uncurry⁼-reflect pAn _ _
              ((uncurry⁼-composition (mapPre l ◁ right) (const (Cone.match s))) ⁻¹ ∙
                (raw-square ∙ uncurry⁼-composition (const (Cone.match t)) (mapPre u ◁ left))) }
```


## The actual supplied square under evaluation

The selected precomposition compositor is recovered from its literal input.
Its evaluation square and the specified precomposition action square give
all three pieces of the mapping-out matching. Endpoint change then uses the
actual evaluation beta legs, with no assumption that mapping-out is a
coherent pseudofunctor.

```agda
module _ {Γ : Context} where
  mapPre-comp-input : {A B C E : CAT Γ} (f : MAP A B) (g : MAP B C) →
    uncurry (mapPre {D = E} f ∘ mapPre g) =₁ uncurry (mapPre (g ∘ f))
  mapPre-comp-input {C = C} {E} f g =
    (mapPre-β (g ∘ f)) ⁻¹ ∙
      ((mapEval ◁ restriction-compositor {P = Map C E} f g) ∙
        (comp-assoc (product-restriction f) (product-restriction g) mapEval ∙
          ((mapPre-β g ▷ product-restriction f) ∙ mapPre-uncurry f (mapPre g))))

  mapPre-comp-image : {A B C E : CAT Γ} (f : MAP A B) (g : MAP B C) →
    uncurry⁼ (mapPre-comp {D = E} f g) =₁ mapPre-comp-input f g
  mapPre-comp-image {C = C} {E} f g =
    uncurry-reflect-β (map-isAn C E)
      (mapPre {D = E} f ∘ mapPre g) (mapPre (g ∘ f)) (mapPre-comp-input f g)

  module CompositorEvaluation {A B C E : CAT Γ} (f : MAP A B) (g : MAP B C) where
    Jf : MAP (Map C E × A) (Map C E × B)
    Jf = product-restriction f
    Jg : MAP (Map C E × B) (Map C E × C)
    Jg = product-restriction g

    before : uncurry (mapPre {D = E} f ∘ mapPre g) =₁ ((mapEval ∘ Jg) ∘ Jf)
    before = (mapPre-β g ▷ Jf) ∙ mapPre-uncurry f (mapPre g)
    after : uncurry (mapPre {D = E} (g ∘ f)) =₁ (mapEval ∘ product-restriction (g ∘ f))
    after = mapPre-β (g ∘ f)
    product-route : ((mapEval ∘ Jg) ∘ Jf) =₁ (mapEval ∘ product-restriction (g ∘ f))
    product-route = (mapEval ◁ restriction-compositor f g) ∙ comp-assoc Jf Jg mapEval

    abstract
      square : SquareCell₌ (uncurry⁼ (mapPre-comp {D = E} f g)) product-route before after
      square = (comp₌-assoc (mapEval ◁ restriction-compositor f g) (comp-assoc Jf Jg mapEval) before) ⁻¹ ∙
        (comp-inv-left after
          ((mapEval ◁ restriction-compositor f g) ∙ (comp-assoc Jf Jg mapEval ∙ before)) ∙
          comp₌-cong (id₌ after) (mapPre-comp-image f g))

  module ActualSquareEvaluation {A B C D E : CAT Γ} {l : MAP A C} {r : MAP B D}
    (s : Square l r) where
    private
      P : CAT Γ
      P = Map D E
      u : MAP A B
      u = Square.source-map s
      v : MAP C D
      v = Square.target-map s
      σ : (r ∘ u) =₁ (v ∘ l)
      σ = Square.cell s
      Ju = product-restriction {P = P} u
      Jl = product-restriction {P = P} l
      Jr = product-restriction {P = P} r
      Jv = product-restriction {P = P} v
      module Evaluation = MappingOutEvaluation {P = P} {E = E} u l
      module Left = CompositorEvaluation {E = E} u r
      module Right = CompositorEvaluation {E = E} l v

    source : Cocone Ju Jl E
    source = Evaluation.represented (mappingOut s E)
    target : Cocone Ju Jl E
    target = cocone-postcompose mapEval (square-cocone (product-square {P = P} s))

    left : Cocone.left source =₁ Cocone.left target
    left = mapPre-β r
    right : Cocone.right source =₁ Cocone.right target
    right = mapPre-β v

    private
      Mu : uncurry (mapPre u ∘ mapPre {D = E} r) =₁ (uncurry (mapPre r) ∘ Ju)
      Mu = mapPre-uncurry u (mapPre r)
      Ml : uncurry (mapPre l ∘ mapPre {D = E} v) =₁ (uncurry (mapPre v) ∘ Jl)
      Ml = mapPre-uncurry l (mapPre v)
      Kleft = mapEval ◁ restriction-compositor {P = P} u r
      Kright = mapEval ◁ restriction-compositor {P = P} l v
      middle = mapEval ◁ productMap-cong (id₌ (id P)) σ
      Aleft = comp-assoc Ju Jr mapEval
      Aright = comp-assoc Jl Jv mapEval
      raw-left = uncurry⁼ (mapPre-comp {D = E} u r)
      raw-right = uncurry⁼ (mapPre-comp {D = E} l v)
      raw-middle = uncurry⁼ (mapPre⁼ {D = E} σ)
      raw-match = uncurry⁼ (Cone.match (mappingOut s E))
      raw-expanded = raw-right ⁻¹ ∙ (raw-middle ∙ raw-left)
      native-expanded = (Kright ∙ Aright) ⁻¹ ∙ (middle ∙ (Kleft ∙ Aleft))

      middle-square : SquareCell₌ raw-middle middle Left.after Right.after
      middle-square = replace-edges₌ (id₌ raw-middle)
        (postWhisker mapEval ◁ productMap-cong₂ (const-One (id₌ (id P))) (id₌ σ))
        (unconst-sides₌ (mapPre-β-natural σ))

      raw-normal : raw-match =₂ raw-expanded
      raw-normal = comp₌-cong
        (uncurry-inverse (mapPre-comp {D = E} l v))
        (uncurry⁼-composition (mapPre⁼ σ) (mapPre-comp u r)) ∙
          uncurry⁼-composition ((mapPre-comp l v) ⁻¹) (mapPre⁼ σ ∙ mapPre-comp u r)

      posted-cell : (mapEval ◁ Square.cell (product-square {P = P} s)) =₂
        (Kright ⁻¹ ∙ (middle ∙ Kleft))
      posted-cell = comp₌-cong (postWhisker-inverse mapEval (restriction-compositor l v))
        (postWhisker-comp₌ mapEval (productMap-cong (id₌ (id P)) σ) (restriction-compositor u r)) ∙
          postWhisker-comp₌ mapEval ((restriction-compositor l v) ⁻¹)
            (productMap-cong (id₌ (id P)) σ ∙ restriction-compositor u r)

      native-normal : native-expanded =₂ Cocone.match target
      native-normal = comp₌-cong (id₌ (Aright ⁻¹))
          (comp₌-cong (posted-cell ⁻¹) (id₌ Aleft)) ∙
        (comp₌-cong (id₌ (Aright ⁻¹))
          ((comp₌-assoc (Kright ⁻¹) (middle ∙ Kleft) Aleft) ⁻¹ ∙
            comp₌-cong (id₌ (Kright ⁻¹)) ((comp₌-assoc middle Kleft Aleft) ⁻¹)) ∙
          (comp₌-assoc (Aright ⁻¹) (Kright ⁻¹) (middle ∙ (Kleft ∙ Aleft)) ∙
            comp₌-cong (inverse-composite Kright Aright) (id₌ (middle ∙ (Kleft ∙ Aleft)))))

      raw-square : SquareCell₌ raw-match (Cocone.match target) Left.before Right.before
      raw-square = replace-edges₌ (raw-normal ⁻¹) native-normal
        (inv-comp-square₌ (adjoin-square₌ Left.square middle-square) Right.square)

    abstract
      identification : CoconeIdentification₁ source target
      identification = record
        { left = left ; right = right
        ; compatible = transpose-square₌
            (replace-sides₌ (comp-inv-right (left ▷ Ju) Mu) (comp-inv-right (right ▷ Jl) Ml)
              (changeEndpoints-extend-square Mu Ml raw-match raw-square)) }
```


## Input comparison at a categorical parameter

The five literal factors of precomposition uncurrying each carry a square.
Their paste compares the whole supplied input identification, with the actual
precomposition uncurrying identifications on both sides.

```agda
module _ {Γ : Context} where
  module ParameterizedInputEvaluation {P A B E : CAT Γ}
    (h : MAP P (Map B E)) {f g : MAP A B} (α : f =₁ g) where
    private
      Q : CAT Γ
      Q = Map B E
      RA = productMap h (id A)
      RB = productMap h (id B)
      JQf = product-restriction {P = Q} f
      JQg = product-restriction {P = Q} g
      JPf = product-restriction {P = P} f
      JPg = product-restriction {P = P} g
      δQ = productMap-cong (id₌ (id Q)) α
      δP = productMap-cong (id₌ (id P)) α
      e : MAP (Q × B) E
      e = mapEval
      first : SquareCell₌ (uncurry⁼ (mapPre⁼ {D = E} α ▷ h))
        (uncurry⁼ (mapPre⁼ α) ▷ RA)
        (uncurry-restrict (mapPre f) h) (uncurry-restrict (mapPre g) h)
      first = unconst-sides₌ (uncurry-restrict-inputs (mapPre⁼ α) h)

      base : SquareCell₌ (uncurry⁼ (mapPre⁼ {D = E} α)) (e ◁ δQ)
        (mapPre-β f) (mapPre-β g)
      base = replace-edges₌ (id₌ _)
        (postWhisker e ◁ productMap-cong₂ (const-One (id₌ (id Q))) (id₌ α))
        (unconst-sides₌ (mapPre-β-natural α))
      second : SquareCell₌ (uncurry⁼ (mapPre⁼ {D = E} α) ▷ RA)
        ((e ◁ δQ) ▷ RA) (mapPre-β f ▷ RA) (mapPre-β g ▷ RA)
      second = pre-square₌ RA base
      third : SquareCell₌ ((e ◁ δQ) ▷ RA) (e ◁ (δQ ▷ RA))
        (comp-assoc RA JQf e) (comp-assoc RA JQg e)
      third = whisker-mixed-One δQ RA e
      fourth : SquareCell₌ (e ◁ (δQ ▷ RA)) (e ◁ (RB ◁ δP))
        (e ◁ productMap-separate h f) (e ◁ productMap-separate h g)
      fourth = post-square₌ e (SeparationSecondInput.compatibility h α)
      fifth : SquareCell₌ (e ◁ (RB ◁ δP)) (uncurry h ◁ δP)
        ((comp-assoc JPf RB e) ⁻¹) ((comp-assoc JPg RB e) ⁻¹)
      fifth = inverse-square₌ (postWhisker-comp-One δP RB e)

    compatibility : SquareCell₌ (uncurry⁼ (mapPre⁼ {D = E} α ▷ h))
      (uncurry h ◁ productMap-cong (id₌ (id P)) α)
      (mapPre-uncurry f h) (mapPre-uncurry g h)
    compatibility = paste-square₌
      (paste-square₌ (paste-square₌ (paste-square₌ first second) third) fourth) fifth
```


## Parameter substitution and the selected compositor

The shared represented-precomposition calculation retains the actual beta
triangles. Its scalar evaluation action is compared explicitly with the
selected uncurry action. Both the compositor and source associator are
transported along this bridge; the public mapping formulas keep their literal
uncurry action and selected product route.

```agda
private
  module _ {Γ : Context} {T C E : CAT Γ} {h k : MAP T (Map C E)} where
    map-scalar-action : (α : h =₁ k) → uncurry⁼ α =₂ evaluate-cong mapEval α
    map-scalar-action α = evaluate⁼-absolute mapEval α ∙ uncurry⁼-evaluate α

module _ {Γ : Context} where
  module ParameterChangeDiagram {X Y A B E : CAT Γ}
    (f : MAP A B) (k : MAP Y (Map B E)) (h : MAP X Y) where
    private
      module R = Pre.RepresentedPrecomposition
        (mapEval {C = A} {D = E}) (mapEval {C = B} {D = E})
        f (mapPre f) (mapPre-β f)
      HA = productMap h (id A)
      HB = productMap h (id B)
      LX = product-restriction {P = X} f
      LY = product-restriction {P = Y} f
      action = (comp-assoc LX HB (uncurry k)) ⁻¹ ∙
        ((uncurry k ◁ productMap-separate h f) ∙
          (comp-assoc HA LY (uncurry k) ∙ (mapPre-uncurry f k ▷ HA)))
      source-bridge = comp₌-cong (id₌ (uncurry-restrict k h ▷ LX))
        (comp₌-cong (id₌ (mapPre-uncurry f (k ∘ h)))
          (map-scalar-action (comp-assoc h k (mapPre f))))

    comparison : ((uncurry-restrict k h ▷ LX) ∙
      (mapPre-uncurry f (k ∘ h) ∙ uncurry⁼ (comp-assoc h k (mapPre f)))) =₂
      (action ∙ uncurry-restrict (mapPre f ∘ k) h)
    comparison = R.substitution k h ∙ source-bridge

  module ParameterizedCompositorEvaluation {P A B C E : CAT Γ}
    (f : MAP A B) (g : MAP B C) (h : MAP P (Map C E)) where
    private
      eA = mapEval {C = A} {D = E}
      eB = mapEval {C = B} {D = E}
      eC = mapEval {C = C} {D = E}
      Ff = mapPre {D = E} f
      Fg = mapPre {D = E} g
      Fgf = mapPre {D = E} (g ∘ f)
      JPf = product-restriction {P = P} f
      JPg = product-restriction {P = P} g
      κP = restriction-compositor {P = P} f g
      module Default = CompositorEvaluation {E = E} f g
      module Calculation = Pre.PrecompositionCompositor eA eB eC f g Ff Fg Fgf
        (mapPre-β f) (mapPre-β g) (mapPre-β (g ∘ f)) (mapPre-comp f g)
      base-square = replace-edges₌ (map-scalar-action (mapPre-comp f g))
        (id₌ Default.product-route) Default.square
      source-bridge = comp₌-cong (id₌ (mapPre-uncurry g h ▷ JPf))
        (comp₌-cong (id₌ (mapPre-uncurry f (Fg ∘ h)))
          ((map-scalar-action (comp-assoc h Fg Ff)) ⁻¹))

    before : uncurry ((Ff ∘ Fg) ∘ h) =₁ ((uncurry h ∘ JPg) ∘ JPf)
    before = (mapPre-uncurry g h ▷ JPf) ∙
      (mapPre-uncurry f (Fg ∘ h) ∙ uncurry⁼ (comp-assoc h Fg Ff))
    after : uncurry (mapPre (g ∘ f) ∘ h) =₁ (uncurry h ∘ product-restriction (g ∘ f))
    after = mapPre-uncurry (g ∘ f) h
    product-route = (uncurry h ◁ κP) ∙ comp-assoc JPf JPg (uncurry h)
    square : SquareCell₌ (uncurry⁼ (mapPre-comp {D = E} f g ▷ h)) product-route before after
    square = replace-sides₌ source-bridge (id₌ after)
      (replace-edges₌ ((map-scalar-action (mapPre-comp f g ▷ h)) ⁻¹)
        (id₌ product-route) (Calculation.comparison base-square h))

```

## Complete evaluation of a restricted mapping-out square

The supplied square is restricted along an arbitrary categorical mapping
parameter. Both cone-restriction associators are retained and normalized,
then the three compositor/input faces assemble the complete matching
comparison. The legs are the actual precomposition uncurrying comparisons.

```agda
module _ {Γ : Context} where
  module ParameterizedSquareEvaluation {P A B C D E : CAT Γ} {l : MAP A C} {r : MAP B D}
    (s : Square l r) (h : MAP P (Map D E)) where
    private
      u : MAP A B
      u = Square.source-map s
      v : MAP C D
      v = Square.target-map s
      σ : (r ∘ u) =₁ (v ∘ l)
      σ = Square.cell s
      Ju = product-restriction {P = P} u
      Jl = product-restriction {P = P} l
      Jr = product-restriction {P = P} r
      Jv = product-restriction {P = P} v
      module Evaluation = MappingOutEvaluation {P = P} {E = E} u l
      module Left = ParameterizedCompositorEvaluation u r h
      module Right = ParameterizedCompositorEvaluation l v h

    source : Cocone Ju Jl E
    source = Evaluation.represented (cone-restrict h (mappingOut s E))
    target : Cocone Ju Jl E
    target = cocone-postcompose (uncurry h) (square-cocone (product-square {P = P} s))

    left : Cocone.left source =₁ Cocone.left target
    left = mapPre-uncurry r h
    right : Cocone.right source =₁ Cocone.right target
    right = mapPre-uncurry v h

    private
      Mu : uncurry (mapPre u ∘ (mapPre {D = E} r ∘ h)) =₁ (uncurry (mapPre r ∘ h) ∘ Ju)
      Mu = mapPre-uncurry u (mapPre r ∘ h)
      Ml : uncurry (mapPre l ∘ (mapPre {D = E} v ∘ h)) =₁ (uncurry (mapPre v ∘ h) ∘ Jl)
      Ml = mapPre-uncurry l (mapPre v ∘ h)
      Kleft = uncurry h ◁ restriction-compositor {P = P} u r
      Kright = uncurry h ◁ restriction-compositor {P = P} l v
      middle = uncurry h ◁ productMap-cong (id₌ (id P)) σ
      Aleft = comp-assoc Ju Jr (uncurry h)
      Aright = comp-assoc Jl Jv (uncurry h)
      assoc-left = uncurry⁼ (comp-assoc h (mapPre r) (mapPre {D = E} u))
      assoc-right = uncurry⁼ (comp-assoc h (mapPre v) (mapPre {D = E} l))
      raw-left = uncurry⁼ (mapPre-comp {D = E} u r ▷ h) ∙ assoc-left ⁻¹
      raw-right = uncurry⁼ (mapPre-comp {D = E} l v ▷ h) ∙ assoc-right ⁻¹
      raw-middle = uncurry⁼ (mapPre⁼ {D = E} σ ▷ h)
      raw-match = uncurry⁼ (Cone.match (cone-restrict h (mappingOut s E)))
      raw-expanded = raw-right ⁻¹ ∙ (raw-middle ∙ raw-left)
      native-expanded = (Kright ∙ Aright) ⁻¹ ∙ (middle ∙ (Kleft ∙ Aleft))

      before-left = (left ▷ Ju) ∙ Mu
      before-right = (right ▷ Jl) ∙ Ml

      -- Remove only the actual uncurry associator from the compositor face.
      strip : {K T : CAT Γ} {x y z x′ y′ : MAP K T}
        (a : x =₁ y) (t : x =₁ z) (b : x′ =₁ y′)
        (q : y =₁ x′) (r : z =₁ y′)
        → SquareCell₌ t b (q ∙ a) r
        → SquareCell₌ (t ∙ a ⁻¹) b q r
      strip a t b q r square = comp₌-cong (id₌ b) (comp-inv-right q a) ∙
        (comp₌-assoc b (q ∙ a) (a ⁻¹) ∙
          (comp₌-cong square (id₌ (a ⁻¹)) ∙
            (comp₌-assoc r t (a ⁻¹)) ⁻¹))

      left-square : SquareCell₌ raw-left (Kleft ∙ Aleft) before-left Left.after
      left-square = strip assoc-left (uncurry⁼ (mapPre-comp u r ▷ h))
        (Kleft ∙ Aleft) before-left Left.after
        (replace-sides₌ ((comp₌-assoc (left ▷ Ju) Mu assoc-left) ⁻¹) (id₌ Left.after) Left.square)
      right-square : SquareCell₌ raw-right (Kright ∙ Aright) before-right Right.after
      right-square = strip assoc-right (uncurry⁼ (mapPre-comp l v ▷ h))
        (Kright ∙ Aright) before-right Right.after
        (replace-sides₌ ((comp₌-assoc (right ▷ Jl) Ml assoc-right) ⁻¹) (id₌ Right.after) Right.square)
      middle-square : SquareCell₌ raw-middle middle Left.after Right.after
      middle-square = ParameterizedInputEvaluation.compatibility h σ

      -- Raw normalization below includes restriction's TWO actual associators.
      raw-normal : raw-match =₂ raw-expanded
      raw-normal = normalization
        where
        L = mapPre-comp {D = E} u r
        R = mapPre-comp {D = E} l v
        M = mapPre⁼ {D = E} σ
        x = uncurry⁼ (L ▷ h)
        y = uncurry⁼ (R ▷ h)
        z = raw-middle
        left-associator = assoc-left
        right-associator = assoc-right
        restrict-composite = comp₌-cong (preWhisker-inverse R h)
          (preWhisker-comp₌ M L h) ∙ preWhisker-comp₌ (R ⁻¹) (M ∙ L) h
        lifted = comp₌-cong (uncurry-inverse (R ▷ h))
          (uncurry⁼-composition (M ▷ h) (L ▷ h)) ∙
            uncurry⁼-composition ((R ▷ h) ⁻¹) ((M ▷ h) ∙ (L ▷ h))
        raw = comp₌-cong (id₌ right-associator)
          (comp₌-cong (lifted ∙ uncurry⁼-cong restrict-composite) (uncurry-inverse (comp-assoc h (mapPre r) (mapPre u))) ∙
            uncurry⁼-composition (Cone.match (mappingOut s E) ▷ h) ((comp-assoc h (mapPre r) (mapPre u)) ⁻¹)) ∙
              uncurry⁼-composition (comp-assoc h (mapPre v) (mapPre l))
                ((Cone.match (mappingOut s E) ▷ h) ∙ (comp-assoc h (mapPre r) (mapPre u)) ⁻¹)
        normalized = comp₌-cong
          (comp₌-cong (inverse-inverse right-associator) (id₌ (y ⁻¹)) ∙ inverse-composite y (right-associator ⁻¹))
          (id₌ (z ∙ (x ∙ left-associator ⁻¹)))
        regroup = comp₌-cong (id₌ right-associator)
          (comp₌-cong (id₌ (y ⁻¹)) (comp₌-assoc z x (left-associator ⁻¹)) ∙
            comp₌-assoc (y ⁻¹) (z ∙ x) (left-associator ⁻¹))
        normalization = normalized ⁻¹ ∙
          ((comp₌-assoc right-associator (y ⁻¹) (z ∙ (x ∙ left-associator ⁻¹))) ⁻¹ ∙ (regroup ∙ raw))

      posted-cell : (uncurry h ◁ Square.cell (product-square {P = P} s)) =₂
        (Kright ⁻¹ ∙ (middle ∙ Kleft))
      posted-cell = comp₌-cong (postWhisker-inverse (uncurry h) (restriction-compositor l v))
        (postWhisker-comp₌ (uncurry h) (productMap-cong (id₌ (id P)) σ) (restriction-compositor u r)) ∙
          postWhisker-comp₌ (uncurry h) ((restriction-compositor l v) ⁻¹)
            (productMap-cong (id₌ (id P)) σ ∙ restriction-compositor u r)

      native-normal : native-expanded =₂ Cocone.match target
      native-normal = comp₌-cong (id₌ (Aright ⁻¹))
          (comp₌-cong (posted-cell ⁻¹) (id₌ Aleft)) ∙
        (comp₌-cong (id₌ (Aright ⁻¹))
          ((comp₌-assoc (Kright ⁻¹) (middle ∙ Kleft) Aleft) ⁻¹ ∙
            comp₌-cong (id₌ (Kright ⁻¹)) ((comp₌-assoc middle Kleft Aleft) ⁻¹)) ∙
          (comp₌-assoc (Aright ⁻¹) (Kright ⁻¹) (middle ∙ (Kleft ∙ Aleft)) ∙
            comp₌-cong (inverse-composite Kright Aright) (id₌ (middle ∙ (Kleft ∙ Aleft)))))

      raw-square : SquareCell₌ raw-match (Cocone.match target) before-left before-right
      raw-square = replace-edges₌ (raw-normal ⁻¹) native-normal
        (inv-comp-square₌ (adjoin-square₌ left-square middle-square) right-square)

    abstract
      matching : SquareCell₌ (left ▷ Ju) (right ▷ Jl) (Cocone.match source) (Cocone.match target)
      matching = transpose-square₌
        (replace-sides₌ (comp-inv-right (left ▷ Ju) Mu) (comp-inv-right (right ▷ Jl) Ml)
          (changeEndpoints-extend-square Mu Ml raw-match raw-square))

    identification : CoconeIdentification₁ source target
    identification = record
      { left = left ; right = right ; compatible = matching }

```

## The actual precomposition action

Evaluation reflects composition of the chosen action on identifications and
its two compositor input squares. The associativity equation retains the
actual precomposition associator image and the chosen compositor routes.

```agda
private
  module PrecompositionCalculation where
    module _ {Γ : Context} where
      module At (E : CAT Γ) where
        F : CAT Γ → CAT Γ
        F C = Map C E
        J : {A B : CAT Γ} → MAP A B → MAP (F B) (F A)
        J = mapPre {D = E}
        R : {A B : CAT Γ} {f g : MAP A B} → f =₁ g → J f =₁ J g
        R = mapPre⁼ {D = E}
        R₂ : {A B : CAT Γ} {f g : MAP A B} {α β : f =₁ g}
          → α =₂ β → R α =₂ R β
        R₂ {B = B} p = curry⁼-cong (map-isAn B E)
          (postWhisker mapEval ◁ productMap-cong₂
            (id₌ (const (id₌ (id (Map B E))))) p)
        K : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C)
          → (J f ∘ J g) =₁ J (g ∘ f)
        K = mapPre-comp {D = E}

        module Identification {A B : CAT Γ} where
          private
            module Native = RestrictionEvaluationAction (F B)
            e : MAP (F B × B) E
            e = mapEval
            N : {f g : MAP A B} → f =₁ g → (e ∘ Native.J f) =₁ (e ∘ Native.J g)
            N α = e ◁ Native.R α
          evaluation : {f g : MAP A B} (α : f =₁ g)
            → SquareCell₌ (uncurry⁼ (R α)) (N α) (mapPre-β f) (mapPre-β g)
          evaluation α = replace-edges₌ (id₌ _)
            (postWhisker e ◁ productMap-cong₂ (const-One (id₌ (id (F B)))) (id₌ α))
            (unconst-sides₌ (mapPre-β-natural α))
          reflect : {f g : MAP A B} (α β : J f =₁ J g)
            (nα nβ : (e ∘ Native.J f) =₁ (e ∘ Native.J g))
            → SquareCell₌ (uncurry⁼ α) nα (mapPre-β f) (mapPre-β g)
            → SquareCell₌ (uncurry⁼ β) nβ (mapPre-β f) (mapPre-β g)
            → nα =₂ nβ → α =₂ β
          reflect {f} {g} α β nα nβ first second p = uncurry⁼-reflect (map-isAn B E) α β
            (cancel-left (mapPre-β g)
              (second ⁻¹ ∙ (comp₌-cong p (id₌ (mapPre-β f)) ∙ first)))
          composition : {f g h : MAP A B} (β : g =₁ h) (α : f =₁ g)
            → R (β ∙ α) =₂ (R β ∙ R α)
          composition β α = reflect (R (β ∙ α)) (R β ∙ R α)
            (N (β ∙ α)) (N β ∙ N α) (evaluation (β ∙ α))
            (replace-edges₌ ((uncurry⁼-composition (R β) (R α)) ⁻¹) (id₌ _)
              (adjoin-square₌ (evaluation α) (evaluation β)))
            (postWhisker-comp₌ e (Native.R β) (Native.R α) ∙
              (postWhisker e ◁ Native.R-comp β α))
          identity : (f : MAP A B) → R (id₌ f) =₂ id₌ (J f)
          identity f =
            let uc-id = const-One (id₌ (uncurry (J f))) ∙
                  (uncurry⁼-identity (J f) ∙ uncurry⁼-cong ((const-One (id₌ (J f))) ⁻¹))
                candidate = replace-edges₌ (uc-id ⁻¹) (id₌ _)
                  (transpose-square₌ (unconst-sides₌ (identity-square₌ (mapPre-β f))))
                native-id = postWhisker-id₌ e (Native.J f) ∙ (postWhisker e ◁ Native.R-id f)
            in reflect (R (id₌ f)) (id₌ (J f)) (N (id₌ f)) (id₌ (e ∘ Native.J f))
              (evaluation (id₌ f)) candidate native-id

        R-comp : {A B : CAT Γ} {f g h : MAP A B}
          (β : g =₁ h) (α : f =₁ g) → R (β ∙ α) =₂ (R β ∙ R α)
        R-comp = Identification.composition
        R-id : {A B : CAT Γ} (f : MAP A B) → R (id₌ f) =₂ id₌ (J f)
        R-id = Identification.identity
        R-inverse : {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g)
          → R (α ⁻¹) =₂ (R α) ⁻¹
        R-inverse {f = f} α = cancel-right (R α)
          ((comp₌-inverseˡ-One (R α)) ⁻¹ ∙
            (R-id f ∙ (R₂ (comp₌-inverseˡ-One α) ∙ (R-comp (α ⁻¹) α) ⁻¹)))
        R-square : {A B : CAT Γ} {x y x′ y′ : MAP A B}
          {t : x =₁ y} {b : x′ =₁ y′} {l : x =₁ x′} {r : y =₁ y′}
          → SquareCell₌ t b l r → SquareCell₌ (R t) (R b) (R l) (R r)
        R-square {t = t} {b} {l} {r} square = R-comp b l ∙ (R₂ square ∙ (R-comp r t) ⁻¹)

        reflect-square : {P A : CAT Γ} {x y x′ y′ : MAP P (Map A E)}
          (pAn : isAn P) {t : x =₁ y} {b : x′ =₁ y′} {l : x =₁ x′} {r : y =₁ y′}
          → SquareCell₌ (uncurry⁼ t) (uncurry⁼ b) (uncurry⁼ l) (uncurry⁼ r)
          → SquareCell₌ t b l r
        reflect-square pAn {t = t} {b} {l} {r} square = uncurry⁼-reflect pAn (r ∙ t) (b ∙ l)
          ((uncurry⁼-composition b l) ⁻¹ ∙ (square ∙ uncurry⁼-composition r t))

        module OuterInput {A B C : CAT Γ} (f : MAP A B)
          {g h : MAP B C} (α : g =₁ h) where
          private
            module N = RestrictionEvaluationAction (F C)
            module L = CompositorEvaluation {E = E} f g
            module H = CompositorEvaluation {E = E} f h
            e : MAP (F C × C) E
            e = mapEval
            Jf = N.J f
            Jg = N.J g
            Jh = N.J h
            source-action = (e ◁ N.R α) ▷ Jf
            target-action = e ◁ N.R (α ▷ f)
            source-square : SquareCell₌ (uncurry⁼ (J f ◁ R α)) source-action L.before H.before
            source-square = paste-square₌
              (unconst-sides₌ (mapPre-uncurry-inputs f (R α)))
              (pre-square₌ Jf (Identification.evaluation α))
            target-square = Identification.evaluation (α ▷ f)
            native-square : SquareCell₌ source-action target-action L.product-route H.product-route
            native-square = paste-square₌ (whisker-mixed-One (N.R α) Jf e)
              (post-square₌ e (N.outer-natural f α))
            transported = replace-sides₌
              ((square-to-changeEndpoints L.before L.after (uncurry⁼ (K f g)) L.product-route L.square) ⁻¹)
              ((square-to-changeEndpoints H.before H.after (uncurry⁼ (K f h)) H.product-route H.square) ⁻¹)
              native-square
            raw-square = reflect-transported-square L.before L.after H.before H.after
              (uncurry⁼ (K f g)) (uncurry⁼ (K f h))
              (uncurry⁼ (J f ◁ R α)) (uncurry⁼ (R (α ▷ f))) source-action target-action
              source-square target-square transported
          compatibility : SquareCell₌ (J f ◁ R α) (R (α ▷ f)) (K f g) (K f h)
          compatibility = reflect-square (map-isAn C E) raw-square

        module InnerInput {A B C : CAT Γ} {f g : MAP A B}
          (α : f =₁ g) (h : MAP B C) where
          private
            module N = RestrictionEvaluationAction (F C)
            module L = CompositorEvaluation {E = E} f h
            module H = CompositorEvaluation {E = E} g h
            e : MAP (F C × C) E
            e = mapEval
            source-action = uncurry (J h) ◁ N.R α
            middle-action = (e ∘ N.J h) ◁ N.R α
            target-action = e ◁ N.R (h ◁ α)
            source-square = ParameterizedInputEvaluation.compatibility (J h) α
            beta-square : SquareCell₌ source-action middle-action
              (mapPre-β h ▷ N.J f) (mapPre-β h ▷ N.J g)
            beta-square = interchange (mapPre-β h) (N.R α)
            before-square : SquareCell₌ (uncurry⁼ (R α ▷ J h)) middle-action L.before H.before
            before-square = paste-square₌ source-square beta-square
            target-square = Identification.evaluation (h ◁ α)
            native-square : SquareCell₌ middle-action target-action L.product-route H.product-route
            native-square = paste-square₌ (postWhisker-comp-One (N.R α) (N.J h) e)
              (post-square₌ e (N.inner-natural α h))
            transported = replace-sides₌
              ((square-to-changeEndpoints L.before L.after (uncurry⁼ (K f h)) L.product-route L.square) ⁻¹)
              ((square-to-changeEndpoints H.before H.after (uncurry⁼ (K g h)) H.product-route H.square) ⁻¹)
              native-square
            raw-square = reflect-transported-square L.before L.after H.before H.after
              (uncurry⁼ (K f h)) (uncurry⁼ (K g h))
              (uncurry⁼ (R α ▷ J h)) (uncurry⁼ (R (h ◁ α))) middle-action target-action
              before-square target-square transported
          compatibility : SquareCell₌ (R α ▷ J h) (R (h ◁ α)) (K f h) (K g h)
          compatibility = reflect-square (map-isAn C E) raw-square

        module Associativity {A B C D : CAT Γ}
          (f : MAP A B) (g : MAP B C) (h : MAP C D) where
          private
            module N = RestrictionEvaluationAction (F D)
            module Param = ParameterizedCompositorEvaluation f g (J h)
            module First = CompositorEvaluation {E = E} (g ∘ f) h
            module Middle = CompositorEvaluation {E = E} g h
            module Last = CompositorEvaluation {E = E} f (h ∘ g)
            e : MAP (F D × D) E
            e = mapEval
            Jf = N.J f
            Jg = N.J g
            Jh = N.J h
            Jgf = N.J (g ∘ f)
            Jhg = N.J (h ∘ g)
            δ = N.K f g
            b = N.K g h
            b′ = N.K (g ∘ f) h
            ρ = N.R (comp-assoc f g h)
            c′ = ρ ∙ N.K f (h ∘ g)
            T = comp-assoc Jf Jg Jh
            β = mapPre-β {D = E} h
            am = comp-assoc (J h) (J g) (J f)
            left = K (g ∘ f) h ∙ (K f g ▷ J h)
            right = R (comp-assoc f g h) ∙
              (K f (h ∘ g) ∙ ((J f ◁ K g h) ∙ am))
            native-inner = ((e ∘ Jh) ◁ δ) ∙ comp-assoc Jf Jg (e ∘ Jh)
            native-left = First.product-route ∙ native-inner
            native-right = (e ◁ ρ) ∙ (Last.product-route ∙ (Middle.product-route ▷ Jf))
            triangle-change : (b′ ∙ (Jh ◁ δ)) =₂ (c′ ∙ restrict-triangle Jh Jg b Jf)
            triangle-change = comp₌-assoc c′ (b ▷ Jf) (T ⁻¹) ∙
              (comp₌-cong
                ((comp₌-assoc ρ (N.K f (h ∘ g)) (b ▷ Jf)) ⁻¹ ∙
                  (restriction-associativity {P = F D} f g h ∙ comp₌-assoc b′ (Jh ◁ δ) T))
                (id₌ (T ⁻¹)) ∙ (comp-inv-right (b′ ∙ (Jh ◁ δ)) T) ⁻¹)
            native-associativity : native-left =₂ native-right
            native-associativity = reassociateFour (e ◁ ρ) (e ◁ N.K f (h ∘ g))
                (comp-assoc Jf Jhg e) (Middle.product-route ▷ Jf) ∙
              (comp₌-cong (postWhisker-comp₌ e ρ (N.K f (h ∘ g)))
                (id₌ (comp-assoc Jf Jhg e ∙ (Middle.product-route ▷ Jf))) ∙
                  post-triangle-change e Jh Jg Jf Jgf δ b b′ c′ triangle-change)
            left-frame = ((β ▷ Jg) ▷ Jf) ∙ Param.before
            beta-frame : SquareCell₌ Param.product-route native-inner
              ((β ▷ Jg) ▷ Jf) (β ▷ Jgf)
            beta-frame = adjoin-square₌ (transpose-square₌ (preWhisker-comp-One β Jg Jf))
              (interchange β δ)
            first-square : SquareCell₌ (uncurry⁼ (K f g ▷ J h)) native-inner left-frame First.before
            first-square = paste-square₌ Param.square beta-frame
            left-square : SquareCell₌ (uncurry⁼ left) native-left left-frame First.after
            left-square = replace-edges₌ ((uncurry⁼-composition (K (g ∘ f) h) (K f g ▷ J h)) ⁻¹) (id₌ native-left)
              (adjoin-square₌ first-square First.square)
            before-action = (Middle.before ▷ Jf) ∙ mapPre-uncurry f (J g ∘ J h)
            frame-assoc : (before-action ∙ uncurry⁼ am) =₂ left-frame
            frame-assoc = comp₌-assoc ((β ▷ Jg) ▷ Jf) (mapPre-uncurry g (J h) ▷ Jf)
                (mapPre-uncurry f (J g ∘ J h) ∙ uncurry⁼ am) ∙
              (comp₌-cong (preWhisker-comp₌ (β ▷ Jg) (mapPre-uncurry g (J h)) Jf)
                (id₌ (mapPre-uncurry f (J g ∘ J h) ∙ uncurry⁼ am)) ∙
                  comp₌-assoc (Middle.before ▷ Jf) (mapPre-uncurry f (J g ∘ J h)) (uncurry⁼ am))
            assoc-square : SquareCell₌ (uncurry⁼ am)
              (id₌ (((e ∘ Jh) ∘ Jg) ∘ Jf)) left-frame before-action
            assoc-square = (comp₌-unitˡ-One left-frame) ⁻¹ ∙ frame-assoc
            action-square : SquareCell₌ (uncurry⁼ (J f ◁ K g h))
              (Middle.product-route ▷ Jf) before-action Last.before
            action-square = paste-square₌ (unconst-sides₌ (mapPre-uncurry-inputs f (K g h)))
              (pre-square₌ Jf Middle.square)
            first-two = replace-edges₌ (id₌ _)
              (comp₌-unitʳ-One (Middle.product-route ▷ Jf)) (adjoin-square₌ assoc-square action-square)
            all-right = adjoin-square₌ (adjoin-square₌ first-two Last.square)
              (Identification.evaluation (comp-assoc f g h))
            raw-right-normal : uncurry⁼ right =₂
              (uncurry⁼ (R (comp-assoc f g h)) ∙
                (uncurry⁼ (K f (h ∘ g)) ∙
                  (uncurry⁼ (J f ◁ K g h) ∙ uncurry⁼ am)))
            raw-right-normal = comp₌-cong (id₌ (uncurry⁼ (R (comp-assoc f g h))))
              (comp₌-cong (id₌ (uncurry⁼ (K f (h ∘ g)))) (uncurry⁼-composition (J f ◁ K g h) am) ∙
                uncurry⁼-composition (K f (h ∘ g)) ((J f ◁ K g h) ∙ am)) ∙
                  uncurry⁼-composition (R (comp-assoc f g h))
                    (K f (h ∘ g) ∙ ((J f ◁ K g h) ∙ am))
            right-square : SquareCell₌ (uncurry⁼ right) native-right left-frame First.after
            right-square = replace-edges₌ (raw-right-normal ⁻¹) (id₌ native-right) all-right

          compatibility : (K (g ∘ f) h ∙ (K f g ▷ J h)) =₂
            (R (comp-assoc f g h) ∙
              (K f (h ∘ g) ∙ ((J f ◁ K g h) ∙ comp-assoc (J h) (J g) (J f))))
          compatibility = uncurry⁼-reflect (map-isAn D E) left right
            (cancel-left First.after
              (right-square ⁻¹ ∙ (comp₌-cong native-associativity (id₌ left-frame) ∙ left-square)))

module _ {Γ : Context} where
  precomposition-action-composition : {A B E : CAT Γ} {f g h : MAP A B}
    (β : g =₁ h) (α : f =₁ g)
    → mapPre⁼ {D = E} (β ∙ α) =₂ (mapPre⁼ β ∙ mapPre⁼ α)
  precomposition-action-composition {E = E} = PrecompositionCalculation.At.R-comp E

  precomposition-compositor-outer : {A B C E : CAT Γ} (f : MAP A B)
    {g h : MAP B C} (α : g =₁ h)
    → SquareCell₌ (mapPre {D = E} f ◁ mapPre⁼ α) (mapPre⁼ (α ▷ f))
        (mapPre-comp f g) (mapPre-comp f h)
  precomposition-compositor-outer {E = E} = PrecompositionCalculation.At.OuterInput.compatibility E

  precomposition-compositor-inner : {A B C E : CAT Γ} {f g : MAP A B}
    (α : f =₁ g) (h : MAP B C)
    → SquareCell₌ (mapPre⁼ {D = E} α ▷ mapPre h) (mapPre⁼ (h ◁ α))
        (mapPre-comp f h) (mapPre-comp g h)
  precomposition-compositor-inner {E = E} = PrecompositionCalculation.At.InnerInput.compatibility E

  precomposition-compositor-associativity : {A B C D E : CAT Γ}
    (f : MAP A B) (g : MAP B C) (h : MAP C D)
    → (mapPre-comp {D = E} (g ∘ f) h ∙ (mapPre-comp f g ▷ mapPre h)) =₂
        (mapPre⁼ (comp-assoc f g h) ∙
          (mapPre-comp f (h ∘ g) ∙
            ((mapPre f ◁ mapPre-comp g h) ∙ comp-assoc (mapPre h) (mapPre g) (mapPre f))))
  precomposition-compositor-associativity {E = E} = PrecompositionCalculation.At.Associativity.compatibility E
```


```agda
module _ {Γ : Context} where
  precomposition-action-inverse : {A B E : CAT Γ} {f g : MAP A B} (α : f =₁ g)
    → mapPre⁼ {D = E} (α ⁻¹) =₂ (mapPre⁼ α) ⁻¹
  precomposition-action-inverse {E = E} = PrecompositionCalculation.At.R-inverse E
```
