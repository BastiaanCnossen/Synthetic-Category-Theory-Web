# Morphisms with specified source and target

A categorical family of arrows can be described by a functor into Ar C,
or by its uncurried interval diagram. Evaluation at a fixed absolute
object computes the source and target in both descriptions. Their chosen
identifications respect the actual identification actions. Encoding and
decoding preserve both endpoint frames and have complete framed
roundtrip identifications. The categorical source P and identification
parameter X remain independent.

The fixed-point evaluation equation traverses left-normal h, then the
inverse of right-normal h. Both routes end at evaluation of pair(h,const a).
All later endpoint equations use this same choice.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section01.Morphisms where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Whiskering
  using (postWhisker-id; preWhisker-id; postWhisker-comp; whisker-mixed)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (contractible-unique)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-constant; pair⁼-square)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair; productMap-pair-outer)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors using (binary-pre; binary-pre-substitution)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate⁼)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry; funCurry-β; funCurry-η; funUncurry; curry⁼; curry⁼-evaluation)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-β)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate⁼-absolute)
open import SCT.VolumeI.Chapter01.Section07.Currying using (reflect-β-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (inverse-identity; comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)

private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    paste-fixed : {P C : CAT Γ} {h k h′ k′ h″ k″ : MAP P C}
      {α : h ＝ k} {β : h′ ＝ k′} {γ : h″ ＝ k″}
      {p : h =₁ h′} {q : k =₁ k′} {r : h′ =₁ h″} {s : k′ =₁ k″}
      → SquareCell₌ α β (const p) (const q)
      → SquareCell₌ β γ (const r) (const s)
      → SquareCell₌ α γ (const (r ∙ p)) (const (s ∙ q))
    paste-fixed {p = p} {q} {r} {s} first second = replace-sides₌
      (const-comp r p) (const-comp s q) (paste-square₌ first second)

    inverse-fixed : {P C : CAT Γ} {h k h′ k′ : MAP P C}
      {α : h ＝ k} {β : h′ ＝ k′} {p : h =₁ h′} {q : k =₁ k′}
      → SquareCell₌ α β (const p) (const q)
      → SquareCell₌ β α (const (p ⁻¹)) (const (q ⁻¹))
    inverse-fixed {p = p} {q} square = replace-sides₌
      ((const-inv p) ⁻¹) ((const-inv q) ⁻¹) (inverse-square₌ square)

    post-fixed : {P C D : CAT Γ} (H : MAP C D)
      {h k h′ k′ : MAP P C} {α : h ＝ k} {β : h′ ＝ k′}
      {p : h =₁ h′} {q : k =₁ k′}
      → SquareCell₌ α β (const p) (const q)
      → SquareCell₌ (H ◁ α) (H ◁ β) (const (H ◁ p)) (const (H ◁ q))
    post-fixed H {p = p} {q} square = replace-sides₌
      (post-constant H p) (post-constant H q) (post-square₌ H square)

    pair-fixed : {P C D : CAT Γ} {h k h′ k′ : MAP P C} {u v u′ v′ : MAP P D}
      {α : h ＝ k} {β : h′ ＝ k′} {γ : u ＝ v} {δ : u′ ＝ v′}
      {p : h =₁ h′} {q : k =₁ k′} {r : u =₁ u′} {s : v =₁ v′}
      → SquareCell₌ α β (const p) (const q)
      → SquareCell₌ γ δ (const r) (const s)
      → SquareCell₌ (pair⁼ α γ) (pair⁼ β δ)
          (const (pair⁼ p r)) (const (pair⁼ q s))
    pair-fixed {p = p} {q} {r} {s} first second = replace-sides₌
      (pair⁼-constant p r) (pair⁼-constant q s) (pair⁼-square first second)

    constant-identity-square : {P C : CAT Γ} {h k : MAP P C} (p : h =₁ k)
      → SquareCell₌ (const {P = X} (id₌ h)) (const (id₌ k)) (const p) (const p)
    constant-identity-square p = (comp₌-unitˡ (const p)) ⁻¹ ∙ comp₌-unitʳ (const p)

module _ {Γ : Context} where
  insert : {P I : CAT Γ} → MAP One I → MAP P (P × I)
  insert {P} a = pair (id P) (const a)

  module AtPoint {I C : CAT Γ} (a : MAP One I) where
    private
      F : CAT Γ
      F = Fun I C
      e : MAP (F × I) C
      e = funEval
    evaluation : MAP F C
    evaluation = e ∘ insert a

    private
      module _ {P : CAT Γ} where
        left-normal : (h : MAP P F) → (evaluation ∘ h) =₁ (e ∘ pair h (const a))
        left-normal h = (e ◁ pair⁼ (comp-unitˡ h) (const-pre a h)) ∙
          binary-pre e (id F) (const {P = F} a) h

        right-normal : (h : MAP P F) → (funUncurry h ∘ insert a) =₁ (e ∘ pair h (const a))
        right-normal h = (e ◁ pair⁼ (comp-unitʳ h) (comp-unitˡ (const {P = P} a))) ∙
          ((e ◁ productMap-pair h (id I) (id P) (const a)) ∙
            comp-assoc (insert a) (productMap h (id I)) e)

    uncurry-image : {P : CAT Γ} (h : MAP P F)
      → (evaluation ∘ h) =₁ (funUncurry h ∘ insert a)
    uncurry-image h = (right-normal h) ⁻¹ ∙ left-normal h

    represented-point : {P : CAT Γ} (h : MAP P F) (H : MAP (P × I) C)
      → funUncurry h =₁ H → (evaluation ∘ h) =₁ (H ∘ insert a)
    represented-point h H beta = (beta ▷ insert a) ∙ uncurry-image h

    curry-image : {P : CAT Γ} (H : MAP (P × I) C)
      → (evaluation ∘ funCurry H) =₁ (H ∘ insert a)
    curry-image H = represented-point (funCurry H) H (funCurry-β H)

    private
      module _ {X P : CAT Γ} where
        open Terms.Equalities X using (_＝_)

        terminal-square : {h k : MAP P F} (α : h ＝ k)
          → SquareCell₌ (terminate F ◁ α) (const (id₌ (terminate P)))
              (const (terminal-identification (terminate F ∘ h) (terminate P)))
              (const (terminal-identification (terminate F ∘ k) (terminate P)))
        terminal-square {h} {k} α = contractible-unique
          (terminal-identifications-isEquiv (terminate F ∘ h) (terminate P))
          (const (terminal-identification (terminate F ∘ k) (terminate P)) ∙ (terminate F ◁ α))
          (const (id₌ (terminate P)) ∙ const (terminal-identification (terminate F ∘ h) (terminate P)))

        constant-pre-square : {h k : MAP P F} (α : h ＝ k)
          → SquareCell₌ (const {P = F} a ◁ α) (const (id₌ (const {P = P} a)))
              (const (const-pre a h)) (const (const-pre a k))
        constant-pre-square α = paste-fixed (postWhisker-comp α (terminate F) a)
          (replace-edges₌ (id₌ _)
            (const-cong (postWhisker-id₌ a (terminate P)) ∙ post-constant a (id₌ (terminate P)))
            (post-fixed a (terminal-square α)))

        left-square : {h k : MAP P F} (α : h ＝ k)
          → SquareCell₌ (evaluation ◁ α) (e ◁ pair⁼ α (const (id₌ (const a))))
              (const (left-normal h)) (const (left-normal k))
        left-square α = paste-fixed
          (binary-pre-substitution e (id F) (const {P = F} a) α)
          (post-fixed e (pair-fixed (postWhisker-id α) (constant-pre-square α)))

        second-unit-square : SquareCell₌ (const {P = X} (id₌ (id I)) ▷ const {P = P} a)
          (const (id₌ (const {P = P} a)))
          (const (comp-unitˡ (const {P = P} a))) (const (comp-unitˡ (const {P = P} a)))
        second-unit-square = replace-edges₌
          ((const-cong (preWhisker-id₌ (id I) (const {P = P} a)) ∙
            pre-constant (id₌ (id I)) (const a)) ⁻¹) (id₌ _)
          (constant-identity-square {X = X} (comp-unitˡ (const {P = P} a)))

        right-square : {h k : MAP P F} (α : h ＝ k)
          → SquareCell₌ (evaluate⁼ e α ▷ insert a) (e ◁ pair⁼ α (const (id₌ (const a))))
              (const (right-normal h)) (const (right-normal k))
        right-square α = paste-fixed
          (paste-fixed
            (whisker-mixed (productMap-cong α (const (id₌ (id I)))) (insert a) e)
            (post-fixed e (productMap-pair-outer α (const (id₌ (id I))) (id P) (const a))))
          (post-fixed e (pair-fixed (preWhisker-id α) second-unit-square))

    module _ {X P : CAT Γ} where
      open Terms.Equalities X using (_＝_)
      uncurry-square : {h k : MAP P F} (α : h ＝ k)
        → SquareCell₌ (evaluation ◁ α) (evaluate⁼ e α ▷ insert a)
            (const (uncurry-image h)) (const (uncurry-image k))
      uncurry-square α = paste-fixed (left-square α) (inverse-fixed (right-square α))

      curry-square : {H K : MAP (P × I) C} (α : H ＝ K)
        → SquareCell₌ (evaluation ◁ curry⁼ e (funUniversal I C) α) (α ▷ insert a)
            (const (curry-image H)) (const (curry-image K))
      curry-square {H} {K} α = paste-fixed
        (uncurry-square (curry⁼ e (funUniversal I C) α))
        (replace-sides₌ (pre-constant (funCurry-β H) (insert a))
          (pre-constant (funCurry-β K) (insert a))
          (pre-square₌ (insert a) (curry⁼-evaluation e (funUniversal I C) α)))

```

A family with specified endpoints records an arrow and its two endpoint
frames. Its identifications retain both compatibility triangles. Currying
and uncurrying act on this entire framed data.

```agda
module _ {Γ : Context} where
  Ar : CAT Γ → CAT Γ
  Ar C = Fun [1] C
  Mor : CAT Γ → Set m
  Mor C = MAP [1] C
  ev₀ ev₁ : {C : CAT Γ} → MAP (Ar C) C
  ev₀ = AtPoint.evaluation zero
  ev₁ = AtPoint.evaluation one

  record MorphismFamily {P C : CAT Γ} (f g : MAP P C) : Set m where
    field
      arrow : MAP P (Ar C)
      source-frame : (ev₀ ∘ arrow) =₁ f
      target-frame : (ev₁ ∘ arrow) =₁ g

  record MorphismFamilyIdentification (X : CAT Γ) {P C : CAT Γ} {f g : MAP P C}
    (α β : MorphismFamily f g) : Set m where
    open Terms.Equalities X using (_＝_)
    field
      identification : MorphismFamily.arrow α ＝ MorphismFamily.arrow β
      source-compatible : (const (MorphismFamily.source-frame β) ∙ (ev₀ ◁ identification))
        =₁ const (MorphismFamily.source-frame α)
      target-compatible : (const (MorphismFamily.target-frame β) ∙ (ev₁ ◁ identification))
        =₁ const (MorphismFamily.target-frame α)

  record DiagramFamily {P C : CAT Γ} (f g : MAP P C) : Set m where
    field
      diagram : MAP (P × [1]) C
      source-frame : (diagram ∘ insert zero) =₁ f
      target-frame : (diagram ∘ insert one) =₁ g

  record DiagramFamilyIdentification (X : CAT Γ) {P C : CAT Γ} {f g : MAP P C}
    (α β : DiagramFamily f g) : Set m where
    open Terms.Equalities X using (_＝_)
    field
      identification : DiagramFamily.diagram α ＝ DiagramFamily.diagram β
      source-compatible : (const (DiagramFamily.source-frame β) ∙ (identification ▷ insert zero))
        =₁ const (DiagramFamily.source-frame α)
      target-compatible : (const (DiagramFamily.target-frame β) ∙ (identification ▷ insert one))
        =₁ const (DiagramFamily.target-frame α)

  encode : {P C : CAT Γ} {f g : MAP P C} → DiagramFamily f g → MorphismFamily f g
  encode α = record
    { arrow = funCurry (DiagramFamily.diagram α)
    ; source-frame = DiagramFamily.source-frame α ∙ AtPoint.curry-image zero (DiagramFamily.diagram α)
    ; target-frame = DiagramFamily.target-frame α ∙ AtPoint.curry-image one (DiagramFamily.diagram α) }

  decode : {P C : CAT Γ} {f g : MAP P C} → MorphismFamily f g → DiagramFamily f g
  decode α = record
    { diagram = funUncurry (MorphismFamily.arrow α)
    ; source-frame = MorphismFamily.source-frame α ∙ (AtPoint.uncurry-image zero (MorphismFamily.arrow α)) ⁻¹
    ; target-frame = MorphismFamily.target-frame α ∙ (AtPoint.uncurry-image one (MorphismFamily.arrow α)) ⁻¹ }

  private
    frame-pasting : {X P C : CAT Γ} {h k h′ k′ f : MAP P C}
      (α : MAP X (Equal h k)) (β : MAP X (Equal h′ k′))
      (p : h =₁ h′) (q : k =₁ k′) (l : h′ =₁ f) (r : k′ =₁ f)
      → SquareCell₌ α β (const p) (const q)
      → (const r ∙ β) =₁ const l
      → (const (r ∙ q) ∙ α) =₁ const (l ∙ p)
    frame-pasting α β p q l r square compatible = const-comp l p ∙
      (comp₌-cong compatible (id₌ (const p)) ∙
        ((comp₌-assoc (const r) β (const p)) ⁻¹ ∙
          (comp₌-cong (id₌ (const r)) square ∙
            (comp₌-assoc (const r) (const q) α ∙
              comp₌-cong ((const-comp r q) ⁻¹) (id₌ α)))))

  encode-identification : {X P C : CAT Γ} {f g : MAP P C} {α β : DiagramFamily f g}
    → DiagramFamilyIdentification X α β → MorphismFamilyIdentification X (encode α) (encode β)
  encode-identification {C = C} {α = α} {β} Φ = record
    { identification = curry⁼ (funEval {C = [1]} {D = C}) (funUniversal [1] C)
        (DiagramFamilyIdentification.identification Φ)
    ; source-compatible = frame-pasting _ _
        (AtPoint.curry-image zero (DiagramFamily.diagram α)) (AtPoint.curry-image zero (DiagramFamily.diagram β))
        (DiagramFamily.source-frame α) (DiagramFamily.source-frame β)
        (AtPoint.curry-square zero (DiagramFamilyIdentification.identification Φ))
        (DiagramFamilyIdentification.source-compatible Φ)
    ; target-compatible = frame-pasting _ _
        (AtPoint.curry-image one (DiagramFamily.diagram α)) (AtPoint.curry-image one (DiagramFamily.diagram β))
        (DiagramFamily.target-frame α) (DiagramFamily.target-frame β)
        (AtPoint.curry-square one (DiagramFamilyIdentification.identification Φ))
        (DiagramFamilyIdentification.target-compatible Φ) }

  decode-identification : {X P C : CAT Γ} {f g : MAP P C} {α β : MorphismFamily f g}
    → MorphismFamilyIdentification X α β → DiagramFamilyIdentification X (decode α) (decode β)
  decode-identification {C = C} {α = α} {β} Φ = record
    { identification = evaluate⁼ (funEval {C = [1]} {D = C}) (MorphismFamilyIdentification.identification Φ)
    ; source-compatible = frame-pasting _ _
        ((AtPoint.uncurry-image zero (MorphismFamily.arrow α)) ⁻¹)
        ((AtPoint.uncurry-image zero (MorphismFamily.arrow β)) ⁻¹)
        (MorphismFamily.source-frame α) (MorphismFamily.source-frame β)
        (inverse-fixed (AtPoint.uncurry-square zero (MorphismFamilyIdentification.identification Φ)))
        (MorphismFamilyIdentification.source-compatible Φ)
    ; target-compatible = frame-pasting _ _
        ((AtPoint.uncurry-image one (MorphismFamily.arrow α)) ⁻¹)
        ((AtPoint.uncurry-image one (MorphismFamily.arrow β)) ⁻¹)
        (MorphismFamily.target-frame α) (MorphismFamily.target-frame β)
        (inverse-fixed (AtPoint.uncurry-square one (MorphismFamilyIdentification.identification Φ)))
        (MorphismFamilyIdentification.target-compatible Φ) }

```

Constant interval diagrams give identity families. An identification of
functors changes the target frame, yielding its associated morphism family.
Natural transformations are morphisms in the functor category.

```agda
module _ {Γ : Context} where
  identity-family : {P C : CAT Γ} (f : MAP P C) → MorphismFamily f f
  identity-family {P} {C} f = record
    { arrow = funCurry (f ∘ pr₁)
    ; source-frame = boundary zero
    ; target-frame = boundary one }
    where
    boundary : (a : MAP One [1]) → (AtPoint.evaluation a ∘ funCurry (f ∘ pr₁)) =₁ f
    boundary a = comp-unitʳ f ∙
      ((f ◁ pair-β₁ (id P) (const a)) ∙
        (comp-assoc (insert a) pr₁ f ∙ AtPoint.curry-image a (f ∘ pr₁)))

  identification-family : {P C : CAT Γ} {f g : MAP P C} → f =₁ g → MorphismFamily f g
  identification-family {f = f} p = record
    { arrow = MorphismFamily.arrow (identity-family f)
    ; source-frame = MorphismFamily.source-frame (identity-family f)
    ; target-frame = p ∙ MorphismFamily.target-frame (identity-family f) }


  source target : {C : CAT Γ} → Mor C → MAP One C
  source h = h ∘ zero
  target h = h ∘ one

  record Morphism {C : CAT Γ} (x y : MAP One C) : Set m where
    field
      diagram : Mor C
      source-frame : source diagram =₁ x
      target-frame : target diagram =₁ y

  NatTrans : (C D : CAT Γ) → Set m
  NatTrans C D = Mor (Fun C D)

  transformation-diagram : {C D : CAT Γ} → NatTrans C D → MAP ([1] × C) D
  transformation-diagram = funUncurry

  diagram-transformation : {C D : CAT Γ} → MAP ([1] × C) D → NatTrans C D
  diagram-transformation = funCurry

  transformation-β : {C D : CAT Γ} (H : MAP ([1] × C) D)
    → transformation-diagram (diagram-transformation H) =₁ H
  transformation-β = funCurry-β

  transformation-η : {C D : CAT Γ} (α : NatTrans C D)
    → diagram-transformation (transformation-diagram α) =₁ α
  transformation-η = funCurry-η

```

The chosen currying beta and eta give the roundtrip identifications. The
endpoint calculations below prove both framing triangles for each roundtrip.

```agda
module _ {Γ : Context} where
  private
    lift-pre-triangle : {X P Q C : CAT Γ} {H K : MAP P C} {f : MAP Q C}
      (i : MAP Q P) (δ : H =₁ K) (p : (H ∘ i) =₁ f) (q : (K ∘ i) =₁ f)
      → (q ∙ (δ ▷ i)) =₂ p
      → (const {P = X} q ∙ (const δ ▷ i)) =₁ const p
    lift-pre-triangle i δ p q compatible = const-cong compatible ∙
      (const-comp q (δ ▷ i) ∙ comp₌-cong (id₌ (const q)) (pre-constant δ i))

    lift-post-triangle : {X P C D : CAT Γ} (π : MAP C D)
      {h k : MAP P C} {f : MAP P D}
      (δ : h =₁ k) (p : (π ∘ h) =₁ f) (q : (π ∘ k) =₁ f)
      → (q ∙ (π ◁ δ)) =₂ p
      → (const {P = X} q ∙ (π ◁ const δ)) =₁ const p
    lift-post-triangle π δ p q compatible = const-cong compatible ∙
      (const-comp q (π ◁ δ) ∙ comp₌-cong (id₌ (const q)) (post-constant π δ))

    remove-frame : {P C : CAT Γ} {a b c d : MAP P C}
      (r : c =₁ d) (β : b =₁ c) (p : a =₁ b)
      → (r ∙ β) =₂ ((r ∙ (β ∙ p)) ∙ p ⁻¹)
    remove-frame r β p = (comp-inv-right (r ∙ β) p ∙
      comp₌-cong ((comp₌-assoc r β p) ⁻¹) (id₌ (p ⁻¹))) ⁻¹

    insert-frame : {P C : CAT Γ} {h k h′ k′ f : MAP P C}
      (α : h =₁ k) (β : h′ =₁ k′) (p : h =₁ h′) (q : k =₁ k′) (r : k =₁ f)
      → SquareCell₌ α β p q
      → (r ∙ α) =₂ ((r ∙ q ⁻¹) ∙ (β ∙ p))
    insert-frame α β p q r square =
      (comp₌-cong (id₌ r) (inv-comp-left q α) ∙
        (comp₌-cong (id₌ r) (comp₌-cong (id₌ (q ⁻¹)) (square ⁻¹)) ∙
          comp₌-assoc r (q ⁻¹) (β ∙ p))) ⁻¹

    eta-image : {P C : CAT Γ} (h : MAP P (Ar C))
      → evaluate⁼ (funEval {C = [1]} {D = C}) (funCurry-η h)
          =₂ funCurry-β (funUncurry h)
    eta-image {C = C} h =
      (comp₌-unitˡ-One (funCurry-β (funUncurry h)) ∙
        comp₌-cong (inverse-identity (funUncurry h)) (id₌ (funCurry-β (funUncurry h)))) ∙
      (reflect-β-One (funEval {C = [1]} {D = C}) (funUniversal [1] C)
        (funCurry (funUncurry h)) h
        ((id₌ (funUncurry h)) ⁻¹ ∙ funCurry-β (funUncurry h)) ∙
        evaluate⁼-absolute (funEval {C = [1]} {D = C}) (funCurry-η h))

    eta-endpoint-square : {P C : CAT Γ} (a : MAP One [1]) (h : MAP P (Ar C))
      → SquareCell₌ (AtPoint.evaluation a ◁ funCurry-η h)
          (funCurry-β (funUncurry h) ▷ insert a)
          (AtPoint.uncurry-image a (funCurry (funUncurry h))) (AtPoint.uncurry-image a h)
    eta-endpoint-square a h = replace-edges₌ (id₌ _) (preWhisker (insert a) ◁ eta-image h)
      (unconst-sides₌ (AtPoint.uncurry-square a (funCurry-η h)))

  decode-encode : {X P C : CAT Γ} {f g : MAP P C} (α : DiagramFamily f g)
    → DiagramFamilyIdentification X (decode (encode α)) α
  decode-encode α = record
    { identification = const (funCurry-β (DiagramFamily.diagram α))
    ; source-compatible = lift-pre-triangle (insert zero) (funCurry-β (DiagramFamily.diagram α)) _ _
        (remove-frame (DiagramFamily.source-frame α)
          (funCurry-β (DiagramFamily.diagram α) ▷ insert zero)
          (AtPoint.uncurry-image zero (funCurry (DiagramFamily.diagram α))))
    ; target-compatible = lift-pre-triangle (insert one) (funCurry-β (DiagramFamily.diagram α)) _ _
        (remove-frame (DiagramFamily.target-frame α)
          (funCurry-β (DiagramFamily.diagram α) ▷ insert one)
          (AtPoint.uncurry-image one (funCurry (DiagramFamily.diagram α)))) }

  encode-decode : {X P C : CAT Γ} {f g : MAP P C} (α : MorphismFamily f g)
    → MorphismFamilyIdentification X (encode (decode α)) α
  encode-decode α = record
    { identification = const (funCurry-η (MorphismFamily.arrow α))
    ; source-compatible = lift-post-triangle ev₀ (funCurry-η (MorphismFamily.arrow α)) _ _
        (insert-frame (ev₀ ◁ funCurry-η (MorphismFamily.arrow α))
          (funCurry-β (funUncurry (MorphismFamily.arrow α)) ▷ insert zero)
          (AtPoint.uncurry-image zero (funCurry (funUncurry (MorphismFamily.arrow α))))
          (AtPoint.uncurry-image zero (MorphismFamily.arrow α))
          (MorphismFamily.source-frame α) (eta-endpoint-square zero (MorphismFamily.arrow α)))
    ; target-compatible = lift-post-triangle ev₁ (funCurry-η (MorphismFamily.arrow α)) _ _
        (insert-frame (ev₁ ◁ funCurry-η (MorphismFamily.arrow α))
          (funCurry-β (funUncurry (MorphismFamily.arrow α)) ▷ insert one)
          (AtPoint.uncurry-image one (funCurry (funUncurry (MorphismFamily.arrow α))))
          (AtPoint.uncurry-image one (MorphismFamily.arrow α))
          (MorphismFamily.target-frame α) (eta-endpoint-square one (MorphismFamily.arrow α))) }
```

Evaluation also acts on the chosen point and respects precomposition of
interval diagrams. The constant-diagram functor is the literal curry of
the first projection; evaluating it gives the identity functor.

```agda
module _ {Γ : Context} where
  evAt : {I C : CAT Γ} → MAP One I → MAP (Fun I C) C
  evAt = AtPoint.evaluation

  evAt-pre : {I J C : CAT Γ} (a : MAP One I) (d : MAP I J)
    → (evAt a ∘ funPre {D = C} d) =₁ evAt (d ∘ a)
  evAt-pre {I} {J} {C} a d =
    (e ◁ pair⁼ (comp-unitˡ (id F)) ((comp-assoc (terminate F) a d) ⁻¹)) ∙
      ((e ◁ productMap-pair (id F) d (id F) (const a)) ∙
        (comp-assoc (insert a) (productMap (id F) d) e ∙
          ((funPre-β {D = C} d ▷ insert a) ∙
            AtPoint.uncurry-image a (funPre {D = C} d))))
    where
    F : CAT Γ
    F = Fun J C
    e : MAP (F × J) C
    e = funEval

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)
    evAt⁼ : {I C : CAT Γ} {a b : MAP One I} → a ＝ b → evAt {C = C} a ＝ evAt b
    evAt⁼ {I} {C} α = funEval {C = I} {D = C} ◁
      pair⁼ (const {P = X} (id₌ (id (Fun I C)))) (α ▷ terminate (Fun I C))

  evAt-cong : {I C : CAT Γ} {a b : MAP One I} → a =₁ b → evAt {C = C} a =₁ evAt b
  evAt-cong = evAt⁼

  constantArrow : (I C : CAT Γ) → MAP C (Fun I C)
  constantArrow I C = funCurry {C = I} {D = C} (pr₁ {C = C} {D = I})

  constantArrow-image : (I C : CAT Γ)
    → funUncurry (constantArrow I C) =₁ (pr₁ {C = C} {D = I})
  constantArrow-image I C = funCurry-β (pr₁ {C = C} {D = I})

  evAt-constant : {I C : CAT Γ} (a : MAP One I)
    → (evAt a ∘ constantArrow I C) =₁ id C
  evAt-constant {I} {C} a = pair-β₁ (id C) (const a) ∙
    AtPoint.curry-image a (pr₁ {C = C} {D = I})

  identityArrow : {C : CAT Γ} → MAP C (Ar C)
  identityArrow {C} = constantArrow [1] C

  identity-source : {C : CAT Γ} → (ev₀ ∘ identityArrow) =₁ id C
  identity-source = evAt-constant zero
  identity-target : {C : CAT Γ} → (ev₁ ∘ identityArrow) =₁ id C
  identity-target = evAt-constant one
```
