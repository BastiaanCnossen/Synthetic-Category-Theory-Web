# Functors as points of mapping animae

Naming uses the curried representation of f composed with the second
projection. Decoding inserts the terminal first coordinate after uncurrying.
The terminal category is essential to these operations. Identification
families have an independent arbitrary parameter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Points where

import SCT.VolumeI.Chapter01.Section02.Naturality as N

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (preWhisker-comp; preWhisker-id)
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
  using (pre-square₌; paste-square₌; replace-sides₌; replace-edges₌)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-compose; equiv-reflect)
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor; triangle; factor-through-equiv)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (preWhisker-isEquiv; factor-through-postWhisker)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying

module _ {Γ : Context} {C D : CAT Γ} where
  open Terms.InContext (One {Γ}) using (Term)

  name-representation : (f : MAP C D) → CurriedRepresentation (f ∘ pr₂ {C = One})
  name-representation f = curried-representation one-isAn (f ∘ pr₂)

  name : MAP C D → Term (Map C D)
  name f = CurriedRepresentation.term (name-representation f)

  decode : Term (Map C D) → MAP C D
  decode a = uncurry a ∘ product-unitˡ-inverse C

  decode-name : (f : MAP C D) → decode (name f) =₁ f
  decode-name f = comp-unitʳ f ∙
    ((f ◁ product-unitˡ-pr₂-inverse C) ∙
      (comp-assoc (product-unitˡ-inverse C) pr₂ f ∙
        (CurriedRepresentation.evaluation (name-representation f) ▷ product-unitˡ-inverse C)))

  name-decode : (a : Term (Map C D)) → name (decode a) =₁ a
  name-decode a = uncurry-reflect one-isAn _ a
    (comp-unitʳ (uncurry a) ∙
      ((uncurry a ◁ product-unitˡ-inverse-pr₂ C) ∙
        (comp-assoc pr₂ (product-unitˡ-inverse C) (uncurry a) ∙
          CurriedRepresentation.evaluation (name-representation (decode a)))))
```

## Family actions and their equivalent functors

The primary naming action is the direct currying formula. The actual naming
functor is currying's specified action after prewhiskering by pr₂. Decoding's
primary action evaluates its actual functor. Both equivalence proofs use
only the existing terminal-product and uncurrying equivalences.

```agda
  name⁼-functor : (f g : MAP C D) → MAP (Equal f g) (Equal (name f) (name g))
  name⁼-functor f g = curry⁼-functor one-isAn (f ∘ pr₂) (g ∘ pr₂) ∘ preWhisker pr₂

  name⁼-isEquiv : (f g : MAP C D) → IsEquiv (name⁼-functor f g)
  name⁼-isEquiv f g = equiv-compose (preWhisker pr₂)
    (curry⁼-functor one-isAn (f ∘ pr₂) (g ∘ pr₂))
    (preWhisker-isEquiv pr₂ (product-unitˡ-isEquiv C) f g)
    (curry⁼-isEquiv one-isAn (f ∘ pr₂) (g ∘ pr₂))

  decode⁼-functor : (a b : Term (Map C D)) → MAP (Equal a b) (Equal (decode a) (decode b))
  decode⁼-functor a b = preWhisker (product-unitˡ-inverse C) ∘ uncurry⁼-functor a b

  decode⁼-isEquiv : (a b : Term (Map C D)) → IsEquiv (decode⁼-functor a b)
  decode⁼-isEquiv a b = equiv-compose (uncurry⁼-functor a b)
    (preWhisker (product-unitˡ-inverse C)) (uncurry⁼-isEquiv one-isAn a b)
    (preWhisker-isEquiv (product-unitˡ-inverse C) (product-unitˡ-inverse-isEquiv C)
      (uncurry a) (uncurry b))

  module _ {X : CAT Γ} where
    open Terms.Equalities X

    name⁼ : {f g : MAP C D} → f ＝ g → name f ＝ name g
    name⁼ α = curry⁼ one-isAn (α ▷ pr₂)

    name⁼-functor-evaluate : {f g : MAP C D} (α : f ＝ g)
      → (name⁼-functor f g ∘ α) =₁ name⁼ α
    name⁼-functor-evaluate {f} {g} α = curry⁼-functor-evaluate one-isAn (α ▷ pr₂) ∙
      comp-assoc α (preWhisker pr₂) (curry⁼-functor one-isAn (f ∘ pr₂) (g ∘ pr₂))

    name⁼-evaluation : {f g : MAP C D} (α : f ＝ g)
      → SquareCell₌ (uncurry⁼ (name⁼ α)) (α ▷ pr₂)
          (const (CurriedRepresentation.evaluation (name-representation f)))
          (const (CurriedRepresentation.evaluation (name-representation g)))
    name⁼-evaluation α = curry⁼-evaluation one-isAn (α ▷ pr₂)

    decode⁼ : {a b : Term (Map C D)} → a ＝ b → decode a ＝ decode b
    decode⁼ {a} {b} α = decode⁼-functor a b ∘ α

    decode⁼-evaluate : {a b : Term (Map C D)} (α : a ＝ b)
      → decode⁼ α =₁ (uncurry⁼ α ▷ product-unitˡ-inverse C)
    decode⁼-evaluate {a} {b} α =
      comp-assoc α (uncurry⁼-functor a b) (preWhisker (product-unitˡ-inverse C))
```

## Recovery and higher consequences

Each recovery uses a single chosen inverse of its actual equivalent action.
The naming image law includes the evaluation comparison with the direct
formula. There is no competing decode-and-change-endpoints naming recovery.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    name-reflection : (f g : MAP C D) (α : name f ＝ name g)
      → Factorization (name⁼-functor f g) α
    name-reflection f g = factor-through-equiv (name⁼-isEquiv f g)

    name-reflect : (f g : MAP C D) → name f ＝ name g → f ＝ g
    name-reflect f g α = factor (name-reflection f g α)

    name-reflect-β : (f g : MAP C D) (α : name f ＝ name g)
      → name⁼ (name-reflect f g α) =₁ α
    name-reflect-β f g α = triangle (name-reflection f g α) ∙
      (name⁼-functor-evaluate (name-reflect f g α)) ⁻¹

    decode-reflection : (a b : Term (Map C D)) (α : decode a ＝ decode b)
      → Factorization (decode⁼-functor a b) α
    decode-reflection a b = factor-through-equiv (decode⁼-isEquiv a b)

    decode-reflect : (a b : Term (Map C D)) → decode a ＝ decode b → a ＝ b
    decode-reflect a b α = factor (decode-reflection a b α)

    decode-reflect-β : (a b : Term (Map C D)) (α : decode a ＝ decode b)
      → decode⁼ (decode-reflect a b α) =₁ α
    decode-reflect-β a b α = triangle (decode-reflection a b α)

    name⁼-cong : {f g : MAP C D} {α β : f ＝ g}
      → α =₁ β → name⁼ α =₁ name⁼ β
    name⁼-cong p = curry⁼-cong one-isAn (preWhisker pr₂ ◁ p)

    decode⁼-cong : {a b : Term (Map C D)} {α β : a ＝ b}
      → α =₁ β → decode⁼ α =₁ decode⁼ β
    decode⁼-cong {a} {b} p = decode⁼-functor a b ◁ p

    name⁼-reflect : {f g : MAP C D} (α β : f ＝ g)
      → name⁼ α =₁ name⁼ β → α =₁ β
    name⁼-reflect {f} {g} α β p = equiv-reflect (name⁼-isEquiv f g) α β
      ((name⁼-functor-evaluate β) ⁻¹ ∙ (p ∙ name⁼-functor-evaluate α))

    decode⁼-reflect : {a b : Term (Map C D)} (α β : a ＝ b)
      → decode⁼ α =₁ decode⁼ β → α =₁ β
    decode⁼-reflect {a} {b} = equiv-reflect (decode⁼-isEquiv a b)

    decode⁼-reflection : {Y : CAT Γ} {a b : Term (Map C D)} (α β : a ＝ b)
      (p : MAP Y (Equal (decode⁼ α) (decode⁼ β)))
      → Factorization (postWhisker (decode⁼-functor a b)) p
    decode⁼-reflection {a = a} {b} α β p =
      factor-through-postWhisker (decode⁼-functor a b) (decode⁼-isEquiv a b) p

    decode⁼-restrict : {Y : CAT Γ} {a b : Term (Map C D)}
      (α : a ＝ b) (r : MAP Y X) → (decode⁼ α ∘ r) =₁ decode⁼ (α ∘ r)
    decode⁼-restrict {a = a} {b} α r = comp-assoc r α (decode⁼-functor a b)
```

## The two round-trip operations

Their family actions are the literal composite naming and decoding actions.

```agda
  decode-name-operation : N.Operation (MAP C D) (N.HomChange C D) C D
  decode-name-operation = record { value = λ f → decode (name f); action = λ α → decode⁼ (name⁼ α) }

  name-decode-operation : N.Operation (Term (Map C D)) (N.HomChange (One {Γ}) (Map C D)) One (Map C D)
  name-decode-operation = record { value = λ a → name (decode a); action = λ α → name⁼ (decode⁼ α) }
```

## The decoded-name computation square

This square uses the already chosen decode-name components. Prewhisker
the currying square by terminal insertion, then paste associator naturality,
fixed-input interchange for the terminal retraction, and unitor naturality.
The constant-side normalization retains the literal composite components.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    opaque
      decode-name-natural : {f g : MAP C D} (α : f ＝ g)
        → N.NaturalityAt decode-name-operation (N.Input C D) decode-name α
      decode-name-natural {f} {g} α =
        let insertion = product-unitˡ-inverse C
            retract = product-unitˡ-pr₂-inverse C
            beta : (h : MAP C D) → uncurry (name h) =₁ (h ∘ pr₂)
            beta h = CurriedRepresentation.evaluation (name-representation h)
            normalize : (h : MAP C D)
              → (const (comp-unitʳ h) ∙ (const (h ◁ retract) ∙
                  (const (comp-assoc insertion pr₂ h) ∙ const (beta h ▷ insertion)))) =₁
                const (decode-name h)
            normalize h = const-comp (comp-unitʳ h)
                ((h ◁ retract) ∙ (comp-assoc insertion pr₂ h ∙ (beta h ▷ insertion))) ∙
              comp₌-cong (id₌ (const (comp-unitʳ h)))
                (const-comp (h ◁ retract) (comp-assoc insertion pr₂ h ∙ (beta h ▷ insertion)) ∙
                  comp₌-cong (id₌ (const (h ◁ retract)))
                    (const-comp (comp-assoc insertion pr₂ h) (beta h ▷ insertion)))
            evaluation-square = replace-sides₌ (pre-constant (beta f) insertion)
              (pre-constant (beta g) insertion) (pre-square₌ insertion (name⁼-evaluation α))
            pasted = paste-square₌
              (paste-square₌ (paste-square₌ evaluation-square (preWhisker-comp α pr₂ insertion))
                ((interchange-fixedInner α retract) ⁻¹)) (preWhisker-id α)
        in replace-edges₌ ((decode⁼-evaluate (name⁼ α)) ⁻¹) (id₌ α)
          (replace-sides₌ (normalize f) (normalize g) pasted)
```

## The named-decode computation square

The specified image of name-decode is its original beta/associator/section/
unitor composite. Paste the currying square with restriction associativity,
fixed-input interchange for the terminal section and unitor naturality to
obtain the image square. The constant and composition laws of the primary
uncurrying action then allow reflection of the complete equation.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X

    opaque
      name-decode-natural : {a b : Term (Map C D)} (α : a ＝ b)
        → N.NaturalityAt name-decode-operation (N.Input (One {Γ}) (Map C D)) name-decode α
      name-decode-natural {a} {b} α =
        let insertion = product-unitˡ-inverse C
            section = product-unitˡ-inverse-pr₂ C
            beta : (z : Term (Map C D)) → uncurry (name (decode z)) =₁ (decode z ∘ pr₂)
            beta z = CurriedRepresentation.evaluation (name-representation (decode z))
            image : (z : Term (Map C D)) → uncurry (name (decode z)) =₁ uncurry z
            image z = comp-unitʳ (uncurry z) ∙
              ((uncurry z ◁ section) ∙
                (comp-assoc pr₂ insertion (uncurry z) ∙ beta z))
            image-law : (z : Term (Map C D)) → uncurry⁼ (name-decode z) =₁ image z
            image-law z = uncurry-reflect-β one-isAn _ z (image z)
            constant-image : (z : Term (Map C D))
              → uncurry⁼ (const {P = X} (name-decode z)) =₁ const (image z)
            constant-image z = const-cong (image-law z) ∙ uncurry⁼-constant (name-decode z)
            normalize : (z : Term (Map C D))
              → (const (comp-unitʳ (uncurry z)) ∙ (const (uncurry z ◁ section) ∙
                  (const (comp-assoc pr₂ insertion (uncurry z)) ∙ const (beta z)))) =₁
                const (image z)
            normalize z = const-comp (comp-unitʳ (uncurry z))
                ((uncurry z ◁ section) ∙ (comp-assoc pr₂ insertion (uncurry z) ∙ beta z)) ∙
              comp₌-cong (id₌ (const (comp-unitʳ (uncurry z))))
                (const-comp (uncurry z ◁ section) (comp-assoc pr₂ insertion (uncurry z) ∙ beta z) ∙
                  comp₌-cong (id₌ (const (uncurry z ◁ section)))
                    (const-comp (comp-assoc pr₂ insertion (uncurry z)) (beta z)))
            evaluation-square = replace-edges₌ (id₌ (uncurry⁼ (name⁼ (decode⁼ α))))
              (preWhisker pr₂ ◁ decode⁼-evaluate α) (name⁼-evaluation (decode⁼ α))
            pasted = paste-square₌
              (paste-square₌
                (paste-square₌ evaluation-square (preWhisker-comp (uncurry⁼ α) insertion pr₂))
                ((interchange-fixedInner (uncurry⁼ α) section) ⁻¹)) (preWhisker-id (uncurry⁼ α))
            image-square = replace-sides₌ ((constant-image a) ⁻¹) ((constant-image b) ⁻¹)
              (replace-sides₌ (normalize a) (normalize b) pasted)
        in uncurry⁼-reflect one-isAn _ _
          ((uncurry⁼-composition α (const (name-decode a))) ⁻¹ ∙
            (image-square ∙ uncurry⁼-composition (const (name-decode b)) (name⁼ (decode⁼ α))))
```

## The full round-trip properties

Both adapters evaluate the same proved square, with the original components.

```agda
  decode-name-naturality : N.Naturality decode-name-operation (N.Input C D) decode-name
  decode-name-naturality α = decode-name-natural α

  name-decode-naturality : N.Naturality name-decode-operation (N.Input (One {Γ}) (Map C D)) name-decode
  name-decode-naturality α = name-decode-natural α
```
