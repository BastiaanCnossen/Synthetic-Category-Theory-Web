# Equivalences of categories

This follows Section 1.3 through the 2-out-of-6 lemma. Equivalences carry
a chosen inverse and two identifications. The arguments below use only the
ambient composition operations in a fixed context; product universality is
not needed. The terminal-codomain results also use the terminal axiom.
Factorizations through an equivalence are constructed in Factorizations,
which uses the relative vocabulary.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Equivalences where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open import SCT.VolumeI.Chapter01.Section03.Squares

open Operations
open Composition
```

## Reflection of identifications

`ReflectsIdentifications f X` says that identifications between functors
from the explicit testing category `X` are reflected by postcomposition
with `f`. No reflection at other testing categories, and no compatibility
of the reflected identifications, is part of this hypothesis. A chosen
inverse supplies reflection at every testing category.

```agda
module _ {Γ : Context} where
  ReflectsIdentifications : {C D : CAT Γ} → MAP C D → CAT Γ → Set m
  ReflectsIdentifications {C} f X =
    (u v : MAP X C) → (f ∘ u) =₁ (f ∘ v) → u =₁ v

  equiv-reflect : {C D X : CAT Γ} {f : MAP C D}
    → IsEquiv f → ReflectsIdentifications f X
  equiv-reflect {C = C} {X = X} {f = f} e u v α =
    let g = IsEquiv.inverse e
        unit-at : (w : MAP X C) → w =₁ (g ∘ (f ∘ w))
        unit-at w = comp-assoc w f g ∙ ((IsEquiv.left-inverse-law e ▷ w) ∙ (comp-unitˡ w) ⁻¹)
    in (unit-at v) ⁻¹ ∙ ((g ◁ α) ∙ unit-at u)
```

## Sections, retractions and inverse identifications

Both laws start at the identity functor. A section and a retraction
are identified by inserting one law, reassociating, and cancelling the other.
This gives an equivalence from separately chosen one-sided inverses, and an
identification between any two chosen inverses. No uniqueness of that
identification is asserted here.

```agda
module _ {Γ : Context} where
  record Section {C D : CAT Γ} (f : MAP C D) : Set m where
    field
      section : MAP D C
      section-law : (id D) =₁ (f ∘ section)

  record Retraction {C D : CAT Γ} (f : MAP C D) : Set m where
    field
      retraction : MAP D C
      retraction-law : (id C) =₁ (retraction ∘ f)

  equiv-section : {C D : CAT Γ} {f : MAP C D} → IsEquiv f → Section f
  equiv-section e = record
    { section = IsEquiv.inverse e
    ; section-law = IsEquiv.right-inverse-law e }

  equiv-retraction : {C D : CAT Γ} {f : MAP C D} → IsEquiv f → Retraction f
  equiv-retraction e = record
    { retraction = IsEquiv.inverse e
    ; retraction-law = IsEquiv.left-inverse-law e }

  section-retraction-equal : {C D : CAT Γ} {f : MAP C D}
    (s : Section f) (r : Retraction f)
    → (Section.section s) =₁ (Retraction.retraction r)
  section-retraction-equal {f = f} s r =
    let u = Section.section s
        v = Retraction.retraction r
    in comp-unitʳ v ∙ ((v ◁ (Section.section-law s) ⁻¹) ∙
       (comp-assoc u f v ∙ ((Retraction.retraction-law r ▷ u) ∙ (comp-unitˡ u) ⁻¹)))

  section-retraction-isEquiv : {C D : CAT Γ} {f : MAP C D}
    → Section f → Retraction f → IsEquiv f
  section-retraction-isEquiv {f = f} s r = record
    { inverse = Section.section s
    ; left-inverse-law = ((section-retraction-equal s r) ⁻¹ ▷ f) ∙ Retraction.retraction-law r
    ; right-inverse-law = Section.section-law s }

  inverse-unique : {C D : CAT Γ} {f : MAP C D} (e e′ : IsEquiv f)
    → (IsEquiv.inverse e) =₁ (IsEquiv.inverse e′)
  inverse-unique e e′ = section-retraction-equal (equiv-section e) (equiv-retraction e′)
```

## Identity, inversion, transport and composition

The inverse of a composite is the reversed composite of the chosen inverses.
The two displayed calculations establish its inverse laws.

```agda
module _ {Γ : Context} where
  id-isEquiv : (C : CAT Γ) → IsEquiv (id C)
  id-isEquiv C = record
    { inverse = id C
    ; left-inverse-law = (comp-unitˡ (id C)) ⁻¹
    ; right-inverse-law = (comp-unitˡ (id C)) ⁻¹ }

  equiv-inverse : {C D : CAT Γ} {f : MAP C D} (e : IsEquiv f)
    → IsEquiv (IsEquiv.inverse e)
  equiv-inverse {f = f} e = record
    { inverse = f ; left-inverse-law = IsEquiv.right-inverse-law e ; right-inverse-law = IsEquiv.left-inverse-law e }

  equiv-transport : {C D : CAT Γ} {f g : MAP C D}
    → f =₁ g → IsEquiv f → IsEquiv g
  equiv-transport α e = record
    { inverse = IsEquiv.inverse e
    ; left-inverse-law = (IsEquiv.inverse e ◁ α) ∙ IsEquiv.left-inverse-law e
    ; right-inverse-law = (α ▷ IsEquiv.inverse e) ∙ IsEquiv.right-inverse-law e }

  equiv-compose : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → IsEquiv f → IsEquiv g → IsEquiv (g ∘ f)
  equiv-compose {C} {D} {E} f g ef eg =
    let u : MAP D C
        u = IsEquiv.inverse ef
        v : MAP E D
        v = IsEquiv.inverse eg
        --! begin equiv-compose-left
        left : ((u ∘ v) ∘ (g ∘ f)) =₁ (id C)
        left = (IsEquiv.left-inverse-law ef) ⁻¹ ∙
          ((u ◁ comp-unitˡ f) ∙ ((u ◁ ((IsEquiv.left-inverse-law eg) ⁻¹ ▷ f)) ∙
          ((u ◁ (comp-assoc f g v) ⁻¹) ∙ comp-assoc (g ∘ f) v u)))
        --! end equiv-compose-left
        --! begin equiv-compose-right
        right : ((g ∘ f) ∘ (u ∘ v)) =₁ (id E)
        right = (IsEquiv.right-inverse-law eg) ⁻¹ ∙
          ((g ◁ comp-unitˡ v) ∙ ((g ◁ ((IsEquiv.right-inverse-law ef) ⁻¹ ▷ v)) ∙
          ((g ◁ (comp-assoc v u f) ⁻¹) ∙ comp-assoc (u ∘ v) f g)))
        --! end equiv-compose-right
    in record { inverse = u ∘ v ; left-inverse-law = left ⁻¹ ; right-inverse-law = right ⁻¹ }
```

## Two-out-of-three

To cancel `f` or `g`, compose with its chosen inverse and transport the
resulting equivalence along the displayed identification.

```agda
module _ {Γ : Context} where
  equiv-cancel-right : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → IsEquiv f → IsEquiv (g ∘ f) → IsEquiv g
  equiv-cancel-right f g ef egf =
    let u = IsEquiv.inverse ef
        cancel-f : ((g ∘ f) ∘ u) =₁ g
        cancel-f = comp-unitʳ g ∙ ((g ◁ (IsEquiv.right-inverse-law ef) ⁻¹) ∙ comp-assoc u f g)
    in equiv-transport cancel-f (equiv-compose u (g ∘ f) (equiv-inverse ef) egf)

  equiv-cancel-left : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → IsEquiv g → IsEquiv (g ∘ f) → IsEquiv f
  equiv-cancel-left f g eg egf =
    let v = IsEquiv.inverse eg
        cancel-g : (v ∘ (g ∘ f)) =₁ f
        cancel-g = comp-unitˡ f ∙ (((IsEquiv.left-inverse-law eg) ⁻¹ ▷ f) ∙ (comp-assoc f g v) ⁻¹)
    in equiv-transport cancel-g (equiv-compose (g ∘ f) v egf (equiv-inverse eg))
```

## Equivalences in a commutative square

Take a square `P : Square f f′` whose second functor `f′` and target map
are equivalences. Then `f` is an equivalence if and only if the source map
is. The cell identifies the two composites, so transport and two-out-of-three
supply both directions.

```agda
module _ {Γ : Context} where
  square-source-map-isEquiv : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    (P : Square f f′) → IsEquiv f′ → IsEquiv (Square.target-map P)
    → IsEquiv f → IsEquiv (Square.source-map P)
  square-source-map-isEquiv {f = f} {f′} P ef′ et ef =
    equiv-cancel-left (Square.source-map P) f′ ef′
      (equiv-transport ((Square.cell P) ⁻¹)
        (equiv-compose f (Square.target-map P) ef et))

  square-functor-isEquiv : {A B A′ B′ : CAT Γ} {f : MAP A B} {f′ : MAP A′ B′}
    (P : Square f f′) → IsEquiv f′ → IsEquiv (Square.target-map P)
    → IsEquiv (Square.source-map P) → IsEquiv f
  square-functor-isEquiv {f = f} {f′} P ef′ et es =
    equiv-cancel-left f (Square.target-map P) et
      (equiv-transport (Square.cell P)
        (equiv-compose (Square.source-map P) f′ es ef′))
```

## Two-out-of-six

Inverses of `g ∘ f` and `h ∘ g` give a section and a retraction of `g`.
Once `g` is an equivalence, the cancellation results give the other two
equivalences and hence the triple composite.

```agda
module _ {Γ : Context} where
  record TwoOutOfSix {C D E F : CAT Γ}
    (f : MAP C D) (g : MAP D E) (h : MAP E F) : Set m where
    field
      first : IsEquiv f
      middle : IsEquiv g
      last : IsEquiv h
      composite : IsEquiv (h ∘ (g ∘ f))

  two-out-of-six : {C D E F : CAT Γ}
    (f : MAP C D) (g : MAP D E) (h : MAP E F)
    → IsEquiv (g ∘ f) → IsEquiv (h ∘ g) → TwoOutOfSix f g h
  two-out-of-six f g h egf ehg =
    --! begin two-out-of-six-inverses
    let u = IsEquiv.inverse egf
        v = IsEquiv.inverse ehg
    --! end two-out-of-six-inverses
        --! begin two-out-of-six-section
        s : Section g
        s = record { section = f ∘ u
                   ; section-law = comp-assoc u f g ∙ IsEquiv.right-inverse-law egf }
        --! end two-out-of-six-section
        --! begin two-out-of-six-retraction
        r : Retraction g
        r = record { retraction = v ∘ h
                   ; retraction-law = (comp-assoc g h v) ⁻¹ ∙ IsEquiv.left-inverse-law ehg }
        --! end two-out-of-six-retraction
        --! begin two-out-of-six-middle
        eg : IsEquiv g
        eg = section-retraction-isEquiv s r
        --! end two-out-of-six-middle
        --! begin two-out-of-six-conclusion
        ef = equiv-cancel-left f g eg egf
        eh = equiv-cancel-right g h eg ehg
    in record { first = ef ; middle = eg ; last = eh
              ; composite = equiv-compose (g ∘ f) h egf eh }
        --! end two-out-of-six-conclusion
```

## Identifications with terminal codomain

The terminal axiom makes each identification category between two functors
into `One` contractible. Reflecting an identification through its equivalence
with `One` therefore compares any two of its absolute objects. This needs no
mapping-anima structure or higher whiskering coherence.

```agda
module _ {Γ : Context} where
  open Terminal using (terminal-identifications-isEquiv)
  open Terminal.Constructions using (terminal-identification)

  terminal-unique₂ : {X : CAT Γ} {f g : MAP X One} (α β : f =₁ g) → α =₂ β
  terminal-unique₂ {f = f} {g} α β =
    equiv-reflect (terminal-identifications-isEquiv f g) α β (terminal-identification _ _)
```

## Contractible categories

Transport contractibility to the source of an equivalence. Reflection
through the terminal equivalence compares functors with a contractible
codomain; their source remains an arbitrary category.

```agda
module _ {Γ : Context} where
  open Terminal using (terminate)
  open Terminal.Constructions using (IsContractible; terminal-identification)

  contractible-source : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv f → IsContractible D → IsContractible C
  contractible-source {C} {D} f e h = equiv-transport
    (terminal-identification (terminate D ∘ f) (terminate C))
    (equiv-compose f (terminate D) e h)

  contractible-unique : {C X : CAT Γ} → IsContractible C
    → (f g : MAP X C) → f =₁ g
  contractible-unique {C} e f g = equiv-reflect e f g (terminal-identification _ _)
```
