# Weak changes of theory

An assignment acts on categories and functors, preserves animae, and compares the terminal and identification categories by equivalences. A weakening additionally has identity and composition comparisons. The full primitive preservation data are supplied separately.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Core where

open import SCT.VolumeI.Chapter05.Section01.Prelude

-- A deliberately minimal interface, NOT a morphism of the whole Theory.
record Assignment {l : Level} (S T : Theory l l l) : Set l where
  private
    module S = View S
    module T = View T
  field
    cat : S.CAT → T.CAT
    map : {C D : S.CAT} → S.MAP C D → T.MAP (cat C) (cat D)
    anima : {C : S.CAT} → S.isAn C → T.isAn (cat C)
    terminal : T.Equiv (cat S.One) T.One
    path : {C D : S.CAT} (f g : S.MAP C D)
      → T.Equiv (cat (S._＝_ f g)) (T._＝_ (map f) (map g))

module Transport {l : Level} {S T : Theory l l l} (W : Assignment S T) where
  private
    module S = View S
    module T = View T
  open Assignment W

  phi : {C D : S.CAT} (f g : S.MAP C D)
    → T.MAP (cat (S._＝_ f g)) (T._＝_ (map f) (map g))
  phi f g = T.Equiv.functor (path f g)

  back : T.MAP T.One (cat S.One)
  back = T.IsEquiv.inverse (T.Equiv.isEquiv terminal)

  term : {C D : S.CAT} {f g : S.MAP C D}
    → S._=₁_ f g → T._=₁_ (map f) (map g)
  term {f = f} {g} alpha = T._∘_ (T._∘_ (phi f g) (map alpha)) back

  lift2 : {C D : S.CAT} {f g : S.MAP C D}
    (alpha beta : S._=₁_ f g)
    → T.MAP (T._＝_ (map alpha) (map beta)) (T._＝_ (term alpha) (term beta))
  lift2 {f = f} {g} alpha beta =
    T._∘_ (T.preWhisker back) (T.postWhisker (phi f g))

  cell2 : {C D : S.CAT} {f g : S.MAP C D}
    {alpha beta : S._=₁_ f g} → S._=₂_ alpha beta → T._=₂_ (term alpha) (term beta)
  cell2 {alpha = alpha} {beta} p = T._∘_ (lift2 alpha beta) (term p)

  cell3 : {C D : S.CAT} {f g : S.MAP C D}
    {alpha beta : S._=₁_ f g} {p q : S._=₂_ alpha beta}
    → S._=₃_ p q → T._=₃_ (cell2 p) (cell2 q)
  cell3 {alpha = alpha} {beta} r = T._◁_ (lift2 alpha beta) (cell2 r)

record Weakening {l : Level} (S T : Theory l l l) : Set l where
  private
    module S = View S
    module T = View T
  field
    assignment : Assignment S T
  open Assignment assignment public
  open Transport assignment public
  field
    unit : (C : S.CAT) → T._=₁_ (map (S.id C)) (T.id (cat C))
    comp : {C D E : S.CAT} (f : S.MAP C D) (g : S.MAP D E)
      → T._=₁_ (map (S._∘_ g f)) (T._∘_ (map g) (map f))

module Results {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W

  preservesEquiv : {C D : S.CAT} {f : S.MAP C D} → S.IsEquiv f → T.IsEquiv (map f)
  preservesEquiv {C} {D} {f} e = record
    { inverse = map (S.IsEquiv.inverse e)
    ; sectionIso = T._∙_ (comp f (S.IsEquiv.inverse e))
        (T._∙_ (term (S.IsEquiv.sectionIso e)) (T._⁻¹ (unit C)))
    ; retractionIso = T._∙_ (comp (S.IsEquiv.inverse e) f)
        (T._∙_ (term (S.IsEquiv.retractionIso e)) (T._⁻¹ (unit D))) }

  equiv : {C D : S.CAT} → S.Equiv C D → T.Equiv (cat C) (cat D)
  equiv e = record
    { functor = map (S.Equiv.functor e)
    ; isEquiv = preservesEquiv (S.Equiv.isEquiv e) }

  -- The primitive terminal equivalence agrees with the canonical terminal map.
  canonicalTerminal : T.IsEquiv (T.terminate (cat S.One))
  canonicalTerminal = T.equiv-transport
    (T.terminal-iso (T.Equiv.functor terminal) (T.terminate (cat S.One)))
    (T.Equiv.isEquiv terminal)

compose : {l : Level} {R S T : Theory l l l}
  → Weakening S T → Weakening R S → Weakening R T
compose {R = R} {S} {T} V W = record
  { assignment = record
      { cat = λ C → V.cat (W.cat C)
      ; map = λ f → V.map (W.map f)
      ; anima = λ x → V.anima (W.anima x)
      ; terminal = join (VR.equiv W.terminal) V.terminal
      ; path = λ f g → join (VR.equiv (W.path f g)) (V.path (W.map f) (W.map g)) }
  ; unit = λ C → T._∙_ (V.unit (W.cat C)) (V.term (W.unit C))
  ; comp = λ f g → T._∙_ (V.comp (W.map f) (W.map g)) (V.term (W.comp f g)) }
  where
  module T = View T
  module V = Weakening V
  module W = Weakening W
  module VR = Results V
  join : {C D E : T.CAT} → T.Equiv C D → T.Equiv D E → T.Equiv C E
  join e d = record
    { functor = T._∘_ (T.Equiv.functor d) (T.Equiv.functor e)
    ; isEquiv = T.equiv-compose (T.Equiv.functor e) (T.Equiv.functor d)
        (T.Equiv.isEquiv e) (T.Equiv.isEquiv d) }

identity : {l : Level} (T : Theory l l l) → Weakening T T
identity T = record
  { assignment = record
      { cat = λ C → C ; map = λ f → f ; anima = λ x → x
      ; terminal = ident T.One ; path = λ f g → ident (T._＝_ f g) }
  ; unit = λ C → T.idIso (T.id C)
  ; comp = λ f g → T.idIso (T._∘_ g f) }
  where
  module T = View T
  ident : (C : T.CAT) → T.Equiv C C
  ident C = record { functor = T.id C ; isEquiv = T.id-isEquiv C }
```
