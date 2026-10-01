# Comparisons of the basic operations

The boundary expressions specify how identity, composition, inversion, and whiskering compare after a weak change. Operation compatibility retains their chosen comparisons, with the required product and endpoint adjustments.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Coherence where

open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as Product

module Boundaries {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

  conjugate : {C D : T.CAT} {f f' g g' : T.MAP C D}
    → T._=₁_ f f' → T._=₁_ g g' → T.MAP (T._＝_ f g) (T._＝_ f' g')
  conjugate {f = f} {g = g} p q =
    T.const q ∙ (T.id (T._＝_ f g) ∙ T.const (p ⁻¹))

  post-source : {C D E : S.CAT} (f g : S.MAP C D) (u : S.MAP D E)
    → T.MAP (cat (S._＝_ f g)) (T._＝_ (map u ∘ map f) (map u ∘ map g))
  post-source f g u = conjugate (comp f u) (comp g u) ∘
    (phi (S._∘_ u f) (S._∘_ u g) ∘ map (S.postWhisker u))

  post-target : {C D E : S.CAT} (f g : S.MAP C D) (u : S.MAP D E)
    → T.MAP (cat (S._＝_ f g)) (T._＝_ (map u ∘ map f) (map u ∘ map g))
  post-target f g u = T.postWhisker (map u) ∘ phi f g

  pre-source : {B C D : S.CAT} (f g : S.MAP C D) (k : S.MAP B C)
    → T.MAP (cat (S._＝_ f g)) (T._＝_ (map f ∘ map k) (map g ∘ map k))
  pre-source f g k = conjugate (comp k f) (comp k g) ∘
    (phi (S._∘_ f k) (S._∘_ g k) ∘ map (S.preWhisker k))

  pre-target : {B C D : S.CAT} (f g : S.MAP C D) (k : S.MAP B C)
    → T.MAP (cat (S._＝_ f g)) (T._＝_ (map f ∘ map k) (map g ∘ map k))
  pre-target f g k = T.preWhisker (map k) ∘ phi f g

  vertical-source : {C D : S.CAT} (f g h : S.MAP C D)
    → T.MAP (cat (S._×_ (S._＝_ g h) (S._＝_ f g))) (T._＝_ (map f) (map h))
  vertical-source f g h = phi f h ∘ map S.isoComp

  vertical-target : {C D : S.CAT} (f g h : S.MAP C D)
    → T.MAP (cat (S._×_ (S._＝_ g h) (S._＝_ f g))) (T._＝_ (map f) (map h))
  vertical-target f g h = T.isoComp ∘
    T.pair (phi g h ∘ map S.pr₁) (phi f g ∘ map S.pr₂)

  assoc-source : {B C D E : S.CAT} (f : S.MAP B C) (g : S.MAP C D) (h : S.MAP D E)
    → T._=₁_ (map (S._∘_ (S._∘_ h g) f)) (map h ∘ (map g ∘ map f))
  assoc-source f g h = (map h ◁ comp f g) ∙
    (comp (S._∘_ g f) h ∙ term (S.comp-assoc f g h))

  assoc-target : {B C D E : S.CAT} (f : S.MAP B C) (g : S.MAP C D) (h : S.MAP D E)
    → T._=₁_ (map (S._∘_ (S._∘_ h g) f)) (map h ∘ (map g ∘ map f))
  assoc-target f g h = T.comp-assoc (map f) (map g) (map h) ∙
    ((comp g h ▷ map f) ∙ comp f (S._∘_ h g))

record OperationCompatibility {l : Level} {S T : Theory l l l}
  (W : Weakening S T) : Set l where
  private
    module S = View S
    module T = View T
  open Weakening W
  open Boundaries W
  field
    products : Product.PreservesProducts W
    post : {C D E : S.CAT} (f g : S.MAP C D) (u : S.MAP D E)
      → T._=₁_ (post-source f g u) (post-target f g u)
    pre : {B C D : S.CAT} (f g : S.MAP C D) (k : S.MAP B C)
      → T._=₁_ (pre-source f g k) (pre-target f g k)
    inversion : {C D : S.CAT} (f g : S.MAP C D)
      → T._=₁_ (T._∘_ (phi g f) (map S.＝-inv)) (T._∘_ T.＝-inv (phi f g))
    identityIso : {C D : S.CAT} (f : S.MAP C D)
      → T._=₂_ (term (S.idIso f)) (T.idIso (map f))
    vertical : {C D : S.CAT} (f g h : S.MAP C D)
      → T._=₁_ (vertical-source f g h) (vertical-target f g h)
    associator : {B C D E : S.CAT} (f : S.MAP B C) (g : S.MAP C D) (h : S.MAP D E)
      → T._=₂_ (assoc-source f g h) (assoc-target f g h)
    leftUnit : {C D : S.CAT} (f : S.MAP C D)
      → T._=₂_ (term (S.comp-unitˡ f))
          (T._∙_ (T.comp-unitˡ (map f))
            (T._∙_ (T._▷_ (unit D) (map f)) (comp f (S.id D))))
    rightUnit : {C D : S.CAT} (f : S.MAP C D)
      → T._=₂_ (term (S.comp-unitʳ f))
          (T._∙_ (T.comp-unitʳ (map f))
            (T._∙_ (T._◁_ (map f) (unit C)) (comp (S.id C) f)))

-- Normalizing a transported derived proof requires boundary identifications.
-- This lemma derives the resulting witness; it does not assume that the
-- normalizing identifications exist for every expression.
module Normalization {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∙_; _⁻¹)

  normalize : {C D : S.CAT} {f g : S.MAP C D} {alpha beta : S._=₁_ f g}
    {alpha' beta' : T._=₁_ (map f) (map g)}
    → T._=₂_ (term alpha) alpha' → T._=₂_ (term beta) beta'
    → S._=₂_ alpha beta → T._=₂_ alpha' beta'
  normalize a b p = b ∙ (cell2 p ∙ (a ⁻¹))
```
