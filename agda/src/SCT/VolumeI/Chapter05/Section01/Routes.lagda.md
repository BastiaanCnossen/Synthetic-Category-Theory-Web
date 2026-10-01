# Comparing two changes of context

A route comparison supplies equivalences on categories and naturality on functors. The identification-anima comparison is recorded at the next layer. These records do not yet include all higher comparisons for the full theory.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Routes where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core

-- First two layers only. Not an equivalence/comparison of full Theory morphisms.
record Comparison {l : Level} {S T : Theory l l l}
  (W V : Weakening S T) : Set l where
  private
    module S = View S
    module T = View T
    module W = Weakening W
    module V = Weakening V
  field
    component : (C : S.CAT) → T.Equiv (W.cat C) (V.cat C)
    naturality : {C D : S.CAT} (f : S.MAP C D)
      → T._=₁_ (T._∘_ (T.Equiv.functor (component D)) (W.map f))
                (T._∘_ (V.map f) (T.Equiv.functor (component C)))

module PathBoundary {l : Level} {S T : Theory l l l} {W V : Weakening S T}
  (e : Comparison W V) where
  private
    module S = View S
    module T = View T
    module W = Weakening W
    module V = Weakening V
  open T using (_∘_; _∙_)
  c : (C : S.CAT) → T.MAP (W.cat C) (V.cat C)
  c C = T.Equiv.functor (Comparison.component e C)

  left : {C D : S.CAT} (f g : S.MAP C D)
    → T.MAP (W.cat (S._＝_ f g)) (T._＝_ (c D ∘ W.map f) (V.map g ∘ c C))
  left {D = D} f g = T.const (Comparison.naturality e g) ∙
    (T.postWhisker (c D) ∘ W.phi f g)

  right : {C D : S.CAT} (f g : S.MAP C D)
    → T.MAP (W.cat (S._＝_ f g)) (T._＝_ (c D ∘ W.map f) (V.map g ∘ c C))
  right {C = C} f g = (T.preWhisker (c C) ∘ (V.phi f g ∘ c (S._＝_ f g))) ∙
    T.const (Comparison.naturality e f)

record PathCompatibility {l : Level} {S T : Theory l l l} {W V : Weakening S T}
  (e : Comparison W V) : Set l where
  private
    module S = View S
    module T = View T
  field
    square : {C D : S.CAT} (f g : S.MAP C D)
      → T._=₁_ (PathBoundary.left e f g) (PathBoundary.right e f g)

-- The next obligation when promoting an objectwise associator to a coherent
-- comparison of route comparisons. Neither componentwise associators nor
-- their pentagon automatically provide this field.
record Modification {l : Level} {S T : Theory l l l} {W V : Weakening S T}
  (e d : Comparison W V) : Set l where
  private
    module S = View S
    module T = View T
    module W = Weakening W
    module V = Weakening V
  field
    component : (C : S.CAT)
      → T._=₁_ (T.Equiv.functor (Comparison.component e C))
                (T.Equiv.functor (Comparison.component d C))
    naturality : {C D : S.CAT} (f : S.MAP C D)
      → T._=₂_ (T._∙_ (T._◁_ (V.map f) (component C)) (Comparison.naturality e f))
                (T._∙_ (Comparison.naturality d f) (T._▷_ (component D) (W.map f)))

composeComparison : {l : Level} {S T : Theory l l l} {W V U : Weakening S T}
  → Comparison V U → Comparison W V → Comparison W U
composeComparison {S = S} {T} {W} {V} {U} d e = record
  { component = λ C → record
      { functor = T._∘_ (dc C) (ec C)
      ; isEquiv = T.equiv-compose (ec C) (dc C)
          (T.Equiv.isEquiv (E.component C)) (T.Equiv.isEquiv (D.component C)) }
  ; naturality = λ {C} {F} f →
      T._∙_ (T.comp-assoc (ec C) (dc C) (U.map f))
      (T._∙_ (T._▷_ (D.naturality f) (ec C))
      (T._∙_ (T._⁻¹ (T.comp-assoc (ec C) (V.map f) (dc F)))
      (T._∙_ (T._◁_ (dc F) (E.naturality f))
               (T.comp-assoc (W.map f) (ec F) (dc F))))) }
  where
  module S = View S
  module T = View T
  module W = Weakening W
  module V = Weakening V
  module U = Weakening U
  module E = Comparison e
  module D = Comparison d
  ec : (C : S.CAT) → T.MAP (W.cat C) (V.cat C)
  ec C = T.Equiv.functor (E.component C)
  dc : (C : S.CAT) → T.MAP (V.cat C) (U.cat C)
  dc C = T.Equiv.functor (D.component C)

-- The object-component associator/pentagon are available. They do not prove
-- coherence of the naturality or PathCompatibility witnesses above.
module ObjectRoutes {l : Level} {S T : Theory l l l}
  {U V W X Y : Weakening S T}
  (a : Comparison U V) (b : Comparison V W) (c : Comparison W X) (d : Comparison X Y) where
  private
    module S = View S
    module T = View T
  f = λ C → T.Equiv.functor (Comparison.component a C)
  g = λ C → T.Equiv.functor (Comparison.component b C)
  h = λ C → T.Equiv.functor (Comparison.component c C)
  k = λ C → T.Equiv.functor (Comparison.component d C)

  associator : (C : S.CAT) → T._=₁_ (T._∘_ (T._∘_ (h C) (g C)) (f C))
                                          (T._∘_ (h C) (T._∘_ (g C) (f C)))
  associator C = T.comp-assoc (f C) (g C) (h C)

  pentagon : (C : S.CAT)
    → let short = T._∙_ (T.comp-assoc (T._∘_ (g C) (f C)) (h C) (k C))
                         (T.comp-assoc (f C) (g C) (T._∘_ (k C) (h C)))
          long = T._∙_ (T._∙_ (T._⋆_ (T.idIso (k C)) (T.comp-assoc (f C) (g C) (h C)))
                                 (T.comp-assoc (f C) (T._∘_ (h C) (g C)) (k C)))
                          (T._⋆_ (T.comp-assoc (g C) (h C) (k C)) (T.idIso (f C)))
      in T._=₂_ short long
  pentagon C = T.comp-pentagon (f C) (g C) (h C) (k C)
```
