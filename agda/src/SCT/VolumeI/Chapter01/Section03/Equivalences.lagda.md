# Equivalences of categories

This follows Section 1.3 through the 2-out-of-6 lemma. Inverse comparisons are
data, and every reassociation below is an explicit natural isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section03.Equivalences
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S

record FunctorLift {C D X : CAT} (f : MAP C D) (d : MAP X D) : Set m where
  field
    lift : MAP X C
    comparison : (f ∘ lift) =₁ d

record NaiveBijection {C D : CAT} (f : MAP C D) : Set (c ⊔ m) where
  field
    reflect : {X : CAT} (u v : MAP X C) → (f ∘ u) =₁ (f ∘ v) → u =₁ v
    lift : {X : CAT} (d : MAP X D) → FunctorLift f d

naive-bijection-isEquiv : {C D : CAT} {f : MAP C D}
  → NaiveBijection f → IsEquiv f
naive-bijection-isEquiv {C} {D} {f} b =
  --! begin naive-bijection-inverse-data
  let chosen = NaiveBijection.lift b (id D)
      g = FunctorLift.lift chosen
      ε = FunctorLift.comparison chosen
  --! end naive-bijection-inverse-data
      --! begin naive-bijection-reflection
      η = NaiveBijection.reflect b (g ∘ f) (id C)
        ((comp-unitʳ f) ⁻¹ ∙ (comp-unitˡ f ∙ ((ε ▷ f) ∙ (comp-assoc f g f) ⁻¹)))
      --! end naive-bijection-reflection
  in record { inverse = g ; sectionIso = η ⁻¹ ; retractionIso = ε ⁻¹ }

equiv-reflect : {C D X : CAT} {f : MAP C D} (e : IsEquiv f)
  (u v : MAP X C) → (f ∘ u) =₁ (f ∘ v) → u =₁ v
equiv-reflect {f = f} e u v α =
  let g = IsEquiv.inverse e
      comparison : (w : MAP _ _) → w =₁ (g ∘ (f ∘ w))
      comparison w = comp-assoc w f g ∙ ((IsEquiv.sectionIso e ▷ w) ∙ (comp-unitˡ w) ⁻¹)
  in (comparison v) ⁻¹ ∙ ((g ◁ α) ∙ comparison u)

equiv-lift : {C D X : CAT} {f : MAP C D} (e : IsEquiv f)
  (d : MAP X D) → FunctorLift f d
equiv-lift {f = f} e d = record
  { lift = IsEquiv.inverse e ∘ d
  ; comparison = comp-unitˡ d ∙
      (((IsEquiv.retractionIso e) ⁻¹ ▷ d) ∙ (comp-assoc d (IsEquiv.inverse e) f) ⁻¹) }

equiv-naive-bijection : {C D : CAT} {f : MAP C D}
  → IsEquiv f → NaiveBijection f
equiv-naive-bijection e = record { reflect = equiv-reflect e ; lift = equiv-lift e }

```

The next constructions concern sections, retractions, and inverse uniqueness.

```agda
record Section {C D : CAT} (f : MAP C D) : Set m where
  field
    section : MAP D C
    comparison : (f ∘ section) =₁ (id D)

record Retraction {C D : CAT} (f : MAP C D) : Set m where
  field
    retraction : MAP D C
    comparison : (id C) =₁ (retraction ∘ f)

equiv-section : {C D : CAT} {f : MAP C D} → IsEquiv f → Section f
equiv-section e = record
  { section = IsEquiv.inverse e
  ; comparison = (IsEquiv.retractionIso e) ⁻¹ }

equiv-retraction : {C D : CAT} {f : MAP C D} → IsEquiv f → Retraction f
equiv-retraction e = record
  { retraction = IsEquiv.inverse e
  ; comparison = IsEquiv.sectionIso e }

section-retraction-iso : {C D : CAT} {f : MAP C D}
  (s : Section f) (r : Retraction f)
  → (Section.section s) =₁ (Retraction.retraction r)
section-retraction-iso {f = f} s r =
  let u = Section.section s
      v = Retraction.retraction r
  in comp-unitʳ v ∙ ((v ◁ Section.comparison s) ∙
     (comp-assoc u f v ∙ ((Retraction.comparison r ▷ u) ∙ (comp-unitˡ u) ⁻¹)))

section-retraction-isEquiv : {C D : CAT} {f : MAP C D}
  → Section f → Retraction f → IsEquiv f
section-retraction-isEquiv {f = f} s r = record
  { inverse = Section.section s
  ; sectionIso = ((section-retraction-iso s r) ⁻¹ ▷ f) ∙ Retraction.comparison r
  ; retractionIso = (Section.comparison s) ⁻¹ }

inverse-unique : {C D : CAT} {f : MAP C D} (e e′ : IsEquiv f)
  → (IsEquiv.inverse e) =₁ (IsEquiv.inverse e′)
inverse-unique e e′ = section-retraction-iso (equiv-section e) (equiv-retraction e′)

id-isEquiv : (C : CAT) → IsEquiv (id C)
id-isEquiv C = record
  { inverse = id C
  ; sectionIso = (comp-unitˡ (id C)) ⁻¹
  ; retractionIso = (comp-unitˡ (id C)) ⁻¹ }

equiv-inverse : {C D : CAT} {f : MAP C D} (e : IsEquiv f)
  → IsEquiv (IsEquiv.inverse e)
equiv-inverse {f = f} e = record
  { inverse = f ; sectionIso = IsEquiv.retractionIso e ; retractionIso = IsEquiv.sectionIso e }

equiv-transport : {C D : CAT} {f g : MAP C D}
  → f =₁ g → IsEquiv f → IsEquiv g
equiv-transport α e = record
  { inverse = IsEquiv.inverse e
  ; sectionIso = (IsEquiv.inverse e ◁ α) ∙ IsEquiv.sectionIso e
  ; retractionIso = (α ▷ IsEquiv.inverse e) ∙ IsEquiv.retractionIso e }

equiv-compose : {C D E : CAT} (f : MAP C D) (g : MAP D E)
  → IsEquiv f → IsEquiv g → IsEquiv (g ∘ f)
equiv-compose {C} {D} {E} f g ef eg =
  let u : MAP D C
      u = IsEquiv.inverse ef
      v : MAP E D
      v = IsEquiv.inverse eg
      --! begin equiv-compose-left
      left : ((u ∘ v) ∘ (g ∘ f)) =₁ (id C)
      left = (IsEquiv.sectionIso ef) ⁻¹ ∙
        ((u ◁ comp-unitˡ f) ∙ ((u ◁ ((IsEquiv.sectionIso eg) ⁻¹ ▷ f)) ∙
        ((u ◁ (comp-assoc f g v) ⁻¹) ∙ comp-assoc (g ∘ f) v u)))
      --! end equiv-compose-left
      --! begin equiv-compose-right
      right : ((g ∘ f) ∘ (u ∘ v)) =₁ (id E)
      right = (IsEquiv.retractionIso eg) ⁻¹ ∙
        ((g ◁ comp-unitˡ v) ∙ ((g ◁ ((IsEquiv.retractionIso ef) ⁻¹ ▷ v)) ∙
        ((g ◁ (comp-assoc v u f) ⁻¹) ∙ comp-assoc (u ∘ v) f g)))
      --! end equiv-compose-right
  in record { inverse = u ∘ v ; sectionIso = left ⁻¹ ; retractionIso = right ⁻¹ }
```

The two cancellation directions of 2-out-of-3 use transport of equivalence
along the displayed comparison, rather than replacing functors by host equality.

```agda
equiv-cancel-right : {C D E : CAT} (f : MAP C D) (g : MAP D E)
  → IsEquiv f → IsEquiv (g ∘ f) → IsEquiv g
equiv-cancel-right f g ef egf =
  let u = IsEquiv.inverse ef
      comparison = comp-unitʳ g ∙ ((g ◁ (IsEquiv.retractionIso ef) ⁻¹) ∙ comp-assoc u f g)
  in equiv-transport comparison (equiv-compose u (g ∘ f) (equiv-inverse ef) egf)

equiv-cancel-left : {C D E : CAT} (f : MAP C D) (g : MAP D E)
  → IsEquiv g → IsEquiv (g ∘ f) → IsEquiv f
equiv-cancel-left f g eg egf =
  let v = IsEquiv.inverse eg
      comparison = comp-unitˡ f ∙ (((IsEquiv.sectionIso eg) ⁻¹ ▷ f) ∙ (comp-assoc f g v) ⁻¹)
  in equiv-transport comparison (equiv-compose (g ∘ f) v egf (equiv-inverse eg))

record TwoOutOfSix {C D E F : CAT}
  (f : MAP C D) (g : MAP D E) (h : MAP E F) : Set m where
  field
    first : IsEquiv f
    middle : IsEquiv g
    last : IsEquiv h
    composite : IsEquiv (h ∘ (g ∘ f))

two-out-of-six : {C D E F : CAT}
  (f : MAP C D) (g : MAP D E) (h : MAP E F)
  → IsEquiv (g ∘ f) → IsEquiv (h ∘ g) → TwoOutOfSix f g h
two-out-of-six f g h egf ehg =
  --! begin two-out-of-six-inverses
  let u = IsEquiv.inverse egf
      v = IsEquiv.inverse ehg
  --! end two-out-of-six-inverses
      --! begin two-out-of-six-section
      s = record { section = f ∘ u
                 ; comparison = (IsEquiv.retractionIso egf) ⁻¹ ∙ (comp-assoc u f g) ⁻¹ }
      --! end two-out-of-six-section
      --! begin two-out-of-six-retraction
      r = record { retraction = v ∘ h
                 ; comparison = (comp-assoc g h v) ⁻¹ ∙ IsEquiv.sectionIso ehg }
      --! end two-out-of-six-retraction
      --! begin two-out-of-six-middle
      eg = section-retraction-isEquiv s r
      --! end two-out-of-six-middle
      --! begin two-out-of-six-conclusion
      ef = equiv-cancel-left f g eg egf
      eh = equiv-cancel-right g h eg ehg
  in record { first = ef ; middle = eg ; last = eh
            ; composite = equiv-compose (g ∘ f) h egf eh }
      --! end two-out-of-six-conclusion
```
