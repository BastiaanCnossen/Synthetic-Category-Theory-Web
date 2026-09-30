# Functor coherence

The whiskered pentagon and triangle control substitution by functors.
They also imply compatibility of the left and right unitors with composition.
These calculations apply before any pairing comparison is considered.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Coherence.PentagonTriangleCoherence PT
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingCoherence V T P PL S VC W
open WhiskeringEquivalences V T P PL S VC W using
  (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv;
   left-evaluate; right-evaluate)
open Isomorphisms V T P PL S VC W using (reassociateFour; cancel-inverse)

open Structural V T P PL S W
open Inverses V T P PL S VC using (cancel-left-reflect)

hcomp-idOuter : {C D E : CAT} {f f′ : MAP C D}
  (g : MAP D E) (α : f =₁ f′)
  → (idIso g ⋆ α) =₂ (g ◁ α)
hcomp-idOuter {f′ = f′} g α = isoComp-unitˡ-at (g ◁ α) ∙
  isoComp-cong (preWhisker-idIso g f′) (idIso (g ◁ α))

hcomp-idInner : {C D E : CAT} {g g′ : MAP D E}
  (β : g =₁ g′) (f : MAP C D)
  → (β ⋆ idIso f) =₂ (β ▷ f)
hcomp-idInner {g = g} β f = isoComp-unitʳ-at (β ▷ f) ∙
  isoComp-cong (idIso (β ▷ f)) (postWhisker-idIso g f)

pentagon-whiskered : {A B C D E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP C D) (k : MAP D E)
  → (comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h)) =₂
      ((k ◁ comp-assoc f g h) ∙
        (comp-assoc f (h ∘ g) k ∙ (comp-assoc g h k ▷ f)))
pentagon-whiskered f g h k =
  isoComp-assoc-at (k ◁ comp-assoc f g h)
    (comp-assoc f (h ∘ g) k) (comp-assoc g h k ▷ f)
  ∙ (isoComp-cong
      (isoComp-cong (hcomp-idOuter k (comp-assoc f g h)) (idIso _))
      (hcomp-idInner (comp-assoc g h k) f)
    ∙ comp-pentagon f g h k)

leftMultiply-at : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g)
  → (leftMultiply β ∘ α) =₂ (β ∙ α)
leftMultiply-at β α = isoComp-cong (const-One β) (idIso α) ∙ left-evaluate β α

rightMultiply-at : {C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) (α : g =₁ h)
  → (rightMultiply β ∘ α) =₂ (α ∙ β)
rightMultiply-at β α = isoComp-cong (idIso α) (const-One β) ∙ right-evaluate β α

cancel-left : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) {α α′ : f =₁ g}
  → (β ∙ α) =₂ (β ∙ α′) → α =₂ α′
cancel-left β {α} {α′} p = equiv-reflect (leftMultiply-isEquiv β)
  ((leftMultiply-at β α′) ⁻¹ ∙ (p ∙ leftMultiply-at β α))

cancel-right : {C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) {α α′ : g =₁ h}
  → (α ∙ β) =₂ (α′ ∙ β) → α =₂ α′
cancel-right β {α} {α′} p = equiv-reflect (rightMultiply-isEquiv β)
  ((rightMultiply-at β α′) ⁻¹ ∙ (p ∙ rightMultiply-at β α))

pre-assoc-at : {A B C D : CAT} {f g : MAP C D}
  (α : f =₁ g) (σ : MAP B C) (τ : MAP A B)
  → (comp-assoc τ σ g ∙ ((α ▷ σ) ▷ τ)) =₂
      ((α ▷ (σ ∘ τ)) ∙ comp-assoc τ σ f)
pre-assoc-at {f = f} {g} α σ τ =
  specialize (preWhisker-comp f g σ τ) α
    (isoComp-evaluate _ _ α
      (const-evaluate (comp-assoc τ σ g) α)
      (preWhisker-evaluate _ τ α
        (preWhisker-evaluate _ σ α (comp-unitˡ α))))
    (isoComp-evaluate _ _ α
      (preWhisker-evaluate _ (σ ∘ τ) α (comp-unitˡ α))
      (const-evaluate (comp-assoc τ σ f) α))

mixed-at : {A B C D : CAT} {f g : MAP B C}
  (u : MAP C D) (α : f =₁ g) (τ : MAP A B)
  → (comp-assoc τ g u ∙ ((u ◁ α) ▷ τ)) =₂
      ((u ◁ (α ▷ τ)) ∙ comp-assoc τ f u)
mixed-at {f = f} {g} u α τ =
  specialize (whisker-mixed f g τ u) α
    (isoComp-evaluate _ _ α
      (const-evaluate (comp-assoc τ g u) α)
      (preWhisker-evaluate _ τ α
        (postWhisker-evaluate u _ α (comp-unitˡ α))))
    (isoComp-evaluate _ _ α
      (postWhisker-evaluate u _ α
        (preWhisker-evaluate _ τ α (comp-unitˡ α)))
      (const-evaluate (comp-assoc τ f u) α))

pre-inverse-at : {A B C : CAT} {f g : MAP B C}
  (α : f =₁ g) (τ : MAP A B)
  → (α ⁻¹ ▷ τ) =₂ ((α ▷ τ) ⁻¹)
pre-inverse-at {f = f} α τ = cancel-right (α ▷ τ)
  ((isoComp-inverseˡ-at (α ▷ τ)) ⁻¹ ∙
    (preWhisker-idIso f τ ∙
      ((preWhisker τ ◁ isoComp-inverseˡ-at α) ∙
        (preWhisker-isoComp-at (α ⁻¹) α τ) ⁻¹)))

inverse-tail : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g)
  → ((β ∙ α) ∙ (α ⁻¹ ∙ β ⁻¹)) =₂ (idIso h)
inverse-tail β α = isoComp-inverseʳ-at β ∙
  (isoComp-cong (idIso β)
    (isoComp-unitˡ-at (β ⁻¹) ∙
      isoComp-cong (isoComp-inverseʳ-at α) (idIso (β ⁻¹))) ∙
    reassociateFour β α (α ⁻¹) (β ⁻¹))

solve-pentagon : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : x₁ =₁ x₄) (B : x₀ =₁ x₁)
  (C′ : x₃ =₁ x₄) (D′ : x₂ =₁ x₃) (E : x₀ =₁ x₂)
  → (A ∙ B) =₂ (C′ ∙ (D′ ∙ E))
  → (B ∙ (E ⁻¹ ∙ D′ ⁻¹)) =₂ (A ⁻¹ ∙ C′)
solve-pentagon A B C′ D′ E p =
  let tail = E ⁻¹ ∙ D′ ⁻¹
      cleared = isoComp-unitʳ-at C′ ∙
        (isoComp-cong (idIso C′) (inverse-tail D′ E) ∙
          (isoComp-assoc-at C′ (D′ ∙ E) tail ∙
            (isoComp-cong p (idIso tail) ∙ (isoComp-assoc-at A B tail) ⁻¹)))
  in cancel-left A ((cancel-inverse A C′) ⁻¹ ∙ cleared)

transport-pre : {R X K C : CAT} (u : MAP K C)
  (p : MAP X K) {f : MAP X C} (β : (u ∘ p) =₁ f)
  (σ : MAP R X) → (u ∘ (p ∘ σ)) =₁ (f ∘ σ)
transport-pre u p β σ = (β ▷ σ) ∙ (comp-assoc σ p u) ⁻¹

transport-pre-assoc : {Q R X K C : CAT}
  (u : MAP K C) (p : MAP X K) (f : MAP X C)
  (β : (u ∘ p) =₁ f) (σ : MAP R X) (τ : MAP Q R)
  →
      ((comp-assoc τ σ f ∙ (transport-pre u p β σ ▷ τ)) ∙
        (comp-assoc τ (p ∘ σ) u) ⁻¹) =₂
      (transport-pre u p β (σ ∘ τ) ∙ (u ◁ comp-assoc τ σ p))
transport-pre-assoc u p f β σ τ =
  let A = comp-assoc τ σ f
      B = (β ▷ σ) ▷ τ
      E = comp-assoc σ p u ▷ τ
      D′ = comp-assoc τ (p ∘ σ) u
      B′ = comp-assoc τ σ (u ∘ p)
      A′ = comp-assoc (σ ∘ τ) p u
      C′ = u ◁ comp-assoc τ σ p
      β′ = β ▷ (σ ∘ τ)
      tail = E ⁻¹ ∙ D′ ⁻¹
      expand = isoComp-cong
        ((isoComp-assoc-at A B (E ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso A)
            (isoComp-cong (idIso B) (pre-inverse-at (comp-assoc σ p u) τ) ∙
              preWhisker-isoComp-at (β ▷ σ) ((comp-assoc σ p u) ⁻¹) τ))
        (idIso (D′ ⁻¹))
      exchange = isoComp-cong
        (isoComp-cong (pre-assoc-at β σ τ) (idIso (E ⁻¹)))
        (idIso (D′ ⁻¹))
      regroup = isoComp-assoc-at β′ B′ tail ∙
        isoComp-assoc-at (β′ ∙ B′) (E ⁻¹) (D′ ⁻¹)
      pentagon = solve-pentagon A′ B′ C′ D′ E (pentagon-whiskered τ σ p u)
  in (isoComp-assoc-at β′ (A′ ⁻¹) C′) ⁻¹ ∙
    (isoComp-cong (idIso β′) pentagon ∙ (regroup ∙ (exchange ∙ expand)))

```

The triangle, together with the pentagon, determines how the unitors pass
through a composite. Reflection through whiskering by an identity then
removes the auxiliary identity functor.

```agda
open Inverses V T P PL S VC public using (cancel-right-reflect)

preWhisker-id-reflect : {X C : CAT} {f g : MAP X C} {α β : f =₁ g}
  → (α ▷ id X) =₂ (β ▷ id X) → α =₂ β
preWhisker-id-reflect {f = f} {g} {α} {β} p =
  cancel-right-reflect (comp-unitʳ f)
    (preWhisker-id-at β ∙
      (isoComp-cong (idIso (comp-unitʳ g)) p ∙ (preWhisker-id-at α) ⁻¹))

triangle-whiskered : {X C D : CAT} (f : MAP X C) (g : MAP C D)
  → (comp-unitʳ g ▷ f) =₂
      ((g ◁ comp-unitˡ f) ∙ comp-assoc f (id C) g)
triangle-whiskered f g =
  isoComp-cong (hcomp-idOuter g (comp-unitˡ f)) (idIso (comp-assoc f (id _) g)) ∙
    (comp-triangle f g ∙ (hcomp-idInner (comp-unitʳ g) f) ⁻¹)

right-unitor-comp : {X K C : CAT} (h : MAP X K) (π : MAP K C)
  → (comp-unitʳ (π ∘ h)) =₂
      ((π ◁ comp-unitʳ h) ∙ comp-assoc (id X) h π)
right-unitor-comp {X} h π =
  let I = id X
      A = comp-assoc I h π
      B = comp-assoc I I (π ∘ h)
      C′ = comp-assoc (I ∘ I) h π
      D′ = comp-assoc I (h ∘ I) π
      E = A ▷ I
      L = comp-unitˡ I
      q = (π ∘ h) ◁ L
      t = π ◁ (h ◁ L)
      s = π ◁ comp-assoc I I h
      u = comp-unitʳ (π ∘ h)
      v = (π ◁ comp-unitʳ h) ∙ A
      left-normal = isoComp-assoc-at t C′ B ∙
        (isoComp-cong (postWhisker-comp-at L h π) (idIso B) ∙
        ((isoComp-assoc-at A q B) ⁻¹ ∙
          isoComp-cong (idIso A) (triangle-whiskered I (π ∘ h))))
      triangle-h = postWhisker-isoComp-at π (h ◁ L) (comp-assoc I I h) ∙
        (postWhisker π ◁ triangle-whiskered I h)
      right-normal = isoComp-cong (idIso t) ((pentagon-whiskered I I h π) ⁻¹) ∙
        (isoComp-assoc-at t s (D′ ∙ E) ∙
        (isoComp-cong triangle-h (idIso (D′ ∙ E)) ∙
        (isoComp-assoc-at (π ◁ (comp-unitʳ h ▷ I)) D′ E ∙
        (isoComp-cong (whisker-mixed-at (comp-unitʳ h) I π) (idIso E) ∙
        ((isoComp-assoc-at A ((π ◁ comp-unitʳ h) ▷ I) E) ⁻¹ ∙
          isoComp-cong (idIso A) (preWhisker-isoComp-at (π ◁ comp-unitʳ h) A I))))))
  in preWhisker-id-reflect (cancel-left-reflect A (right-normal ⁻¹ ∙ left-normal))
postWhisker-id-reflect : {X C : CAT} {f g : MAP X C} {α β : f =₁ g}
  → (id C ◁ α) =₂ (id C ◁ β) → α =₂ β
postWhisker-id-reflect {f = f} {g} {α} {β} p =
  cancel-right-reflect (comp-unitˡ f)
    (postWhisker-id-at β ∙
      (isoComp-cong (idIso (comp-unitˡ g)) p ∙ (postWhisker-id-at α) ⁻¹))

left-unitor-comp : {X K C : CAT} (f : MAP X K) (g : MAP K C)
  → (comp-unitˡ (g ∘ f) ∙ comp-assoc f g (id C)) =₂ (comp-unitˡ g ▷ f)
left-unitor-comp {C = C} f g =
  let I = id C
      A = comp-assoc f g I
      B = comp-assoc (g ∘ f) I I
      C′ = comp-assoc f g (I ∘ I)
      D′ = comp-assoc f (I ∘ g) I
      E = comp-assoc g I I ▷ f
      tail = D′ ∙ E
      r = comp-unitʳ I
      left-normal = (preWhisker-comp-at r g f) ⁻¹ ∙
        (isoComp-cong ((triangle-whiskered (g ∘ f) I) ⁻¹) (idIso C′) ∙
        ((isoComp-assoc-at (I ◁ comp-unitˡ (g ∘ f)) B C′) ⁻¹ ∙
        (isoComp-cong (idIso (I ◁ comp-unitˡ (g ∘ f)))
          ((pentagon-whiskered f g I I) ⁻¹) ∙
        (isoComp-assoc-at (I ◁ comp-unitˡ (g ∘ f)) (I ◁ A) tail ∙
          isoComp-cong (postWhisker-isoComp-at I (comp-unitˡ (g ∘ f)) A) (idIso tail)))))
      right-normal = isoComp-cong (idIso A)
        ((preWhisker f ◁ (triangle-whiskered g I) ⁻¹) ∙
          (preWhisker-isoComp-at (I ◁ comp-unitˡ g) (comp-assoc g I I) f) ⁻¹) ∙
        (isoComp-assoc-at A ((I ◁ comp-unitˡ g) ▷ f) E ∙
        (isoComp-cong ((whisker-mixed-at (comp-unitˡ g) f I) ⁻¹) (idIso E) ∙
          (isoComp-assoc-at (I ◁ (comp-unitˡ g ▷ f)) D′ E) ⁻¹))
  in postWhisker-id-reflect
    (cancel-right-reflect tail (right-normal ⁻¹ ∙ left-normal))
```

The unitors agree at an identity. Consequently, an identification with the
identity satisfies the self-naturality square used to compare section frames.

```agda
abstract
  identity-unitors : (D : CAT) → comp-unitʳ (id D) =₂ comp-unitˡ (id D)
  identity-unitors D = postWhisker-id-reflect
    (cancel-right-reflect (comp-assoc i i i)
      (triangle-whiskered i i ∙
        ((cancel-left-reflect r (preWhisker-id-at r)) ⁻¹ ∙ (right-unitor-comp i i) ⁻¹)))
    where
    i : MAP D D
    i = id D
    r : (i ∘ i) =₁ i
    r = comp-unitʳ i

  self-naturality : {D : CAT} {t : MAP D D} (ρ : t =₁ id D) →
    (comp-unitʳ t ∙ (t ◁ ρ)) =₂ (comp-unitˡ t ∙ (ρ ▷ t))
  self-naturality {D} {t} ρ = cancel-left-reflect ρ
    (isoComp-assoc-at ρ (comp-unitˡ t) (ρ ▷ t) ∙
      (isoComp-cong (postWhisker-id-at ρ) (idIso (ρ ▷ t)) ∙
      (isoComp-cong (isoComp-cong (identity-unitors D) (idIso (id D ◁ ρ))) (idIso (ρ ▷ t)) ∙
      ((isoComp-assoc-at (comp-unitʳ (id D)) (id D ◁ ρ) (ρ ▷ t)) ⁻¹ ∙
      (isoComp-cong (idIso (comp-unitʳ (id D))) (interchange-at ρ ρ) ∙
      (isoComp-assoc-at (comp-unitʳ (id D)) (ρ ▷ id D) (t ◁ ρ) ∙
      (isoComp-cong ((preWhisker-id-at ρ) ⁻¹) (idIso (t ◁ ρ)) ∙
        (isoComp-assoc-at ρ (comp-unitʳ t) (t ◁ ρ)) ⁻¹)))))))

```
