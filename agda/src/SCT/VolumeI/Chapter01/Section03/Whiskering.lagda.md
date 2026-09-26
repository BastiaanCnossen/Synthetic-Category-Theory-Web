# Whiskering by an equivalence

The proof concerns functors between whole isomorphism animae. It first proves
that multiplication by a fixed natural isomorphism is an equivalence, then
uses the two fixed-input interchange clauses and 2-out-of-6.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.Equivalences as Equivalences

module SCT.VolumeI.Chapter01.Section03.Whiskering
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.Constructions V T
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Parameterized V T P PL S VC
open Equivalences V T P PL S

leftMultiply : {C D : CAT} {f g h : MAP C D}
  → g =₁ h → MAP (f ＝ g) (f ＝ h)
leftMultiply β = const β ∙ id _

rightMultiply : {C D : CAT} {f g h : MAP C D}
  → f =₁ g → MAP (g ＝ h) (f ＝ h)
rightMultiply β = id _ ∙ const β

left-evaluate : {X C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : MAP X (f ＝ g))
  → (leftMultiply β ∘ α) =₁ (const β ∙ α)
left-evaluate β α = isoComp-evaluate (const β) (id _) α
  (const-pre β α) (comp-unitˡ α)

right-evaluate : {X C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) (α : MAP X (g ＝ h))
  → (rightMultiply β ∘ α) =₁ (α ∙ const β)
right-evaluate β α = isoComp-evaluate (id _) (const β) α
  (comp-unitˡ α) (const-pre β α)

leftMultiply-isEquiv : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) → IsEquiv (leftMultiply {f = f} β)
leftMultiply-isEquiv β = record
  { inverse = leftMultiply (β ⁻¹)
  ; sectionIso = (left-cancel β (id _) ∙ left-evaluate (β ⁻¹) (leftMultiply β)) ⁻¹
  ; retractionIso = (left-cancelʳ β (id _) ∙ left-evaluate β (leftMultiply (β ⁻¹))) ⁻¹ }

rightMultiply-isEquiv : {C D : CAT} {f g h : MAP C D}
  (β : f =₁ g) → IsEquiv (rightMultiply {h = h} β)
rightMultiply-isEquiv β = record
  { inverse = rightMultiply (β ⁻¹)
  ; sectionIso = (right-cancel β (id _) ∙ right-evaluate (β ⁻¹) (rightMultiply β)) ⁻¹
  ; retractionIso = (right-cancelʳ β (id _) ∙ right-evaluate β (rightMultiply (β ⁻¹))) ⁻¹ }
```

A commuting square with invertible endpoint changes transfers equivalence in
either direction. Its displayed boundary uses only familiar vertical pasting.

```agda
square-left : {X C D : CAT} {f g f′ g′ : MAP C D}
  (u : MAP X (f ＝ g)) (v : MAP X (f′ ＝ g′))
  (α : f =₁ f′) (β : g =₁ g′)
  → (const β ∙ u) =₁ (v ∙ const α) → IsEquiv v → IsEquiv u
square-left u v α β κ ev = equiv-cancel-left u (leftMultiply β)
  (leftMultiply-isEquiv β)
  (equiv-transport ((left-evaluate β u) ⁻¹ ∙ (κ ⁻¹ ∙ right-evaluate α v))
    (equiv-compose v (rightMultiply α) ev (rightMultiply-isEquiv α)))

square-right : {X C D : CAT} {f g f′ g′ : MAP C D}
  (u : MAP X (f ＝ g)) (v : MAP X (f′ ＝ g′))
  (α : f =₁ f′) (β : g =₁ g′)
  → (const β ∙ u) =₁ (v ∙ const α) → IsEquiv u → IsEquiv v
square-right u v α β κ eu = equiv-cancel-left v (rightMultiply α)
  (rightMultiply-isEquiv α)
  (equiv-transport ((right-evaluate α v) ⁻¹ ∙ (κ ∙ left-evaluate β u))
    (equiv-compose u (leftMultiply β) eu (leftMultiply-isEquiv β)))

post-id : {C D : CAT} (f g : MAP C D) → IsEquiv (postWhisker {f = f} {g} (id D))
post-id {D = D} f g = square-left (postWhisker (id D)) (id (f ＝ g))
  (comp-unitˡ f) (comp-unitˡ g)
  (postWhisker-id f g ∙ (isoComp-cong (idIso _) (comp-unitʳ (postWhisker (id D)))) ⁻¹)
  (id-isEquiv (f ＝ g))

pre-id : {C D : CAT} (f g : MAP C D) → IsEquiv (preWhisker {f = f} {g} (id C))
pre-id {C} f g = square-left (preWhisker (id C)) (id (f ＝ g))
  (comp-unitʳ f) (comp-unitʳ g)
  (preWhisker-id f g ∙ (isoComp-cong (idIso _) (comp-unitʳ (preWhisker (id C)))) ⁻¹)
  (id-isEquiv (f ＝ g))

post-change : {B C D : CAT} {F G : MAP C D}
  (τ : F =₁ G) (f g : MAP B C)
  → IsEquiv (postWhisker {f = f} {g} G) → IsEquiv (postWhisker {f = f} {g} F)
post-change {F = F} {G} τ f g = square-left (postWhisker F) (postWhisker G)
  (τ ▷ f) (τ ▷ g)
  (isoComp-cong (comp-unitʳ (postWhisker G)) (idIso _) ∙
   (interchange-fixedOuter F G f g τ ∙
    (isoComp-cong (idIso _) (comp-unitʳ (postWhisker F))) ⁻¹))

pre-change : {B C D : CAT} {h k : MAP B C}
  (σ : h =₁ k) (f g : MAP C D)
  → IsEquiv (preWhisker {f = f} {g} k) → IsEquiv (preWhisker {f = f} {g} h)
pre-change {h = h} {k} σ f g = square-left (preWhisker h) (preWhisker k)
  (f ◁ σ) (g ◁ σ)
  (isoComp-cong (comp-unitʳ (preWhisker k)) (idIso _) ∙
   ((interchange-fixedInner f g h k σ) ⁻¹ ∙
    (isoComp-cong (idIso _) (comp-unitʳ (preWhisker h))) ⁻¹))
```

The composition comparisons transfer equivalence between whiskering by a
composite and the composite of the two whiskering functors. They retain the
associators at both endpoints.

```agda
post-composite : {B C D E : CAT} (f g : MAP B C) (u : MAP C D) (v : MAP D E)
  → IsEquiv (postWhisker {f = f} {g} (v ∘ u))
  → IsEquiv (postWhisker v ∘ postWhisker {f = f} {g} u)
post-composite f g u v = square-right (postWhisker (v ∘ u))
  (postWhisker v ∘ postWhisker u) (comp-assoc f u v) (comp-assoc g u v)
  (isoComp-cong (postWhisker v ◁ comp-unitʳ (postWhisker u)) (idIso _) ∙
   (postWhisker-comp f g u v ∙
    (isoComp-cong (idIso _) (comp-unitʳ (postWhisker (v ∘ u)))) ⁻¹))

pre-composite : {A B C D : CAT} (f g : MAP C D) (k : MAP B C) (l : MAP A B)
  → IsEquiv (preWhisker {f = f} {g} (k ∘ l))
  → IsEquiv (preWhisker l ∘ preWhisker {f = f} {g} k)
pre-composite f g k l = square-left (preWhisker l ∘ preWhisker k)
  (preWhisker (k ∘ l)) (comp-assoc l k f) (comp-assoc l k g)
  (isoComp-cong (comp-unitʳ (preWhisker (k ∘ l))) (idIso _) ∙
   (preWhisker-comp f g k l ∙
    (isoComp-cong (idIso _) (preWhisker l ◁ comp-unitʳ (preWhisker k))) ⁻¹))

postWhisker-isEquiv : {B C D : CAT} (F : MAP C D) → IsEquiv F
  → (f g : MAP B C) → IsEquiv (postWhisker {f = f} {g} F)
postWhisker-isEquiv F e f g =
  let G = IsEquiv.inverse e
      first = post-composite f g F G
        (post-change ((IsEquiv.sectionIso e) ⁻¹) f g (post-id f g))
      second = post-composite (F ∘ f) (F ∘ g) G F
        (post-change ((IsEquiv.retractionIso e) ⁻¹) (F ∘ f) (F ∘ g)
          (post-id (F ∘ f) (F ∘ g)))
  in TwoOutOfSix.first (two-out-of-six (postWhisker F) (postWhisker G)
       (postWhisker F) first second)

preWhisker-isEquiv : {C D E : CAT} (F : MAP C D) → IsEquiv F
  → (f g : MAP D E) → IsEquiv (preWhisker {f = f} {g} F)
preWhisker-isEquiv F e f g =
  let G = IsEquiv.inverse e
      first = pre-composite f g F G
        (pre-change ((IsEquiv.retractionIso e) ⁻¹) f g (pre-id f g))
      second = pre-composite (f ∘ F) (g ∘ F) G F
        (pre-change ((IsEquiv.sectionIso e) ⁻¹) (f ∘ F) (g ∘ F)
          (pre-id (f ∘ F) (g ∘ F)))
  in TwoOutOfSix.first (two-out-of-six (preWhisker F) (preWhisker G)
       (preWhisker F) first second)
```

Lifting keeps the comparison with the prescribed image. Applying the same
construction to an isomorphism anima also lifts specified higher identifications.

```agda
lift-along : {X C D : CAT} {f : MAP C D} → IsEquiv f
  → (d : MAP X D) → FunctorLift f d
lift-along {f = f} e d = record
  { lift = IsEquiv.inverse e ∘ d
  ; comparison = comp-unitˡ d ∙
      (((IsEquiv.retractionIso e) ⁻¹ ▷ d) ∙
        (comp-assoc d (IsEquiv.inverse e) f) ⁻¹) }

postWhisker-lift : {B C D : CAT} (F : MAP C D) → IsEquiv F
  → {f g : MAP B C} → (α : (F ∘ f) =₁ (F ∘ g))
  → FunctorLift (postWhisker F) α
postWhisker-lift F e {f} {g} α = lift-along (postWhisker-isEquiv F e f g) α

preWhisker-lift : {C D E : CAT} (F : MAP C D) → IsEquiv F
  → {f g : MAP D E} → (α : (f ∘ F) =₁ (g ∘ F))
  → FunctorLift (preWhisker F) α
preWhisker-lift F e {f} {g} α = lift-along (preWhisker-isEquiv F e f g) α

postWhisker-Iso₂-lift : {B C D : CAT} (F : MAP C D) → IsEquiv F
  → {f g : MAP B C} (α β : f =₁ g)
  → (p : (F ◁ α) =₂ (F ◁ β))
  → FunctorLift (postWhisker (postWhisker F)) p
postWhisker-Iso₂-lift F e {f} {g} α β p =
  postWhisker-lift (postWhisker F) (postWhisker-isEquiv F e f g) p

preWhisker-Iso₂-lift : {C D E : CAT} (F : MAP C D) → IsEquiv F
  → {f g : MAP D E} (α β : f =₁ g)
  → (p : (α ▷ F) =₂ (β ▷ F))
  → FunctorLift (postWhisker (preWhisker F)) p
preWhisker-Iso₂-lift F e {f} {g} α β p =
  postWhisker-lift (preWhisker F) (preWhisker-isEquiv F e f g) p
```

