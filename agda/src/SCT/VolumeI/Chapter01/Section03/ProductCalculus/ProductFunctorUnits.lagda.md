# Unit comparisons for product functors

This module proves the left and right unit laws for the already chosen
product functor comparisons. It first derives the remaining unit
compatibility of the external associator and records projection triangles
for the chosen product unit. The projection calculations then identify the
two pastings in each unit law.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductConstructions
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorCoherence as ProductFunctorCoherence

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits
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
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open ProductConstructions V T P PL S
open PairingCoherence V T P PL S VC W
open PairingNaturality V T P PL S VC W
  using (cancel-left-reflect; project-composite; pre-square-projection; cancel-right; move-square;
         substitution-square-projection)
open Structural V T P PL S W
open IteratedPairing V T P PL S VC W PT using (pentagon-whiskered)
open PairingUnits V T P PL S VC W PT
open ProductFunctorCoherence V T P PL S VC W
open Isomorphisms V T P PL S VC W using (cancel-inverse)

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

pair-projections-triangle₁ : {C D : CAT}
  → (comp-unitʳ pr₁ ∙ (pr₁ ◁ pair-projections {C} {D})) =₂ (pair-β₁ pr₁ pr₂)
pair-projections-triangle₁ = cancel-inverse (comp-unitʳ pr₁) (pair-β₁ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₁))
    (pair-iso-β₁ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
      ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

pair-projections-triangle₂ : {C D : CAT}
  → (comp-unitʳ pr₂ ∙ (pr₂ ◁ pair-projections {C} {D})) =₂ (pair-β₂ pr₁ pr₂)
pair-projections-triangle₂ = cancel-inverse (comp-unitʳ pr₂) (pair-β₂ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₂))
    (pair-iso-β₂ ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
      ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂))

productMap-id-triangle₁ : (C D : CAT)
  → (comp-unitʳ pr₁ ∙ (pr₁ ◁ productMap-id C D)) =₂
      (comp-unitˡ pr₁ ∙ pair-β₁ (id C ∘ pr₁) (id D ∘ pr₂))
productMap-id-triangle₁ C D =
  pair-cong-triangle₁ (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
  (isoComp-cong pair-projections-triangle₁
      (idIso (pr₁ ◁ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
    project-composite pr₁ pair-projections
      (pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₁))

productMap-id-triangle₂ : (C D : CAT)
  → (comp-unitʳ pr₂ ∙ (pr₂ ◁ productMap-id C D)) =₂
      (comp-unitˡ pr₂ ∙ pair-β₂ (id C ∘ pr₁) (id D ∘ pr₂))
productMap-id-triangle₂ C D =
  pair-cong-triangle₂ (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
  (isoComp-cong pair-projections-triangle₂
      (idIso (pr₂ ◁ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
    project-composite pr₂ pair-projections
      (pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₂))

coordinate-left-unit : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : (π ∘ h) =₁ (f ∘ ρ))
  → ((comp-unitˡ f ▷ ρ) ∙ coordinate-comparison ρ f π h b (id C)) =₂
      (b ∙ (comp-unitˡ π ▷ h))
coordinate-left-unit ρ f π h b =
  let A = comp-assoc ρ f (id _)
      B = comp-assoc h π (id _)
      first = cancel-right A (comp-unitˡ (f ∘ ρ)) ∙
        isoComp-cong ((left-unitor-comp ρ f) ⁻¹) (idIso (A ⁻¹))
  in isoComp-cong (idIso b) (left-unitor-comp h π) ∙
    (isoComp-assoc-at b (comp-unitˡ (π ∘ h)) B ∙
    (isoComp-cong (postWhisker-id-at b) (idIso B) ∙
    ((isoComp-assoc-at (comp-unitˡ (f ∘ ρ)) (id _ ◁ b) B) ⁻¹ ∙
    (isoComp-cong first (idIso ((id _ ◁ b) ∙ B)) ∙
      (isoComp-assoc-at (comp-unitˡ f ▷ ρ) (A ⁻¹) ((id _ ◁ b) ∙ B)) ⁻¹))))

pair-pre-cong-triangle₁ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  {f′ : MAP R C} {g′ : MAP R D}
  (α : (f ∘ r) =₁ f′) (β : (g ∘ r) =₁ g′)
  → (pair-β₁ f′ g′ ∙ (pr₁ ◁ (pair-cong α β ∙ pair-pre f g r))) =₂
      (α ∙ ((pair-β₁ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₁) ⁻¹))
pair-pre-cong-triangle₁ f g r {f′} {g′} α β =
  isoComp-cong (idIso α) (pair-pre-triangle₁ f g r) ∙
  (isoComp-assoc-at α (pair-β₁ (f ∘ r) (g ∘ r)) (pr₁ ◁ pair-pre f g r) ∙
  (isoComp-cong (pair-cong-triangle₁ α β) (idIso (pr₁ ◁ pair-pre f g r)) ∙
    project-composite pr₁ (pair-cong α β) (pair-pre f g r) (pair-β₁ f′ g′)))

pair-pre-cong-triangle₂ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  {f′ : MAP R C} {g′ : MAP R D}
  (α : (f ∘ r) =₁ f′) (β : (g ∘ r) =₁ g′)
  → (pair-β₂ f′ g′ ∙ (pr₂ ◁ (pair-cong α β ∙ pair-pre f g r))) =₂
      (β ∙ ((pair-β₂ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₂) ⁻¹))
pair-pre-cong-triangle₂ f g r {f′} {g′} α β =
  isoComp-cong (idIso β) (pair-pre-triangle₂ f g r) ∙
  (isoComp-assoc-at β (pair-β₂ (f ∘ r) (g ∘ r)) (pr₂ ◁ pair-pre f g r) ∙
  (isoComp-cong (pair-cong-triangle₂ α β) (idIso (pr₂ ◁ pair-pre f g r)) ∙
    project-composite pr₂ (pair-cong α β) (pair-pre f g r) (pair-β₂ f′ g′)))

left-unit-projection : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h h′ : MAP R K)
  (J : MAP K K) (δ : J =₁ (id K))
  (b : (π ∘ h) =₁ (f ∘ ρ))
  (b′ : (π ∘ h′) =₁ ((id C ∘ f) ∘ ρ))
  (bJ : (π ∘ J) =₁ (id C ∘ π))
  (out : h′ =₁ h) (step : (J ∘ h) =₁ h′)
  → (comp-unitʳ π ∙ (π ◁ δ)) =₂ (comp-unitˡ π ∙ bJ)
  → (b ∙ (π ◁ out)) =₂ ((comp-unitˡ f ▷ ρ) ∙ b′)
  → (b′ ∙ (π ◁ step)) =₂
      (coordinate-comparison ρ f π h b (id C) ∙
        ((bJ ▷ h) ∙ (comp-assoc h J π) ⁻¹))
  → (π ◁ (out ∙ step)) =₂ (π ◁ (comp-unitˡ h ∙ (δ ▷ h)))
left-unit-projection ρ f π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
  let transport = (bJ ▷ h) ∙ (comp-assoc h J π) ⁻¹
      e = coordinate-comparison ρ f π h b (id _)
      left-normal = isoComp-assoc-at b (comp-unitˡ π ▷ h) transport ∙
        (isoComp-cong (coordinate-left-unit ρ f π h b) (idIso transport) ∙
        ((isoComp-assoc-at (comp-unitˡ f ▷ ρ) e transport) ⁻¹ ∙
        (isoComp-cong (idIso (comp-unitˡ f ▷ ρ)) step-triangle ∙
        (isoComp-assoc-at (comp-unitˡ f ▷ ρ) b′ (π ◁ step) ∙
        (isoComp-cong out-triangle (idIso (π ◁ step)) ∙
          project-composite π out step b)))))
      A = comp-assoc h (id _) π
      triangle-solved =
        (cancel-right A (π ◁ comp-unitˡ h) ∙
          isoComp-cong (triangle-whiskered h π) (idIso (A ⁻¹))) ⁻¹
      pre-square = pre-square-projection π δ (comp-unitˡ π) bJ (comp-unitʳ π) h unit-triangle
      right-normal = isoComp-cong (idIso b)
        (pre-square ∙ isoComp-cong triangle-solved (idIso (π ◁ (δ ▷ h)))) ∙
        (isoComp-assoc-at b (π ◁ comp-unitˡ h) (π ◁ (δ ▷ h)) ∙
          project-composite π (comp-unitˡ h) (δ ▷ h) b)
  in cancel-left-reflect b (right-normal ⁻¹ ∙ left-normal)

productMap-unitˡ : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  →
      (productMap-cong (comp-unitˡ f) (comp-unitˡ g) ∙
        productMap-comp f (id C′) g (id D′)) =₂
      (comp-unitˡ (productMap f g) ∙ (productMap-id C′ D′ ▷ productMap f g))
productMap-unitˡ {C} {C′} {D} {D′} f g =
  let h = productMap f g
      h′ = productMap (id C′ ∘ f) (id D′ ∘ g)
      J = productMap (id C′) (id D′)
      δ = productMap-id C′ D′
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      b′ = pair-β₁ ((id C′ ∘ f) ∘ pr₁) ((id D′ ∘ g) ∘ pr₂)
      d′ = pair-β₂ ((id C′ ∘ f) ∘ pr₁) ((id D′ ∘ g) ∘ pr₂)
      bJ = pair-β₁ (id C′ ∘ pr₁) (id D′ ∘ pr₂)
      dJ = pair-β₂ (id C′ ∘ pr₁) (id D′ ∘ pr₂)
      out = productMap-cong (comp-unitˡ f) (comp-unitˡ g)
      step = productMap-comp f (id C′) g (id D′)
      e = coordinate-comparison pr₁ f pr₁ h b (id C′)
      k = coordinate-comparison pr₂ g pr₂ h d (id D′)
  in pair-iso-extensionality
    (left-unit-projection pr₁ f pr₁ h h′ J δ b b′ bJ out step
      (productMap-id-triangle₁ C′ D′)
      (pair-cong-triangle₁ (comp-unitˡ f ▷ pr₁) (comp-unitˡ g ▷ pr₂))
      (pair-pre-cong-triangle₁ (id C′ ∘ pr₁) (id D′ ∘ pr₂) h e k))
    (left-unit-projection pr₂ g pr₂ h h′ J δ d d′ dJ out step
      (productMap-id-triangle₂ C′ D′)
      (pair-cong-triangle₂ (comp-unitˡ f ▷ pr₁) (comp-unitˡ g ▷ pr₂))
      (pair-pre-cong-triangle₂ (id C′ ∘ pr₁) (id D′ ∘ pr₂) h e k))

coordinate-right-unit : {R C D : CAT}
  (ρ : MAP R C) (f : MAP C D) (J : MAP R R) (δ : J =₁ (id R))
  (bJ : (ρ ∘ J) =₁ (id C ∘ ρ))
  → (comp-unitʳ ρ ∙ (ρ ◁ δ)) =₂ (comp-unitˡ ρ ∙ bJ)
  →
      ((comp-unitʳ f ▷ ρ) ∙ coordinate-comparison ρ (id C) ρ J bJ f) =₂
      (comp-unitʳ (f ∘ ρ) ∙ ((f ∘ ρ) ◁ δ))
coordinate-right-unit ρ f J δ bJ unit-triangle =
  let A = comp-assoc ρ (id _) f
      B = comp-assoc J ρ f
      C′ = comp-assoc (id _) ρ f
      q = (f ∘ ρ) ◁ δ
      first = cancel-right A (f ◁ comp-unitˡ ρ) ∙
        isoComp-cong (triangle-whiskered ρ f) (idIso (A ⁻¹))
  in isoComp-cong ((right-unitor-comp ρ f) ⁻¹) (idIso q) ∙
    ((isoComp-assoc-at (f ◁ comp-unitʳ ρ) C′ q) ⁻¹ ∙
    (isoComp-cong (idIso (f ◁ comp-unitʳ ρ)) ((postWhisker-comp-at δ ρ f) ⁻¹) ∙
    (isoComp-assoc-at (f ◁ comp-unitʳ ρ) (f ◁ (ρ ◁ δ)) B ∙
    (isoComp-cong
      (postWhisker-isoComp-at f (comp-unitʳ ρ) (ρ ◁ δ) ∙
        ((postWhisker f ◁ unit-triangle ⁻¹) ∙
          (postWhisker-isoComp-at f (comp-unitˡ ρ) bJ) ⁻¹)) (idIso B) ∙
    ((isoComp-assoc-at (f ◁ comp-unitˡ ρ) (f ◁ bJ) B) ⁻¹ ∙
    (isoComp-cong first (idIso ((f ◁ bJ) ∙ B)) ∙
      (isoComp-assoc-at (comp-unitʳ f ▷ ρ) (A ⁻¹) ((f ◁ bJ) ∙ B)) ⁻¹))))))

right-unit-square-projection : {R K C : CAT}
  (π : MAP K C) (h : MAP R K) (F : MAP R C) (b : (π ∘ h) =₁ F)
  (J : MAP R R) (δ : J =₁ (id R))
  → (b ∙ (π ◁ (comp-unitʳ h ∙ (h ◁ δ)))) =₂
      (comp-unitʳ F ∙ ((F ◁ δ) ∙ ((b ▷ J) ∙ (comp-assoc J h π) ⁻¹)))
right-unit-square-projection π h F b J δ =
  let A = comp-assoc (id _) h π
      solved = (cancel-right A (π ◁ comp-unitʳ h) ∙
        isoComp-cong (right-unitor-comp h π) (idIso (A ⁻¹))) ⁻¹
      head = isoComp-assoc-at (comp-unitʳ F) (b ▷ id _) (A ⁻¹) ∙
        (isoComp-cong ((preWhisker-id-at b) ⁻¹) (idIso (A ⁻¹)) ∙
        ((isoComp-assoc-at b (comp-unitʳ (π ∘ h)) (A ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso b) solved))
  in isoComp-cong (idIso (comp-unitʳ F)) (substitution-square-projection π h F b δ) ∙
    (isoComp-assoc-at (comp-unitʳ F) ((b ▷ id _) ∙ A ⁻¹) (π ◁ (h ◁ δ)) ∙
    (isoComp-cong head (idIso (π ◁ (h ◁ δ))) ∙
      project-composite π (comp-unitʳ h) (h ◁ δ) b))

right-unit-projection : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h h′ : MAP R K)
  (J : MAP R R) (δ : J =₁ (id R))
  (b : (π ∘ h) =₁ (f ∘ ρ))
  (b′ : (π ∘ h′) =₁ ((f ∘ id X) ∘ ρ))
  (bJ : (ρ ∘ J) =₁ (id X ∘ ρ))
  (out : h′ =₁ h) (step : (h ∘ J) =₁ h′)
  → (comp-unitʳ ρ ∙ (ρ ◁ δ)) =₂ (comp-unitˡ ρ ∙ bJ)
  → (b ∙ (π ◁ out)) =₂ ((comp-unitʳ f ▷ ρ) ∙ b′)
  → (b′ ∙ (π ◁ step)) =₂
      (coordinate-comparison ρ (id X) ρ J bJ f ∙
        ((b ▷ J) ∙ (comp-assoc J h π) ⁻¹))
  → (π ◁ (out ∙ step)) =₂ (π ◁ (comp-unitʳ h ∙ (h ◁ δ)))
right-unit-projection ρ f π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
  let transport = (b ▷ J) ∙ (comp-assoc J h π) ⁻¹
      e = coordinate-comparison ρ (id _) ρ J bJ f
      left-normal = isoComp-assoc-at (comp-unitʳ (f ∘ ρ)) ((f ∘ ρ) ◁ δ) transport ∙
        (isoComp-cong (coordinate-right-unit ρ f J δ bJ unit-triangle) (idIso transport) ∙
        ((isoComp-assoc-at (comp-unitʳ f ▷ ρ) e transport) ⁻¹ ∙
        (isoComp-cong (idIso (comp-unitʳ f ▷ ρ)) step-triangle ∙
        (isoComp-assoc-at (comp-unitʳ f ▷ ρ) b′ (π ◁ step) ∙
        (isoComp-cong out-triangle (idIso (π ◁ step)) ∙
          project-composite π out step b)))))
  in cancel-left-reflect b
    ((right-unit-square-projection π h (f ∘ ρ) b J δ) ⁻¹ ∙ left-normal)

productMap-unitʳ : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  →
      (productMap-cong (comp-unitʳ f) (comp-unitʳ g) ∙
        productMap-comp (id C) f (id D) g) =₂
      (comp-unitʳ (productMap f g) ∙ (productMap f g ◁ productMap-id C D))
productMap-unitʳ {C} {C′} {D} {D′} f g =
  let h = productMap f g
      h′ = productMap (f ∘ id C) (g ∘ id D)
      J = productMap (id C) (id D)
      δ = productMap-id C D
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      b′ = pair-β₁ ((f ∘ id C) ∘ pr₁) ((g ∘ id D) ∘ pr₂)
      d′ = pair-β₂ ((f ∘ id C) ∘ pr₁) ((g ∘ id D) ∘ pr₂)
      bJ = pair-β₁ (id C ∘ pr₁) (id D ∘ pr₂)
      dJ = pair-β₂ (id C ∘ pr₁) (id D ∘ pr₂)
      out = productMap-cong (comp-unitʳ f) (comp-unitʳ g)
      step = productMap-comp (id C) f (id D) g
      e = coordinate-comparison pr₁ (id C) pr₁ J bJ f
      k = coordinate-comparison pr₂ (id D) pr₂ J dJ g
  in pair-iso-extensionality
    (right-unit-projection pr₁ f pr₁ h h′ J δ b b′ bJ out step
      (productMap-id-triangle₁ C D)
      (pair-cong-triangle₁ (comp-unitʳ f ▷ pr₁) (comp-unitʳ g ▷ pr₂))
      (pair-pre-cong-triangle₁ (f ∘ pr₁) (g ∘ pr₂) J e k))
    (right-unit-projection pr₂ g pr₂ h h′ J δ d d′ dJ out step
      (productMap-id-triangle₂ C D)
      (pair-cong-triangle₂ (comp-unitʳ f ▷ pr₁) (comp-unitʳ g ▷ pr₂))
      (pair-pre-cong-triangle₂ (f ∘ pr₁) (g ∘ pr₂) J e k))
```
