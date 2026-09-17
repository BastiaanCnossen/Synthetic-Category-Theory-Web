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
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.Products as ProductConstructions
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.ProductFunctorCoherence as ProductFunctorCoherence

module SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits
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

postWhisker-id-reflect : {X C : CAT} {f g : MAP X C} {α β : NatIso f g}
  → Iso₂ (id C ◁ α) (id C ◁ β) → Iso₂ α β
postWhisker-id-reflect {f = f} {g} {α} {β} p =
  cancel-right-reflect (comp-unitˡ f)
    (postWhisker-id-at β ∙
      (isoComp-cong (idIso (comp-unitˡ g)) p ∙ invIso (postWhisker-id-at α)))

left-unitor-comp : {X K C : CAT} (f : MAP X K) (g : MAP K C)
  → Iso₂ (comp-unitˡ (g ∘ f) ∙ comp-assoc f g (id C)) (comp-unitˡ g ▷ f)
left-unitor-comp {C = C} f g =
  let I = id C
      A = comp-assoc f g I
      B = comp-assoc (g ∘ f) I I
      C′ = comp-assoc f g (I ∘ I)
      D′ = comp-assoc f (I ∘ g) I
      E = comp-assoc g I I ▷ f
      tail = D′ ∙ E
      r = comp-unitʳ I
      left-normal = invIso (preWhisker-comp-at r g f) ∙
        (isoComp-cong (invIso (triangle-whiskered (g ∘ f) I)) (idIso C′) ∙
        (invIso (isoComp-assoc-at (I ◁ comp-unitˡ (g ∘ f)) B C′) ∙
        (isoComp-cong (idIso (I ◁ comp-unitˡ (g ∘ f)))
          (invIso (pentagon-whiskered f g I I)) ∙
        (isoComp-assoc-at (I ◁ comp-unitˡ (g ∘ f)) (I ◁ A) tail ∙
          isoComp-cong (postWhisker-isoComp-at I (comp-unitˡ (g ∘ f)) A) (idIso tail)))))
      right-normal = isoComp-cong (idIso A)
        ((preWhisker f ◁ invIso (triangle-whiskered g I)) ∙
          invIso (preWhisker-isoComp-at (I ◁ comp-unitˡ g) (comp-assoc g I I) f)) ∙
        (isoComp-assoc-at A ((I ◁ comp-unitˡ g) ▷ f) E ∙
        (isoComp-cong (invIso (whisker-mixed-at (comp-unitˡ g) f I)) (idIso E) ∙
          invIso (isoComp-assoc-at (I ◁ (comp-unitˡ g ▷ f)) D′ E)))
  in postWhisker-id-reflect
    (cancel-right-reflect tail (invIso right-normal ∙ left-normal))

pair-projections-triangle₁ : {C D : CAT}
  → Iso₂ (comp-unitʳ pr₁ ∙ (pr₁ ◁ pair-projections {C} {D})) (pair-β₁ pr₁ pr₂)
pair-projections-triangle₁ = cancel-inverse (comp-unitʳ pr₁) (pair-β₁ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₁))
    (pair-iso-β₁ (invIso (comp-unitʳ pr₁) ∙ pair-β₁ pr₁ pr₂)
      (invIso (comp-unitʳ pr₂) ∙ pair-β₂ pr₁ pr₂))

pair-projections-triangle₂ : {C D : CAT}
  → Iso₂ (comp-unitʳ pr₂ ∙ (pr₂ ◁ pair-projections {C} {D})) (pair-β₂ pr₁ pr₂)
pair-projections-triangle₂ = cancel-inverse (comp-unitʳ pr₂) (pair-β₂ pr₁ pr₂) ∙
  isoComp-cong (idIso (comp-unitʳ pr₂))
    (pair-iso-β₂ (invIso (comp-unitʳ pr₁) ∙ pair-β₁ pr₁ pr₂)
      (invIso (comp-unitʳ pr₂) ∙ pair-β₂ pr₁ pr₂))

productMap-id-triangle₁ : (C D : CAT)
  → Iso₂ (comp-unitʳ pr₁ ∙ (pr₁ ◁ productMap-id C D))
      (comp-unitˡ pr₁ ∙ pair-β₁ (id C ∘ pr₁) (id D ∘ pr₂))
productMap-id-triangle₁ C D =
  pair-cong-triangle₁ (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
  (isoComp-cong pair-projections-triangle₁
      (idIso (pr₁ ◁ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
    project-composite pr₁ pair-projections
      (pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₁))

productMap-id-triangle₂ : (C D : CAT)
  → Iso₂ (comp-unitʳ pr₂ ∙ (pr₂ ◁ productMap-id C D))
      (comp-unitˡ pr₂ ∙ pair-β₂ (id C ∘ pr₁) (id D ∘ pr₂))
productMap-id-triangle₂ C D =
  pair-cong-triangle₂ (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
  (isoComp-cong pair-projections-triangle₂
      (idIso (pr₂ ◁ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
    project-composite pr₂ pair-projections
      (pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₂))

coordinate-left-unit : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : NatIso (π ∘ h) (f ∘ ρ))
  → Iso₂ ((comp-unitˡ f ▷ ρ) ∙ coordinate-comparison ρ f π h b (id C))
      (b ∙ (comp-unitˡ π ▷ h))
coordinate-left-unit ρ f π h b =
  let A = comp-assoc ρ f (id _)
      B = comp-assoc h π (id _)
      first = cancel-right A (comp-unitˡ (f ∘ ρ)) ∙
        isoComp-cong (invIso (left-unitor-comp ρ f)) (idIso (invIso A))
  in isoComp-cong (idIso b) (left-unitor-comp h π) ∙
    (isoComp-assoc-at b (comp-unitˡ (π ∘ h)) B ∙
    (isoComp-cong (postWhisker-id-at b) (idIso B) ∙
    (invIso (isoComp-assoc-at (comp-unitˡ (f ∘ ρ)) (id _ ◁ b) B) ∙
    (isoComp-cong first (idIso ((id _ ◁ b) ∙ B)) ∙
      invIso (isoComp-assoc-at (comp-unitˡ f ▷ ρ) (invIso A) ((id _ ◁ b) ∙ B))))))

pair-pre-cong-triangle₁ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  {f′ : MAP R C} {g′ : MAP R D}
  (α : NatIso (f ∘ r) f′) (β : NatIso (g ∘ r) g′)
  → Iso₂ (pair-β₁ f′ g′ ∙ (pr₁ ◁ (pair-cong α β ∙ pair-pre f g r)))
      (α ∙ ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁)))
pair-pre-cong-triangle₁ f g r {f′} {g′} α β =
  isoComp-cong (idIso α) (pair-pre-triangle₁ f g r) ∙
  (isoComp-assoc-at α (pair-β₁ (f ∘ r) (g ∘ r)) (pr₁ ◁ pair-pre f g r) ∙
  (isoComp-cong (pair-cong-triangle₁ α β) (idIso (pr₁ ◁ pair-pre f g r)) ∙
    project-composite pr₁ (pair-cong α β) (pair-pre f g r) (pair-β₁ f′ g′)))

pair-pre-cong-triangle₂ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  {f′ : MAP R C} {g′ : MAP R D}
  (α : NatIso (f ∘ r) f′) (β : NatIso (g ∘ r) g′)
  → Iso₂ (pair-β₂ f′ g′ ∙ (pr₂ ◁ (pair-cong α β ∙ pair-pre f g r)))
      (β ∙ ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂)))
pair-pre-cong-triangle₂ f g r {f′} {g′} α β =
  isoComp-cong (idIso β) (pair-pre-triangle₂ f g r) ∙
  (isoComp-assoc-at β (pair-β₂ (f ∘ r) (g ∘ r)) (pr₂ ◁ pair-pre f g r) ∙
  (isoComp-cong (pair-cong-triangle₂ α β) (idIso (pr₂ ◁ pair-pre f g r)) ∙
    project-composite pr₂ (pair-cong α β) (pair-pre f g r) (pair-β₂ f′ g′)))

left-unit-projection : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h h′ : MAP R K)
  (J : MAP K K) (δ : NatIso J (id K))
  (b : NatIso (π ∘ h) (f ∘ ρ))
  (b′ : NatIso (π ∘ h′) ((id C ∘ f) ∘ ρ))
  (bJ : NatIso (π ∘ J) (id C ∘ π))
  (out : NatIso h′ h) (step : NatIso (J ∘ h) h′)
  → Iso₂ (comp-unitʳ π ∙ (π ◁ δ)) (comp-unitˡ π ∙ bJ)
  → Iso₂ (b ∙ (π ◁ out)) ((comp-unitˡ f ▷ ρ) ∙ b′)
  → Iso₂ (b′ ∙ (π ◁ step))
      (coordinate-comparison ρ f π h b (id C) ∙
        ((bJ ▷ h) ∙ invIso (comp-assoc h J π)))
  → Iso₂ (π ◁ (out ∙ step)) (π ◁ (comp-unitˡ h ∙ (δ ▷ h)))
left-unit-projection ρ f π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
  let transport = (bJ ▷ h) ∙ invIso (comp-assoc h J π)
      e = coordinate-comparison ρ f π h b (id _)
      left-normal = isoComp-assoc-at b (comp-unitˡ π ▷ h) transport ∙
        (isoComp-cong (coordinate-left-unit ρ f π h b) (idIso transport) ∙
        (invIso (isoComp-assoc-at (comp-unitˡ f ▷ ρ) e transport) ∙
        (isoComp-cong (idIso (comp-unitˡ f ▷ ρ)) step-triangle ∙
        (isoComp-assoc-at (comp-unitˡ f ▷ ρ) b′ (π ◁ step) ∙
        (isoComp-cong out-triangle (idIso (π ◁ step)) ∙
          project-composite π out step b)))))
      A = comp-assoc h (id _) π
      triangle-solved = invIso
        (cancel-right A (π ◁ comp-unitˡ h) ∙
          isoComp-cong (triangle-whiskered h π) (idIso (invIso A)))
      pre-square = pre-square-projection π δ (comp-unitˡ π) bJ (comp-unitʳ π) h unit-triangle
      right-normal = isoComp-cong (idIso b)
        (pre-square ∙ isoComp-cong triangle-solved (idIso (π ◁ (δ ▷ h)))) ∙
        (isoComp-assoc-at b (π ◁ comp-unitˡ h) (π ◁ (δ ▷ h)) ∙
          project-composite π (comp-unitˡ h) (δ ▷ h) b)
  in cancel-left-reflect b (invIso right-normal ∙ left-normal)

productMap-unitˡ : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → Iso₂
      (productMap-cong (comp-unitˡ f) (comp-unitˡ g) ∙
        productMap-comp f (id C′) g (id D′))
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
  (ρ : MAP R C) (f : MAP C D) (J : MAP R R) (δ : NatIso J (id R))
  (bJ : NatIso (ρ ∘ J) (id C ∘ ρ))
  → Iso₂ (comp-unitʳ ρ ∙ (ρ ◁ δ)) (comp-unitˡ ρ ∙ bJ)
  → Iso₂
      ((comp-unitʳ f ▷ ρ) ∙ coordinate-comparison ρ (id C) ρ J bJ f)
      (comp-unitʳ (f ∘ ρ) ∙ ((f ∘ ρ) ◁ δ))
coordinate-right-unit ρ f J δ bJ unit-triangle =
  let A = comp-assoc ρ (id _) f
      B = comp-assoc J ρ f
      C′ = comp-assoc (id _) ρ f
      q = (f ∘ ρ) ◁ δ
      first = cancel-right A (f ◁ comp-unitˡ ρ) ∙
        isoComp-cong (triangle-whiskered ρ f) (idIso (invIso A))
  in isoComp-cong (invIso (right-unitor-comp ρ f)) (idIso q) ∙
    (invIso (isoComp-assoc-at (f ◁ comp-unitʳ ρ) C′ q) ∙
    (isoComp-cong (idIso (f ◁ comp-unitʳ ρ)) (invIso (postWhisker-comp-at δ ρ f)) ∙
    (isoComp-assoc-at (f ◁ comp-unitʳ ρ) (f ◁ (ρ ◁ δ)) B ∙
    (isoComp-cong
      (postWhisker-isoComp-at f (comp-unitʳ ρ) (ρ ◁ δ) ∙
        ((postWhisker f ◁ invIso unit-triangle) ∙
          invIso (postWhisker-isoComp-at f (comp-unitˡ ρ) bJ))) (idIso B) ∙
    (invIso (isoComp-assoc-at (f ◁ comp-unitˡ ρ) (f ◁ bJ) B) ∙
    (isoComp-cong first (idIso ((f ◁ bJ) ∙ B)) ∙
      invIso (isoComp-assoc-at (comp-unitʳ f ▷ ρ) (invIso A) ((f ◁ bJ) ∙ B))))))))

right-unit-square-projection : {R K C : CAT}
  (π : MAP K C) (h : MAP R K) (F : MAP R C) (b : NatIso (π ∘ h) F)
  (J : MAP R R) (δ : NatIso J (id R))
  → Iso₂ (b ∙ (π ◁ (comp-unitʳ h ∙ (h ◁ δ))))
      (comp-unitʳ F ∙ ((F ◁ δ) ∙ ((b ▷ J) ∙ invIso (comp-assoc J h π))))
right-unit-square-projection π h F b J δ =
  let A = comp-assoc (id _) h π
      solved = invIso (cancel-right A (π ◁ comp-unitʳ h) ∙
        isoComp-cong (right-unitor-comp h π) (idIso (invIso A)))
      head = isoComp-assoc-at (comp-unitʳ F) (b ▷ id _) (invIso A) ∙
        (isoComp-cong (invIso (preWhisker-id-at b)) (idIso (invIso A)) ∙
        (invIso (isoComp-assoc-at b (comp-unitʳ (π ∘ h)) (invIso A)) ∙
          isoComp-cong (idIso b) solved))
  in isoComp-cong (idIso (comp-unitʳ F)) (substitution-square-projection π h F b δ) ∙
    (isoComp-assoc-at (comp-unitʳ F) ((b ▷ id _) ∙ invIso A) (π ◁ (h ◁ δ)) ∙
    (isoComp-cong head (idIso (π ◁ (h ◁ δ))) ∙
      project-composite π (comp-unitʳ h) (h ◁ δ) b))

right-unit-projection : {R X K C : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h h′ : MAP R K)
  (J : MAP R R) (δ : NatIso J (id R))
  (b : NatIso (π ∘ h) (f ∘ ρ))
  (b′ : NatIso (π ∘ h′) ((f ∘ id X) ∘ ρ))
  (bJ : NatIso (ρ ∘ J) (id X ∘ ρ))
  (out : NatIso h′ h) (step : NatIso (h ∘ J) h′)
  → Iso₂ (comp-unitʳ ρ ∙ (ρ ◁ δ)) (comp-unitˡ ρ ∙ bJ)
  → Iso₂ (b ∙ (π ◁ out)) ((comp-unitʳ f ▷ ρ) ∙ b′)
  → Iso₂ (b′ ∙ (π ◁ step))
      (coordinate-comparison ρ (id X) ρ J bJ f ∙
        ((b ▷ J) ∙ invIso (comp-assoc J h π)))
  → Iso₂ (π ◁ (out ∙ step)) (π ◁ (comp-unitʳ h ∙ (h ◁ δ)))
right-unit-projection ρ f π h h′ J δ b b′ bJ out step unit-triangle out-triangle step-triangle =
  let transport = (b ▷ J) ∙ invIso (comp-assoc J h π)
      e = coordinate-comparison ρ (id _) ρ J bJ f
      left-normal = isoComp-assoc-at (comp-unitʳ (f ∘ ρ)) ((f ∘ ρ) ◁ δ) transport ∙
        (isoComp-cong (coordinate-right-unit ρ f J δ bJ unit-triangle) (idIso transport) ∙
        (invIso (isoComp-assoc-at (comp-unitʳ f ▷ ρ) e transport) ∙
        (isoComp-cong (idIso (comp-unitʳ f ▷ ρ)) step-triangle ∙
        (isoComp-assoc-at (comp-unitʳ f ▷ ρ) b′ (π ◁ step) ∙
        (isoComp-cong out-triangle (idIso (π ◁ step)) ∙
          project-composite π out step b)))))
  in cancel-left-reflect b
    (invIso (right-unit-square-projection π h (f ∘ ρ) b J δ) ∙ left-normal)

productMap-unitʳ : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → Iso₂
      (productMap-cong (comp-unitʳ f) (comp-unitʳ g) ∙
        productMap-comp (id C) f (id D) g)
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
