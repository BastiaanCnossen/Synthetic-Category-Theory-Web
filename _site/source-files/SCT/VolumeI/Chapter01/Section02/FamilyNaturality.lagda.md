# Naturality with varying isomorphism inputs

The inputs have an arbitrary common parameter category `A`. These are natural
isomorphisms between actual boundary functors, so specializing to the input
product gives the jointly parameterized naturality squares. The proof orders
the two changes according to the definition of horizontal composition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.FamilyPairing as FamilyPairing

module SCT.VolumeI.Chapter01.Section02.FamilyNaturality
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Whiskering V T P PL S W using (interchange-fixedOuter; interchange-fixedInner)
open Parameterized V T P PL S VC
open Parameterized.WhiskeringLaws V T P PL S VC W
open PairingCoherence V T P PL S VC W using (pair-pre-triangle₁; pair-pre-triangle₂)
open FamilyPairing V T P PL S VC W

post-const : {A X C D : CAT} {f g : MAP X C}
  (u : MAP C D) (α : NatIso f g)
  → NatIso (u ◁ const {P = A} α) (const (u ◁ α))
post-const {A} u α = invIso (comp-assoc (terminate A) α (postWhisker u))

pre-const : {A R X C : CAT} {f g : MAP X C}
  (α : NatIso f g) (r : MAP R X)
  → NatIso (const {P = A} α ▷ r) (const (α ▷ r))
pre-const {A} α r = invIso (comp-assoc (terminate A) α (preWhisker r))

pre-composition : {A R X C : CAT} {f g h : MAP X C}
  (β : MAP A (g ≅ h)) (α : MAP A (f ≅ g)) (r : MAP R X)
  → NatIso ((β ∙ α) ▷ r) ((β ▷ r) ∙ (α ▷ r))
pre-composition {f = f} {g} {h} β α r =
  let input = pair β α
  in specialize (preWhisker-isoComp f g h r) input
    (preWhisker-evaluate (pr₁ ∙ pr₂) r input
      (isoComp-evaluate pr₁ pr₂ input (pair-β₁ β α) (pair-β₂ β α)))
    (isoComp-evaluate (pr₁ ▷ r) (pr₂ ▷ r) input
      (preWhisker-evaluate pr₁ r input (pair-β₁ β α))
      (preWhisker-evaluate pr₂ r input (pair-β₂ β α)))

family-cancel-left : {A X C : CAT} {f g h : MAP X C}
  (b : NatIso g h) {α β : MAP A (f ≅ g)}
  → NatIso (const b ∙ α) (const b ∙ β) → NatIso α β
family-cancel-left b {α} {β} p = left-cancel b β ∙
  (isoComp-cong (idIso (const (invIso b))) p ∙ invIso (left-cancel b α))

family-move-square : {A X C : CAT} {f g f′ g′ : MAP X C}
  (b : NatIso g g′) (u : MAP A (f ≅ g)) (v : MAP A (f′ ≅ g′)) (a : NatIso f f′)
  → NatIso (const b ∙ u) (v ∙ const a)
  → NatIso (const (invIso b) ∙ v) (u ∙ const (invIso a))
family-move-square b u v a p =
  let solved = isoComp-cong (idIso (const (invIso b))) p ∙ invIso (left-cancel b u)
      rearranged = invIso (assoc (const (invIso b)) v (const a)) ∙ solved
  in invIso (right-cancel a (const (invIso b) ∙ v) ∙
       isoComp-cong rearranged (idIso (const (invIso a))))

family-interchange-fixedOuter : {A B C D : CAT} {F G : MAP C D} {h k : MAP B C}
  (τ : NatIso F G) (σ : MAP A (h ≅ k))
  → NatIso (const (τ ▷ k) ∙ (F ◁ σ)) ((G ◁ σ) ∙ const (τ ▷ h))
family-interchange-fixedOuter {F = F} {G} {h} {k} τ σ =
  specialize (interchange-fixedOuter F G h k τ) σ
    (isoComp-evaluate _ _ σ (const-pre (τ ▷ k) σ)
      (postWhisker-evaluate F _ σ (comp-unitˡ σ)))
    (isoComp-evaluate _ _ σ
      (postWhisker-evaluate G _ σ (comp-unitˡ σ)) (const-pre (τ ▷ h) σ))

family-interchange-fixedInner : {A B C D : CAT} {F G : MAP C D} {h k : MAP B C}
  (τ : MAP A (F ≅ G)) (σ : NatIso h k)
  → NatIso ((τ ▷ k) ∙ const (F ◁ σ)) (const (G ◁ σ) ∙ (τ ▷ h))
family-interchange-fixedInner {F = F} {G} {h} {k} τ σ =
  specialize (interchange-fixedInner F G h k σ) τ
    (isoComp-evaluate _ _ τ
      (preWhisker-evaluate _ k τ (comp-unitˡ τ)) (const-pre (F ◁ σ) τ))
    (isoComp-evaluate _ _ τ (const-pre (G ◁ σ) τ)
      (preWhisker-evaluate _ h τ (comp-unitˡ τ)))

constant-triangle : {A X K C : CAT} {h h′ : MAP X K} {f : MAP X C}
  (π : MAP K C) (δ : NatIso h h′)
  (b : NatIso (π ∘ h′) f) (q : NatIso (π ∘ h) f)
  → Iso₂ (b ∙ (π ◁ δ)) q
  → NatIso (const {P = A} b ∙ (π ◁ const δ)) (const q)
constant-triangle π δ b q t = const-cong t ∙
  (const-comp b (π ◁ δ) ∙ isoComp-cong (idIso (const b)) (post-const π δ))

family-project-composite : {A X K C : CAT} {h₀ h₁ h₂ : MAP X K} {z : MAP X C}
  (π : MAP K C) (β : MAP A (h₁ ≅ h₂)) (α : MAP A (h₀ ≅ h₁))
  (b : NatIso (π ∘ h₂) z)
  → NatIso (const b ∙ (π ◁ (β ∙ α))) ((const b ∙ (π ◁ β)) ∙ (π ◁ α))
family-project-composite π β α b = invIso (assoc (const b) (π ◁ β) (π ◁ α)) ∙
  isoComp-cong (idIso (const b)) (post-composition π β α)

family-pre-square-projection : {A R X K C : CAT} (π : MAP K C)
  {h h′ : MAP X K} {f f′ : MAP X C}
  (δ : MAP A (h ≅ h′)) (α : MAP A (f ≅ f′))
  (b : NatIso (π ∘ h) f) (b′ : NatIso (π ∘ h′) f′)
  (r : MAP R X)
  → NatIso (const b′ ∙ (π ◁ δ)) (α ∙ const b)
  → NatIso
      (const ((b′ ▷ r) ∙ invIso (comp-assoc r h′ π)) ∙ (π ◁ (δ ▷ r)))
      ((α ▷ r) ∙ const ((b ▷ r) ∙ invIso (comp-assoc r h π)))
family-pre-square-projection π {h} {h′} δ α b b′ r square =
  let moved = family-move-square (comp-assoc r h′ π) ((π ◁ δ) ▷ r)
        (π ◁ (δ ▷ r)) (comp-assoc r h π) (whisker-mixed-general δ r π)
      pre-square = isoComp-cong (idIso (α ▷ r)) (pre-const b r) ∙
        (pre-composition α (const b) r ∙
          ((preWhisker r ◁ square) ∙
            (invIso (pre-composition (const b′) (π ◁ δ) r) ∙
              invIso (isoComp-cong (pre-const b′ r) (idIso ((π ◁ δ) ▷ r))))))
      expanded = assoc (α ▷ r) (const (b ▷ r)) (const (invIso (comp-assoc r h π))) ∙
        (isoComp-cong pre-square (idIso (const (invIso (comp-assoc r h π)))) ∙
          (invIso (assoc (const (b′ ▷ r)) ((π ◁ δ) ▷ r)
            (const (invIso (comp-assoc r h π)))) ∙
            (isoComp-cong (idIso (const (b′ ▷ r))) moved ∙
              assoc (const (b′ ▷ r)) (const (invIso (comp-assoc r h′ π)))
                (π ◁ (δ ▷ r)))))
  in isoComp-cong (idIso (α ▷ r)) (const-comp (b ▷ r) (invIso (comp-assoc r h π))) ∙
    (expanded ∙ isoComp-cong
      (invIso (const-comp (b′ ▷ r) (invIso (comp-assoc r h′ π))))
      (idIso (π ◁ (δ ▷ r))))

family-substitution-square-projection : {A R X K C : CAT} (π : MAP K C)
  (h : MAP X K) (f : MAP X C) (b : NatIso (π ∘ h) f)
  {r s : MAP R X} (γ : MAP A (r ≅ s))
  → NatIso
      (const ((b ▷ s) ∙ invIso (comp-assoc s h π)) ∙ (π ◁ (h ◁ γ)))
      ((f ◁ γ) ∙ const ((b ▷ r) ∙ invIso (comp-assoc r h π)))
family-substitution-square-projection π h f b {r} {s} γ =
  let moved = family-move-square (comp-assoc s h π) ((π ∘ h) ◁ γ)
        (π ◁ (h ◁ γ)) (comp-assoc r h π) (postWhisker-comp-general γ h π)
      expanded = assoc (f ◁ γ) (const (b ▷ r)) (const (invIso (comp-assoc r h π))) ∙
        (isoComp-cong (family-interchange-fixedOuter b γ)
          (idIso (const (invIso (comp-assoc r h π)))) ∙
          (invIso (assoc (const (b ▷ s)) ((π ∘ h) ◁ γ)
            (const (invIso (comp-assoc r h π)))) ∙
            (isoComp-cong (idIso (const (b ▷ s))) moved ∙
              assoc (const (b ▷ s)) (const (invIso (comp-assoc s h π))) (π ◁ (h ◁ γ)))))
  in isoComp-cong (idIso (f ◁ γ)) (const-comp (b ▷ r) (invIso (comp-assoc r h π))) ∙
    (expanded ∙ isoComp-cong (invIso (const-comp (b ▷ s) (invIso (comp-assoc s h π))))
      (idIso (π ◁ (h ◁ γ))))

family-projected-square : {A X K C : CAT}
  {h₀ h₁ h₂ h₃ : MAP X K} {z₁ z₃ : MAP X C}
  (π : MAP K C) (ρ : MAP A (h₁ ≅ h₃)) (τ : MAP A (h₀ ≅ h₁))
  (υ : MAP A (h₂ ≅ h₃)) (δ : MAP A (h₀ ≅ h₂))
  (b : NatIso (π ∘ h₁) z₁) (c : NatIso (π ∘ h₃) z₃)
  (α : MAP A (z₁ ≅ z₃))
  (q : MAP A ((π ∘ h₀) ≅ z₁)) (q′ : MAP A ((π ∘ h₂) ≅ z₃))
  → NatIso (const c ∙ (π ◁ ρ)) (α ∙ const b)
  → NatIso (const b ∙ (π ◁ τ)) q
  → NatIso (const c ∙ (π ◁ υ)) q′
  → NatIso (q′ ∙ (π ◁ δ)) (α ∙ q)
  → NatIso (π ◁ (ρ ∙ τ)) (π ◁ (υ ∙ δ))
family-projected-square π ρ τ υ δ b c α q q′ top left bottom square =
  let left-normal = isoComp-cong (idIso α) left ∙
        (assoc α (const b) (π ◁ τ) ∙
          (isoComp-cong top (idIso (π ◁ τ)) ∙ family-project-composite π ρ τ c))
      right-normal = square ∙
        (isoComp-cong bottom (idIso (π ◁ δ)) ∙ family-project-composite π υ δ c)
  in family-cancel-left c (invIso right-normal ∙ left-normal)

family-pair-pre-triangle₁ : {A R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → NatIso (const {P = A} (pair-β₁ (f ∘ r) (g ∘ r)) ∙ (pr₁ ◁ const (pair-pre f g r)))
      (const ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁)))
family-pair-pre-triangle₁ f g r = constant-triangle pr₁ (pair-pre f g r)
  (pair-β₁ (f ∘ r) (g ∘ r)) _ (pair-pre-triangle₁ f g r)

family-pair-pre-triangle₂ : {A R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → NatIso (const {P = A} (pair-β₂ (f ∘ r) (g ∘ r)) ∙ (pr₂ ◁ const (pair-pre f g r)))
      (const ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂)))
family-pair-pre-triangle₂ f g r = constant-triangle pr₂ (pair-pre f g r)
  (pair-β₂ (f ∘ r) (g ∘ r)) _ (pair-pre-triangle₂ f g r)

family-pair-pre-inputs : {A R X C D : CAT} {f f′ : MAP X C} {g g′ : MAP X D}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′)) (r : MAP R X)
  → NatIso (pairing (α ▷ r) (β ▷ r) ∙ const (pair-pre f g r))
      (const (pair-pre f′ g′ r) ∙ (pairing α β ▷ r))
family-pair-pre-inputs {f = f} {f′} {g} {g′} α β r =
  let input = pairing α β
      output = pairing (α ▷ r) (β ▷ r)
      before = const (pair-pre f g r)
      after = const (pair-pre f′ g′ r)
  in family-extensionality
    (family-projected-square pr₁ output before after (input ▷ r)
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f′ ∘ r) (g′ ∘ r)) (α ▷ r)
      (const ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁)))
      (const ((pair-β₁ f′ g′ ▷ r) ∙ invIso (comp-assoc r (pair f′ g′) pr₁)))
      (pairing-triangle₁ (α ▷ r) (β ▷ r))
      (family-pair-pre-triangle₁ f g r) (family-pair-pre-triangle₁ f′ g′ r)
      (family-pre-square-projection pr₁ input α (pair-β₁ f g) (pair-β₁ f′ g′) r
        (pairing-triangle₁ α β)))
    (family-projected-square pr₂ output before after (input ▷ r)
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f′ ∘ r) (g′ ∘ r)) (β ▷ r)
      (const ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂)))
      (const ((pair-β₂ f′ g′ ▷ r) ∙ invIso (comp-assoc r (pair f′ g′) pr₂)))
      (pairing-triangle₂ (α ▷ r) (β ▷ r))
      (family-pair-pre-triangle₂ f g r) (family-pair-pre-triangle₂ f′ g′ r)
      (family-pre-square-projection pr₂ input β (pair-β₂ f g) (pair-β₂ f′ g′) r
        (pairing-triangle₂ α β)))

family-pair-pre-substitution : {A R X C D : CAT}
  (f : MAP X C) (g : MAP X D) {r s : MAP R X} (γ : MAP A (r ≅ s))
  → NatIso (pairing (f ◁ γ) (g ◁ γ) ∙ const (pair-pre f g r))
      (const (pair-pre f g s) ∙ (pair f g ◁ γ))
family-pair-pre-substitution f g {r} {s} γ =
  let input = pair f g ◁ γ
      output = pairing (f ◁ γ) (g ◁ γ)
      before = const (pair-pre f g r)
      after = const (pair-pre f g s)
  in family-extensionality
    (family-projected-square pr₁ output before after input
      (pair-β₁ (f ∘ r) (g ∘ r)) (pair-β₁ (f ∘ s) (g ∘ s)) (f ◁ γ)
      (const ((pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁)))
      (const ((pair-β₁ f g ▷ s) ∙ invIso (comp-assoc s (pair f g) pr₁)))
      (pairing-triangle₁ (f ◁ γ) (g ◁ γ))
      (family-pair-pre-triangle₁ f g r) (family-pair-pre-triangle₁ f g s)
      (family-substitution-square-projection pr₁ (pair f g) f (pair-β₁ f g) γ))
    (family-projected-square pr₂ output before after input
      (pair-β₂ (f ∘ r) (g ∘ r)) (pair-β₂ (f ∘ s) (g ∘ s)) (g ◁ γ)
      (const ((pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂)))
      (const ((pair-β₂ f g ▷ s) ∙ invIso (comp-assoc s (pair f g) pr₂)))
      (pairing-triangle₂ (f ◁ γ) (g ◁ γ))
      (family-pair-pre-triangle₂ f g r) (family-pair-pre-triangle₂ f g s)
      (family-substitution-square-projection pr₂ (pair f g) g (pair-β₂ f g) γ))

family-pair-pre-full : {A R X C D : CAT}
  {f f′ : MAP X C} {g g′ : MAP X D} {r s : MAP R X}
  (α : MAP A (f ≅ f′)) (β : MAP A (g ≅ g′)) (γ : MAP A (r ≅ s))
  → NatIso (pairing (α ⋆ γ) (β ⋆ γ) ∙ const (pair-pre f g r))
      (const (pair-pre f′ g′ s) ∙ (pairing α β ⋆ γ))
family-pair-pre-full {f = f} {f′} {g} {g′} {r} {s} α β γ =
  let outer = pairing (α ▷ s) (β ▷ s)
      inner = pairing (f ◁ γ) (g ◁ γ)
      before = const (pair-pre f g r)
      middle = const (pair-pre f g s)
      after = const (pair-pre f′ g′ s)
      input = pairing α β ▷ s
      substitution = pair f g ◁ γ
  in assoc after input substitution ∙
    (isoComp-cong (family-pair-pre-inputs α β s) (idIso substitution) ∙
      (invIso (assoc outer middle substitution) ∙
        (isoComp-cong (idIso outer) (family-pair-pre-substitution f g γ) ∙
          (assoc outer inner before ∙
            isoComp-cong (pairing-composition (α ▷ s) (f ◁ γ) (β ▷ s) (g ◁ γ))
              (idIso before)))))
```

The following instance records the three independently varying inputs. The
two boundary maps have this actual product as their common source. This is
not obtained by choosing a witness separately at each absolute input.

```agda
module ThreeInputs {R X C D : CAT}
  (f f′ : MAP X C) (g g′ : MAP X D) (r s : MAP R X) where

  Parameter : CAT
  Parameter = ((f ≅ f′) × (g ≅ g′)) × (r ≅ s)

  α : MAP Parameter (f ≅ f′)
  α = pr₁ ∘ pr₁

  β : MAP Parameter (g ≅ g′)
  β = pr₂ ∘ pr₁

  γ : MAP Parameter (r ≅ s)
  γ = pr₂

  naturality : NatIso
    (pairing (α ⋆ γ) (β ⋆ γ) ∙ const (pair-pre f g r))
    (const (pair-pre f′ g′ s) ∙ (pairing α β ⋆ γ))
  naturality = family-pair-pre-full α β γ
```

