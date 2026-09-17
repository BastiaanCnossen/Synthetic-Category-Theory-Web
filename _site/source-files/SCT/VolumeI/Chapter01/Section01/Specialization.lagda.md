# Specializing parameterized comparisons

This module proves comparison lemmas from the supplied Section 1 interface.
In particular, product comparison lifting retains its two projection
witnesses, and the left and right vertical unit laws are specialized to
absolute natural isomorphisms without treating associativity as Agda equality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section01.Specialization
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Products.Comparison V P
open Products.ProductLaws PL
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
```

First apply the chosen inverse to the specified product comparison. The
resulting `image` comparison will supply both projection witnesses.

```agda
module ProductLift {X C D : CAT} {f g : MAP X (C × D)}
  (α : NatIso (pr₁ ∘ f) (pr₁ ∘ g))
  (β : NatIso (pr₂ ∘ f) (pr₂ ∘ g)) where

  private
    comparison = product-isoMap f g
    witness = product-isoMap-isEquiv f g
    back = IsEquiv.inverse witness
    point = pair α β

  lift : NatIso f g
  lift = back ∘ point

  image : NatIso (comparison ∘ lift) point
  image = comp-unitˡ point ∙
    (invIso (IsEquiv.retractionIso witness ▷ point) ∙
     invIso (comp-assoc point back comparison))

  β₁ : Iso₂ (pr₁ ◁ lift) α
  β₁ = ((pair-β₁ α β ∙ (pr₁ ◁ image)) ∙ comp-assoc lift comparison pr₁)
       ∙ invIso (pair-β₁ (postWhisker pr₁) (postWhisker pr₂) ▷ lift)

  β₂ : Iso₂ (pr₂ ◁ lift) β
  β₂ = ((pair-β₂ α β ∙ (pr₂ ◁ image)) ∙ comp-assoc lift comparison pr₂)
       ∙ invIso (pair-β₂ (postWhisker pr₁) (postWhisker pr₂) ▷ lift)

pair-iso : {X C D : CAT} {f g : MAP X (C × D)}
  → NatIso (pr₁ ∘ f) (pr₁ ∘ g) → NatIso (pr₂ ∘ f) (pr₂ ∘ g) → NatIso f g
pair-iso = ProductLift.lift

pair-iso-β₁ : {X C D : CAT} {f g : MAP X (C × D)}
  (α : NatIso (pr₁ ∘ f) (pr₁ ∘ g)) (β : NatIso (pr₂ ∘ f) (pr₂ ∘ g))
  → Iso₂ (pr₁ ◁ pair-iso α β) α
pair-iso-β₁ = ProductLift.β₁

pair-iso-β₂ : {X C D : CAT} {f g : MAP X (C × D)}
  (α : NatIso (pr₁ ∘ f) (pr₁ ∘ g)) (β : NatIso (pr₂ ∘ f) (pr₂ ∘ g))
  → Iso₂ (pr₂ ◁ pair-iso α β) β
pair-iso-β₂ = ProductLift.β₂
```

Pairing respects comparisons and precomposition through specified natural
isomorphisms. In `pair-pre`, the inverse associator exposes each projection
before the product beta comparison is used.

```agda
pair-cong : {X C D : CAT} {a a′ : MAP X C} {b b′ : MAP X D}
  → NatIso a a′ → NatIso b b′ → NatIso (pair a b) (pair a′ b′)
pair-cong {a = a} {a′} {b} {b′} α β = pair-iso
  (invIso (pair-β₁ a′ b′) ∙ (α ∙ pair-β₁ a b))
  (invIso (pair-β₂ a′ b′) ∙ (β ∙ pair-β₂ a b))

pair-pre : {R X C D : CAT} (a : MAP X C) (b : MAP X D) (r : MAP R X)
  → NatIso (pair a b ∘ r) (pair (a ∘ r) (b ∘ r))
pair-pre a b r = pair-iso
  (invIso (pair-β₁ (a ∘ r) (b ∘ r)) ∙
    ((pair-β₁ a b ▷ r) ∙ invIso (comp-assoc r (pair a b) pr₁)))
  (invIso (pair-β₂ (a ∘ r) (b ∘ r)) ∙
    ((pair-β₂ a b ▷ r) ∙ invIso (comp-assoc r (pair a b) pr₂)))

isoComp-cong : {X C D : CAT} {f g h : MAP C D}
  {β β′ : MAP X (g ≅ h)} {α α′ : MAP X (f ≅ g)}
  → NatIso β β′ → NatIso α α′ → NatIso (β ∙ α) (β′ ∙ α′)
isoComp-cong b a = isoComp ◁ pair-cong b a

isoComp-pre : {R X C D : CAT} {f g h : MAP C D}
  (β : MAP X (g ≅ h)) (α : MAP X (f ≅ g)) (r : MAP R X)
  → NatIso ((β ∙ α) ∘ r) ((β ∘ r) ∙ (α ∘ r))
isoComp-pre β α r = (isoComp ◁ pair-pre β α r) ∙ comp-assoc r (pair β α) isoComp
```

Whiskering and inversion commute with precomposition through the external
associator. Constants also use uniqueness of maps to the terminal category.

```agda
postWhisker-pre : {R X C D E : CAT} {f g : MAP C D}
  (u : MAP D E) (α : MAP X (f ≅ g)) (r : MAP R X)
  → NatIso ((u ◁ α) ∘ r) (u ◁ (α ∘ r))
postWhisker-pre u α r = comp-assoc r α (postWhisker u)

preWhisker-pre : {R X B C D : CAT} {f g : MAP C D}
  (α : MAP X (f ≅ g)) (k : MAP B C) (r : MAP R X)
  → NatIso ((α ▷ k) ∘ r) ((α ∘ r) ▷ k)
preWhisker-pre α k r = comp-assoc r α (preWhisker k)

invIso-pre : {R X C D : CAT} {f g : MAP C D}
  (α : MAP X (f ≅ g)) (r : MAP R X)
  → NatIso (invIso α ∘ r) (invIso (α ∘ r))
invIso-pre α r = comp-assoc r α isoInv

const-pre : {R X C : CAT} (x : ObjAbs C) (r : MAP R X)
  → NatIso (const x ∘ r) (const x)
const-pre {R} {X} x r =
  (x ◁ terminal-iso (terminate X ∘ r) (terminate R)) ∙ comp-assoc r (terminate X) x

const-One : {C : CAT} (x : ObjAbs C) → NatIso (const {P = One} x) x
const-One x = comp-unitʳ x ∙ (x ◁ terminal-iso (terminate One) (id One))

hcomp-pre : {R X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : MAP X (g ≅ g′)) (α : MAP X (f ≅ f′)) (r : MAP R X)
  → NatIso ((β ⋆ α) ∘ r) ((β ∘ r) ⋆ (α ∘ r))
hcomp-pre {f′ = f′} {g = g} β α r =
  isoComp-cong (preWhisker-pre β f′ r) (postWhisker-pre g α r)
  ∙ isoComp-pre (β ▷ f′) (g ◁ α) r

hcomp-cong : {X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  {β β′ : MAP X (g ≅ g′)} {α α′ : MAP X (f ≅ f′)}
  → NatIso β β′ → NatIso α α′ → NatIso (β ⋆ α) (β′ ⋆ α′)
hcomp-cong {f′ = f′} {g = g} b a =
  isoComp-cong (preWhisker f′ ◁ b) (postWhisker g ◁ a)

isoHComp-at : {C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : NatIso g g′) (α : NatIso f f′)
  → Iso₂ (isoHComp ∘ pair β α) (β ⋆ α)
isoHComp-at β α = hcomp-cong (pair-β₁ β α) (pair-β₂ β α)
                 ∙ hcomp-pre pr₁ pr₂ (pair β α)
```

Finally specialize a comparison, keeping the normalization of its two
boundaries explicit. The result below is composition of supplied witnesses;
it does not postulate coherent normalization of all expressions.

```agda
specialize : {R X Y : CAT} {f g : MAP X Y} {f′ g′ : MAP R Y}
  → NatIso f g → (r : MAP R X)
  → NatIso (f ∘ r) f′ → NatIso (g ∘ r) g′ → NatIso f′ g′
specialize κ r left right = (right ∙ (κ ▷ r)) ∙ invIso left

isoComp-evaluate : {R X C D : CAT} {f g h : MAP C D}
  (β : MAP X (g ≅ h)) (α : MAP X (f ≅ g)) (r : MAP R X)
  {β′ : MAP R (g ≅ h)} {α′ : MAP R (f ≅ g)}
  → NatIso (β ∘ r) β′ → NatIso (α ∘ r) α′
  → NatIso ((β ∙ α) ∘ r) (β′ ∙ α′)
isoComp-evaluate β α r b a = isoComp-cong b a ∙ isoComp-pre β α r

postWhisker-evaluate : {R X C D E : CAT} {f g : MAP C D}
  (u : MAP D E) (α : MAP X (f ≅ g)) (r : MAP R X)
  {α′ : MAP R (f ≅ g)} → NatIso (α ∘ r) α′
  → NatIso ((u ◁ α) ∘ r) (u ◁ α′)
postWhisker-evaluate u α r a = (postWhisker u ◁ a) ∙ postWhisker-pre u α r

preWhisker-evaluate : {R X B C D : CAT} {f g : MAP C D}
  (α : MAP X (f ≅ g)) (k : MAP B C) (r : MAP R X)
  {α′ : MAP R (f ≅ g)} → NatIso (α ∘ r) α′
  → NatIso ((α ▷ k) ∘ r) (α′ ▷ k)
preWhisker-evaluate α k r a = (preWhisker k ◁ a) ∙ preWhisker-pre α k r

const-evaluate : {X C : CAT} (x : ObjAbs C) (r : ObjAbs X)
  → NatIso (const x ∘ r) x
const-evaluate x r = const-One x ∙ const-pre x r

module TriplePoint {A B C : CAT} (γ : ObjAbs C) (β : ObjAbs B) (α : ObjAbs A) where
  point : ObjAbs ((C × B) × A)
  point = pair (pair γ β) α

  first : NatIso ((pr₁ ∘ pr₁) ∘ point) γ
  first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₁)

  second : NatIso ((pr₂ ∘ pr₁) ∘ point) β
  second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₂)

  third : NatIso (pr₂ ∘ point) α
  third = pair-β₂ (pair γ β) α

module Units (VC : Coherence.VerticalCoherence V T P S) where
  open Coherence.VerticalCoherence VC

  isoComp-unitˡ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (idIso g ∙ α) α
  isoComp-unitˡ-at {f = f} {g} α =
    specialize (isoComp-unitˡ f g) α
      (isoComp-cong (const-One (idIso g) ∙ const-pre (idIso g) α) (comp-unitˡ α)
       ∙ isoComp-pre (const (idIso g)) (id (f ≅ g)) α)
      (comp-unitˡ α)

  isoComp-unitʳ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (α ∙ idIso f) α
  isoComp-unitʳ-at {f = f} {g} α =
    specialize (isoComp-unitʳ f g) α
      (isoComp-cong (comp-unitˡ α) (const-One (idIso f) ∙ const-pre (idIso f) α)
       ∙ isoComp-pre (id (f ≅ g)) (const (idIso f)) α)
      (comp-unitˡ α)

  isoComp-inverseˡ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (invIso α ∙ α) (idIso f)
  isoComp-inverseˡ-at {f = f} {g} α =
    specialize (isoComp-inverseˡ f g) α
      (isoComp-evaluate (invIso (id (f ≅ g))) (id (f ≅ g)) α
        ((isoInv ◁ comp-unitˡ α) ∙ invIso-pre (id (f ≅ g)) α)
        (comp-unitˡ α))
      (const-evaluate (idIso f) α)

  isoComp-inverseʳ-at : {C D : CAT} {f g : MAP C D} (α : NatIso f g)
    → Iso₂ (α ∙ invIso α) (idIso g)
  isoComp-inverseʳ-at {f = f} {g} α =
    specialize (isoComp-inverseʳ f g) α
      (isoComp-evaluate (id (f ≅ g)) (invIso (id (f ≅ g))) α
        (comp-unitˡ α)
        ((isoInv ◁ comp-unitˡ α) ∙ invIso-pre (id (f ≅ g)) α))
      (const-evaluate (idIso g) α)

  isoComp-assoc-at : {C D : CAT} {f g h k : MAP C D}
    (γ : NatIso h k) (β : NatIso g h) (α : NatIso f g)
    → Iso₂ ((γ ∙ β) ∙ α) (γ ∙ (β ∙ α))
  isoComp-assoc-at {f = f} {g} {h} {k} γ β α =
    let open TriplePoint γ β α
    in specialize (isoComp-assoc f g h k) point
      (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ point
        (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) point first second) third)
      (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) point first
        (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ point second third))

module Whiskering (W : Coherence.WhiskeringCoherence V T P S) where
  open Coherence.WhiskeringCoherence W

  interchange-family : {X B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (τ : MAP X (F ≅ G)) (σ : MAP X (h ≅ k))
    → NatIso ((τ ▷ k) ∙ (F ◁ σ)) ((G ◁ σ) ∙ (τ ▷ h))
  interchange-family {F = F} {G} {h} {k} τ σ =
    let parameters = pair τ σ
    in specialize (interchange-joint F G h k) parameters
      (isoComp-evaluate (pr₁ ▷ k) (F ◁ pr₂) parameters
        (preWhisker-evaluate pr₁ k parameters (pair-β₁ τ σ))
        (postWhisker-evaluate F pr₂ parameters (pair-β₂ τ σ)))
      (isoComp-evaluate (G ◁ pr₂) (pr₁ ▷ h) parameters
        (postWhisker-evaluate G pr₂ parameters (pair-β₂ τ σ))
        (preWhisker-evaluate pr₁ h parameters (pair-β₁ τ σ)))

  interchange-fixedOuter : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
    (τ : NatIso F G)
    → let σ = id (h ≅ k)
      in NatIso (const (τ ▷ k) ∙ (F ◁ σ)) ((G ◁ σ) ∙ const (τ ▷ h))
  interchange-fixedOuter F G h k τ =
    let normalize : (r : MAP _ _) → NatIso (const τ ▷ r) (const (τ ▷ r))
        normalize r = invIso (comp-assoc (terminate (h ≅ k)) τ (preWhisker r))
    in isoComp-cong (idIso (G ◁ id (h ≅ k))) (normalize h) ∙
      (interchange-family (const τ) (id (h ≅ k)) ∙
        invIso (isoComp-cong (normalize k) (idIso (F ◁ id (h ≅ k)))))

  interchange-fixedInner : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
    (σ : NatIso h k)
    → let τ = id (F ≅ G)
      in NatIso ((τ ▷ k) ∙ const (F ◁ σ)) (const (G ◁ σ) ∙ (τ ▷ h))
  interchange-fixedInner F G h k σ =
    let normalize : (u : MAP _ _) → NatIso (u ◁ const σ) (const (u ◁ σ))
        normalize u = invIso (comp-assoc (terminate (F ≅ G)) σ (postWhisker u))
    in isoComp-cong (normalize G) (idIso (id (F ≅ G) ▷ h)) ∙
      (interchange-family (id (F ≅ G)) (const σ) ∙
        invIso (isoComp-cong (idIso (id (F ≅ G) ▷ k)) (normalize F)))

  postWhisker-isoComp-at : {C D E : CAT} {f g h : MAP C D}
    (u : MAP D E) (τ : NatIso g h) (σ : NatIso f g)
    → Iso₂ (u ◁ (τ ∙ σ)) ((u ◁ τ) ∙ (u ◁ σ))
  postWhisker-isoComp-at {f = f} {g} {h} u τ σ =
    let point = pair τ σ
    in specialize (postWhisker-isoComp f g h u) point
      (postWhisker-evaluate u (pr₁ ∙ pr₂) point
        (isoComp-evaluate pr₁ pr₂ point (pair-β₁ τ σ) (pair-β₂ τ σ)))
      (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) point
        (postWhisker-evaluate u pr₁ point (pair-β₁ τ σ))
        (postWhisker-evaluate u pr₂ point (pair-β₂ τ σ)))

  preWhisker-isoComp-at : {B C D : CAT} {f g h : MAP C D}
    (τ : NatIso g h) (σ : NatIso f g) (k : MAP B C)
    → Iso₂ ((τ ∙ σ) ▷ k) ((τ ▷ k) ∙ (σ ▷ k))
  preWhisker-isoComp-at {f = f} {g} {h} τ σ k =
    let point = pair τ σ
    in specialize (preWhisker-isoComp f g h k) point
      (preWhisker-evaluate (pr₁ ∙ pr₂) k point
        (isoComp-evaluate pr₁ pr₂ point (pair-β₁ τ σ) (pair-β₂ τ σ)))
      (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) point
        (preWhisker-evaluate pr₁ k point (pair-β₁ τ σ))
        (preWhisker-evaluate pr₂ k point (pair-β₂ τ σ)))

  interchange-at : {B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (τ : NatIso F G) (σ : NatIso h k)
    → Iso₂ ((τ ▷ k) ∙ (F ◁ σ)) ((G ◁ σ) ∙ (τ ▷ h))
  interchange-at {F = F} {G} {h} {k} τ σ =
    specialize (interchange-fixedOuter F G h k τ) σ
      (isoComp-evaluate (const (τ ▷ k)) (F ◁ id (h ≅ k)) σ
        (const-evaluate (τ ▷ k) σ)
        (postWhisker-evaluate F (id (h ≅ k)) σ (comp-unitˡ σ)))
      (isoComp-evaluate (G ◁ id (h ≅ k)) (const (τ ▷ h)) σ
        (postWhisker-evaluate G (id (h ≅ k)) σ (comp-unitˡ σ))
        (const-evaluate (τ ▷ h) σ))
```
