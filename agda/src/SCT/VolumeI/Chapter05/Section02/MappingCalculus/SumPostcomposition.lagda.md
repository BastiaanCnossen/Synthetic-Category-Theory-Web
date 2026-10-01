# Postcomposition under restriction to a local category

The comparison between restriction and postcomposition is natural on
identifications. Its first part is the postwhiskering comparison for
weakening, restricted along the pair functor. Its second part is the
mixed whiskering coherence in the local theory.
The same comparison is natural in the postcomposing functor, using
prewhiskering coherence instead.

It also respects reassociation of three absolute functors. The proof
uses the associator comparison for weakening and the local pentagon,
retaining the specified associativity identifications.

Combining the latter calculation with the extension computation gives
naturality of restriction along the total functor of a local functor.
The two final calculations vary the absolute functor and the local
restricting functor separately.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumPostcomposition
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q using (Σ; pair; flatten)
open Action W P Q using (flatten-post; flatten-local-pre; Σ-map; Σ-map-β)
open Identifications W K P Q using (action; sum-β-natural)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_; preWhisker-isoComp-at; postWhisker-isoComp-at;
  isoComp-cong; isoComp-assoc-at; isoComp-inverseʳ-at; isoComp-unitˡ-at; interchange-at; three-prefix)
open Pasting W K P using (paste; post-square)
open Structural T.vocabulary T.terminal T.products T.productLaws T.composition T.whiskering
  using (whisker-mixed-at; preWhisker-comp-at; postWhisker-comp-at)
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square; cancel-left; cancel-left-reflect)
open Projection T using (post-inverse)
open Iterated T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering T.pentagonTriangle
  using (pentagon-whiskered)

associativity : {B : T.CAT} {C D E : S.CAT}
  (p : S.MAP (Σ B) C) (q : S.MAP C D) (r : S.MAP D E)
  → T._=₂_
    (((W.map r ◁ flatten-post q p) ∙ flatten-post r (S._∘_ q p)) ∙ action (S.comp-assoc p q r))
    (T.comp-assoc (flatten p) (W.map q) (W.map r) ∙
      ((W.comp q r ▷ flatten p) ∙ flatten-post (S._∘_ r q) p))
associativity {B} p q r =
  isoComp-cong (isoComp-cong (postWhisker-isoComp-at c aq cx) (T.idIso (ar ∙ dx))) (T.idIso t) then
  isoComp-assoc-at (u ∙ v) (ar ∙ dx) t then
  isoComp-cong (T.idIso (u ∙ v)) (isoComp-assoc-at ar dx t) then
  isoComp-assoc-at u v (ar ∙ (dx ∙ t)) then
  isoComp-cong (T.idIso u)
    ((isoComp-assoc-at v ar (dx ∙ t)) ⁻¹ then
      isoComp-cong ((whisker-mixed-at (W.comp p q) x c) ⁻¹) (T.idIso (dx ∙ t)) then
      isoComp-assoc-at d ax (dx ∙ t) then isoComp-cong (T.idIso d) weakened-associator) then
  three-prefix u d bx (ex ∙ fx) then
  isoComp-cong ((pentagon-whiskered x a b c) ⁻¹) (T.idIso (ex ∙ fx)) then
  isoComp-assoc-at ap ab (ex ∙ fx) then
  isoComp-cong (T.idIso ap)
    ((isoComp-assoc-at ab ex fx) ⁻¹ then
      isoComp-cong (preWhisker-comp-at (W.comp q r) a x) (T.idIso fx) then
      isoComp-assoc-at (W.comp q r ▷ flatten p) af fx)
  where
  x = pair B
  a = W.map p
  b = W.map q
  c = W.map r
  aq = T.comp-assoc x a b
  cx = W.comp p q ▷ x
  ar = T.comp-assoc x (W.map (S._∘_ q p)) c
  dx = W.comp (S._∘_ q p) r ▷ x
  t = action (S.comp-assoc p q r)
  u = c ◁ aq
  v = c ◁ cx
  d = T.comp-assoc x (b ∘ a) c
  ax = (c ◁ W.comp p q) ▷ x
  bx = T.comp-assoc a b c ▷ x
  ex = (W.comp q r ▷ a) ▷ x
  fx = W.comp p (S._∘_ r q) ▷ x
  ap = T.comp-assoc (flatten p) b c
  ab = T.comp-assoc x a (c ∘ b)
  af = T.comp-assoc x a (W.map (S._∘_ r q))
  weakened-associator : T._=₂_ (ax ∙ (dx ∙ t)) (bx ∙ (ex ∙ fx))
  weakened-associator =
    isoComp-cong (T.idIso ax) ((preWhisker-isoComp-at (W.comp (S._∘_ q p) r)
      (W.term (S.comp-assoc p q r)) x) ⁻¹) then
    (preWhisker-isoComp-at (c ◁ W.comp p q)
      (W.comp (S._∘_ q p) r ∙ W.term (S.comp-assoc p q r)) x) ⁻¹ then
    (T.preWhisker x ◁ OperationCompatibility.associator K p q r) then
    preWhisker-isoComp-at (T.comp-assoc a b c)
      ((W.comp q r ▷ a) ∙ W.comp p (S._∘_ r q)) x then
    isoComp-cong (T.idIso bx) (preWhisker-isoComp-at (W.comp q r ▷ a) (W.comp p (S._∘_ r q)) x)

pre-square : {B C D : T.CAT} {x₀ x₁ y₀ y₁ : T.MAP C D}
  (r : T.MAP B C) (p : T._=₁_ x₀ y₀) (q : T._=₁_ x₁ y₁)
  (α : T._=₁_ x₀ x₁) (β : T._=₁_ y₀ y₁)
  → T._=₂_ (q ∙ α) (β ∙ p)
  → T._=₂_ ((q ▷ r) ∙ (α ▷ r)) ((β ▷ r) ∙ (p ▷ r))
pre-square r p q α β s = (preWhisker-isoComp-at q α r) ⁻¹ then
  (T.preWhisker r ◁ s) then preWhisker-isoComp-at β p r

naturality : {B : T.CAT} {D E : S.CAT} (f : S.MAP D E)
  {h k : S.MAP (Σ B) D} (α : S._=₁_ h k)
  → T._=₂_ (flatten-post f k ∙ action (S._◁_ f α))
      ((W.map f ◁ action α) ∙ flatten-post f h)
naturality {B} f {h} {k} α = paste
  (W.comp h f ▷ pair B) (W.comp k f ▷ pair B)
  (T.comp-assoc (pair B) (W.map h) (W.map f))
  (T.comp-assoc (pair B) (W.map k) (W.map f))
  (action (S._◁_ f α)) ((W.map f ◁ W.term α) ▷ pair B) (W.map f ◁ action α)
  (pre-square (pair B) (W.comp h f) (W.comp k f)
    (W.term (S._◁_ f α)) (W.map f ◁ W.term α)
    (Operations.post-term-square W K f α))
  (whisker-mixed-at (W.term α) (pair B) (W.map f))

outer-naturality : {B : T.CAT} {D E : S.CAT} {f g : S.MAP D E}
  (α : S._=₁_ f g) (h : S.MAP (Σ B) D)
  → T._=₂_ (flatten-post g h ∙ action (S._▷_ α h))
      ((W.term α ▷ flatten h) ∙ flatten-post f h)
outer-naturality {B} {f = f} {g} α h = paste
  (W.comp h f ▷ pair B) (W.comp h g ▷ pair B)
  (T.comp-assoc (pair B) (W.map h) (W.map f))
  (T.comp-assoc (pair B) (W.map h) (W.map g))
  (action (S._▷_ α h)) ((W.term α ▷ W.map h) ▷ pair B) (W.term α ▷ flatten h)
  (pre-square (pair B) (W.comp h f) (W.comp h g)
    (W.term (S._▷_ α h)) (W.term α ▷ W.map h)
    (Operations.pre-term-square W K h α))
  (preWhisker-comp-at (W.term α) (W.map h) (pair B))

local-restriction-naturality : {B C : T.CAT} {D : S.CAT}
  {h k : S.MAP (Σ C) D} (α : S._=₁_ h k) (r : T.MAP B C)
  → T._=₂_ (flatten-local-pre k r ∙ action (S._▷_ α (Σ-map r)))
      ((action α ▷ r) ∙ flatten-local-pre h r)
local-restriction-naturality {C = C} {h = h} {k} α r =
  isoComp-cong ((isoComp-assoc-at wk vk uk) ⁻¹) (T.idIso a₀) then
  paste uh uk (wh ∙ vh) (wk ∙ vk) a₀ a₁ a₃
    (outer-naturality α (Σ-map r))
    (paste vh vk wh wk a₁ a₂ a₃
      ((interchange-at (W.term α) ((Σ-map-β r) ⁻¹)) ⁻¹)
      (move-square (T.comp-assoc r (pair C) (W.map k)) a₃ a₂
        (T.comp-assoc r (pair C) (W.map h))
        (preWhisker-comp-at (W.term α) (pair C) r))) then
  isoComp-cong (T.idIso a₃) (isoComp-assoc-at wh vh uh)
  where
  a₀ = action (S._▷_ α (Σ-map r))
  a₁ = W.term α ▷ flatten (Σ-map r)
  a₂ = W.term α ▷ (pair C ∘ r)
  a₃ = action α ▷ r
  uh = flatten-post h (Σ-map r)
  uk = flatten-post k (Σ-map r)
  vh = W.map h ◁ (Σ-map-β r) ⁻¹
  vk = W.map k ◁ (Σ-map-β r) ⁻¹
  wh = (T.comp-assoc r (pair C) (W.map h)) ⁻¹
  wk = (T.comp-assoc r (pair C) (W.map k)) ⁻¹

local-functor-naturality : {B C : T.CAT} {D : S.CAT}
  (h : S.MAP (Σ C) D) {r s : T.MAP B C} (α : T._=₁_ r s)
  → T._=₂_ (flatten-local-pre h s ∙ action (S._◁_ h (Action.Σ-map-cong W P Q α)))
      ((flatten h ◁ α) ∙ flatten-local-pre h r)
local-functor-naturality {C = C} h {r} {s} α =
  isoComp-cong ((isoComp-assoc-at ws vs us) ⁻¹) (T.idIso a₀) then
  paste ur us (wr ∙ vr) (ws ∙ vs) a₀ a₁ a₃
    (naturality h (Action.Σ-map-cong W P Q α))
    (paste vr vs wr ws a₁ a₂ a₃
      (post-square (W.map h) ((Σ-map-β r) ⁻¹) ((Σ-map-β s) ⁻¹)
        (action (Action.Σ-map-cong W P Q α)) (pair C ◁ α)
        (move-square (Σ-map-β s) (pair C ◁ α)
          (action (Action.Σ-map-cong W P Q α)) (Σ-map-β r) (sum-β-natural α)))
      (move-square (T.comp-assoc s (pair C) (W.map h)) a₃ a₂
        (T.comp-assoc r (pair C) (W.map h))
        (postWhisker-comp-at α (pair C) (W.map h)))) then
  isoComp-cong (T.idIso a₃) (isoComp-assoc-at wr vr ur)
  where
  a₀ = action (S._◁_ h (Action.Σ-map-cong W P Q α))
  a₁ = W.map h ◁ action (Action.Σ-map-cong W P Q α)
  a₂ = W.map h ◁ (pair C ◁ α)
  a₃ = flatten h ◁ α
  ur = flatten-post h (Σ-map r)
  us = flatten-post h (Σ-map s)
  vr = W.map h ◁ (Σ-map-β r) ⁻¹
  vs = W.map h ◁ (Σ-map-β s) ⁻¹
  wr = (T.comp-assoc r (pair C) (W.map h)) ⁻¹
  ws = (T.comp-assoc s (pair C) (W.map h)) ⁻¹
```

Restriction along a total functor also commutes with absolute
postcomposition. The associator in this formula is the specified one.
Its compatibility follows from the preceding associativity calculation,
the local pentagon, and naturality of whiskering.

```agda
local-post-associativity : {B C : T.CAT} {D E : S.CAT}
  (p : S.MAP (Σ C) D) (q : S.MAP D E) (f : T.MAP B C)
  → T._=₂_
    ((flatten-post q p ▷ f) ∙ flatten-local-pre (S._∘_ q p) f)
    ((T.comp-assoc f (flatten p) (W.map q)) ⁻¹ ∙
      ((W.map q ◁ flatten-local-pre p f) ∙
        (flatten-post q (S._∘_ p (Σ-map f)) ∙ action (S.comp-assoc (Σ-map f) p q))))
local-post-associativity {C = C} p q f = cancel-left-reflect v
  (calculation then ((isoComp-assoc-at v (v ⁻¹) goal) ⁻¹ then
    isoComp-cong (isoComp-inverseʳ-at v) (T.idIso goal) then isoComp-unitˡ-at goal) ⁻¹)
  where
  i = pair C
  a = W.map p
  c = W.map q
  d = W.map (S._∘_ q p)
  δ = W.comp p q
  ν = (Σ-map-β f) ⁻¹
  z = flatten (Σ-map f)
  u = c ◁ T.comp-assoc f i a
  u′ = c ◁ (T.comp-assoc f i a) ⁻¹
  v = T.comp-assoc f (flatten p) c
  b = T.comp-assoc i a c ▷ f
  t = (δ ▷ i) ▷ f
  r = T.comp-assoc f i d
  s = T.comp-assoc f i (c ∘ a)
  e = T.comp-assoc (i ∘ f) a c
  e′ = T.comp-assoc z a c
  δ₀ = δ ▷ (i ∘ f)
  δ₁ = δ ▷ z
  h = flatten-post (S._∘_ q p) (Σ-map f)
  k = flatten-post q (S._∘_ p (Σ-map f))
  α = action (S.comp-assoc (Σ-map f) p q)
  goal = (c ◁ flatten-local-pre p f) ∙ (k ∙ α)
  moved : T._=₂_ (t ∙ r ⁻¹) (s ⁻¹ ∙ δ₀)
  moved = (move-square s t δ₀ r (preWhisker-comp-at δ i f)) ⁻¹
  pentagon : T._=₂_ ((v ∙ b) ∙ s ⁻¹) (u′ ∙ e)
  pentagon = (move-square u (v ∙ b) e s ((pentagon-whiskered f i a c) ⁻¹)) ⁻¹ then
    isoComp-cong ((post-inverse c (T.comp-assoc f i a)) ⁻¹) (T.idIso e)
  calculation : T._=₂_
    (v ∙ ((flatten-post q p ▷ f) ∙ flatten-local-pre (S._∘_ q p) f)) goal
  calculation =
    isoComp-cong (T.idIso v)
      (isoComp-cong (preWhisker-isoComp-at (T.comp-assoc i a c) (δ ▷ i) f) (T.idIso _) then
        isoComp-assoc-at b t (r ⁻¹ ∙ ((d ◁ ν) ∙ h)) then
        isoComp-cong (T.idIso b)
          ((isoComp-assoc-at t (r ⁻¹) ((d ◁ ν) ∙ h)) ⁻¹ then
            isoComp-cong moved (T.idIso _) then
            isoComp-assoc-at (s ⁻¹) δ₀ ((d ◁ ν) ∙ h) then
            isoComp-cong (T.idIso (s ⁻¹))
              ((isoComp-assoc-at δ₀ (d ◁ ν) h) ⁻¹ then
                isoComp-cong (interchange-at δ ν) (T.idIso h) then
                isoComp-assoc-at ((c ∘ a) ◁ ν) δ₁ h))) then
    three-prefix v b (s ⁻¹) (((c ∘ a) ◁ ν) ∙ (δ₁ ∙ h)) then
    isoComp-cong ((isoComp-assoc-at v b (s ⁻¹)) ⁻¹ then pentagon) (T.idIso _) then
    isoComp-assoc-at u′ e (((c ∘ a) ◁ ν) ∙ (δ₁ ∙ h)) then
    isoComp-cong (T.idIso u′)
      ((isoComp-assoc-at e ((c ∘ a) ◁ ν) (δ₁ ∙ h)) ⁻¹ then
        isoComp-cong (postWhisker-comp-at ν a c) (T.idIso _) then
        isoComp-assoc-at (c ◁ (a ◁ ν)) e′ (δ₁ ∙ h) then
        isoComp-cong (T.idIso (c ◁ (a ◁ ν)))
          ((associativity (Σ-map f) p q) ⁻¹ then
            isoComp-assoc-at (c ◁ flatten-post p (Σ-map f)) k α)) then
    three-prefix u′ (c ◁ (a ◁ ν)) (c ◁ flatten-post p (Σ-map f)) (k ∙ α) then
    isoComp-cong
      (isoComp-cong (T.idIso u′) ((postWhisker-isoComp-at c (a ◁ ν) (flatten-post p (Σ-map f))) ⁻¹) then
        (postWhisker-isoComp-at c ((T.comp-assoc f i a) ⁻¹) ((a ◁ ν) ∙ flatten-post p (Σ-map f))) ⁻¹)
      (T.idIso (k ∙ α))
```
