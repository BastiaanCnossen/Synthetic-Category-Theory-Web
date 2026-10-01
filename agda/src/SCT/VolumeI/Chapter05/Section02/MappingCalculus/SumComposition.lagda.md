# The dependent-sum composition comparison

The chosen comparison for composition of dependent sums is reflected
from a chain of local identifications. We compute its restriction and
paste the naturality squares for the six parts of that chain. Reflection
then gives naturality of the original chosen comparison separately in
each local functor. No replacement comparison or extra coherence is supplied.

The restriction calculation also compares composition of local functors
with successive restriction of an absolute functor. Its proof retains
the sum compositor, the absolute associator, and the local associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumPostcomposition as Post
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumComposition
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q using (Σ; pair; flatten)
open Action W P Q using (Σ-map; Σ-map-β; Σ-map-cong; Σ-map-comp; flatten-post; flatten-local-pre)
open Identifications W K P Q using (action; reflect₂; reflect-β; action-comp; action-inverse; sum-β-natural)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_; isoComp-cong; interchange-at; isoComp-assoc-at;
  isoComp-inverseˡ-at; isoComp-unitˡ-at; postWhisker-isoComp-at; preWhisker-isoComp-at; three-prefix)
open Pasting W K P using (paste; post-square)
open Structural T.vocabulary T.terminal T.products T.productLaws T.composition T.whiskering
  using (postWhisker-comp-at; preWhisker-comp-at; whisker-mixed-at)
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square; cancel-left)
open Inverses T using (inverse-composite; inverse-inverse; pre-inverse)
open Projection T using (post-inverse)
open Iterated T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering T.pentagonTriangle
  using (pentagon-whiskered; solve-pentagon)

restriction-composite : {B C D : T.CAT} (f : T.MAP B C) (g : T.MAP C D)
  → T._=₁_ (flatten (Σ-map (g ∘ f))) (flatten (S._∘_ (Σ-map g) (Σ-map f)))
restriction-composite {C = C} {D} f g = (Σ-map-β (g ∘ f)) ⁻¹ then
  (T.comp-assoc f g (pair D)) ⁻¹ then (Σ-map-β g ▷ f) then
  T.comp-assoc f (pair C) (W.map (Σ-map g)) then
  (W.map (Σ-map g) ◁ Σ-map-β f) then (flatten-post (Σ-map g) (Σ-map f)) ⁻¹

composition-image : {B C D : T.CAT} (f : T.MAP B C) (g : T.MAP C D)
  → T._=₂_ (action (Σ-map-comp f g)) (restriction-composite f g)
composition-image f g = reflect-β (restriction-composite f g)

module Restriction {B C D : T.CAT} (f : T.MAP B C) (g : T.MAP C D) where
  private
    u = Σ-map-β (g ∘ f)
    a = T.comp-assoc f g (pair D)
    b = T.comp-assoc f (pair C) (W.map (Σ-map g))
    β = Σ-map-β g ▷ f
    v = W.map (Σ-map g) ◁ Σ-map-β f
    h = flatten-post (Σ-map g) (Σ-map f)
    tail = v ∙ (b ∙ (β ∙ (a ⁻¹ ∙ u ⁻¹)))
    c = action (Σ-map-comp f g)
    inverse-rest = b ⁻¹ ∙ v ⁻¹

    inverse-tail : T._=₂_ (tail ⁻¹) (u ∙ (a ∙ (β ⁻¹ ∙ inverse-rest)))
    inverse-tail = inverse-composite v (b ∙ (β ∙ (a ⁻¹ ∙ u ⁻¹))) then
      isoComp-cong (inverse-composite b (β ∙ (a ⁻¹ ∙ u ⁻¹))) (T.idIso (v ⁻¹)) then
      isoComp-cong (isoComp-cong (inverse-composite β (a ⁻¹ ∙ u ⁻¹)) (T.idIso (b ⁻¹))) (T.idIso (v ⁻¹)) then
      isoComp-cong (isoComp-cong (isoComp-cong
        (inverse-composite (a ⁻¹) (u ⁻¹) then isoComp-cong (inverse-inverse u) (inverse-inverse a))
        (T.idIso (β ⁻¹))) (T.idIso (b ⁻¹))) (T.idIso (v ⁻¹)) then
      isoComp-assoc-at ((u ∙ a) ∙ β ⁻¹) (b ⁻¹) (v ⁻¹) then
      isoComp-assoc-at (u ∙ a) (β ⁻¹) inverse-rest then isoComp-assoc-at u a (β ⁻¹ ∙ inverse-rest)

  compositor : T._=₂_ (u ⁻¹ ∙ action (S._⁻¹ (Σ-map-comp f g)))
    (a ∙ (((Σ-map-β g) ⁻¹ ▷ f) ∙ flatten-local-pre (Σ-map g) f))
  compositor = isoComp-cong (T.idIso (u ⁻¹))
      (action-inverse (Σ-map-comp f g) then
        (T.＝-inv ◁ composition-image f g) then inverse-composite (h ⁻¹) tail then
        isoComp-cong inverse-tail (inverse-inverse h) then
        isoComp-assoc-at u (a ∙ (β ⁻¹ ∙ inverse-rest)) h) then
    cancel-left u ((a ∙ (β ⁻¹ ∙ inverse-rest)) ∙ h) then
    isoComp-assoc-at a (β ⁻¹ ∙ inverse-rest) h then
    isoComp-cong (T.idIso a)
      (isoComp-assoc-at (β ⁻¹) inverse-rest h then
        isoComp-cong ((pre-inverse (Σ-map-β g) f) ⁻¹)
          (isoComp-assoc-at (b ⁻¹) (v ⁻¹) h then
            isoComp-cong (T.idIso (b ⁻¹))
              (isoComp-cong ((post-inverse (W.map (Σ-map g)) (Σ-map-β f)) ⁻¹) (T.idIso h))))

  module Postcomposition {E : S.CAT} (k : S.MAP (Σ D) E) where
    private
      w = W.map k
      βinv = (Σ-map-β g) ⁻¹
      p = flatten-post k (Σ-map (g ∘ f))
      q = flatten-post k (S._∘_ (Σ-map g) (Σ-map f))
      z = action (S._◁_ k (S._⁻¹ (Σ-map-comp f g)))
      z′ = w ◁ action (S._⁻¹ (Σ-map-comp f g))
      r = T.comp-assoc (g ∘ f) (pair D) w
      r₀ = T.comp-assoc g (pair D) w
      s = T.comp-assoc f (pair D ∘ g) w
      t = T.comp-assoc f (flatten (Σ-map g)) w
      u₀ = T.comp-assoc f g (flatten k)
      x = w ◁ (βinv ▷ f)
      y = (w ◁ βinv) ▷ f
      local = w ◁ flatten-local-pre (Σ-map g) f
      v₀ = r₀ ⁻¹ ▷ f
      α = action (S.comp-assoc (Σ-map f) (Σ-map g) k)
      d = flatten-local-pre (S._∘_ k (Σ-map g)) f
      n = flatten-post k (Σ-map g) ▷ f

      pentagon : T._=₂_ (r ⁻¹ ∙ (w ◁ a)) (u₀ ∙ (v₀ ∙ s ⁻¹))
      pentagon = (solve-pentagon r u₀ (w ◁ a) s (r₀ ▷ f)
        (pentagon-whiskered f g (pair D) w)) ⁻¹ then
        isoComp-cong (T.idIso u₀) (isoComp-cong ((pre-inverse r₀ f) ⁻¹) (T.idIso (s ⁻¹)))

      mixed : T._=₂_ (s ⁻¹ ∙ x) (y ∙ t ⁻¹)
      mixed = move-square s y x t (whisker-mixed-at βinv f w)

      normalized : T._=₂_ (flatten-local-pre k (g ∘ f) ∙ z)
        (u₀ ∙ (v₀ ∙ (y ∙ (t ⁻¹ ∙ (local ∙ q)))))
      normalized = isoComp-assoc-at (r ⁻¹) ((w ◁ u ⁻¹) ∙ p) z then
        isoComp-cong (T.idIso (r ⁻¹))
          (isoComp-assoc-at (w ◁ u ⁻¹) p z then
            isoComp-cong (T.idIso (w ◁ u ⁻¹)) (Post.naturality W K P Q k (S._⁻¹ (Σ-map-comp f g))) then
            (isoComp-assoc-at (w ◁ u ⁻¹) z′ q) ⁻¹ then
            isoComp-cong ((postWhisker-isoComp-at w (u ⁻¹) (action (S._⁻¹ (Σ-map-comp f g)))) ⁻¹ then
              (T.postWhisker w ◁ compositor) then
              postWhisker-isoComp-at w a ((βinv ▷ f) ∙ flatten-local-pre (Σ-map g) f) then
              isoComp-cong (T.idIso (w ◁ a))
                (postWhisker-isoComp-at w (βinv ▷ f) (flatten-local-pre (Σ-map g) f))) (T.idIso q) then
            isoComp-assoc-at (w ◁ a) (x ∙ local) q then
            isoComp-cong (T.idIso (w ◁ a)) (isoComp-assoc-at x local q)) then
        (isoComp-assoc-at (r ⁻¹) (w ◁ a) (x ∙ (local ∙ q))) ⁻¹ then
        isoComp-cong pentagon (T.idIso (x ∙ (local ∙ q))) then
        isoComp-assoc-at u₀ (v₀ ∙ s ⁻¹) (x ∙ (local ∙ q)) then
        isoComp-cong (T.idIso u₀)
          (isoComp-assoc-at v₀ (s ⁻¹) (x ∙ (local ∙ q)) then
            isoComp-cong (T.idIso v₀)
              ((isoComp-assoc-at (s ⁻¹) x (local ∙ q)) ⁻¹ then
                isoComp-cong mixed (T.idIso (local ∙ q)) then isoComp-assoc-at y (t ⁻¹) (local ∙ q)))

    comparison : T._=₂_ ((flatten-local-pre k (g ∘ f) ∙ z) ∙ α)
      (u₀ ∙ ((flatten-local-pre k g ▷ f) ∙ d))
    comparison = isoComp-cong normalized (T.idIso α) then
      isoComp-assoc-at u₀ (v₀ ∙ (y ∙ (t ⁻¹ ∙ (local ∙ q)))) α then
      isoComp-cong (T.idIso u₀)
        (isoComp-assoc-at v₀ (y ∙ (t ⁻¹ ∙ (local ∙ q))) α then
          isoComp-cong (T.idIso v₀)
            (isoComp-assoc-at y (t ⁻¹ ∙ (local ∙ q)) α then
              isoComp-cong (T.idIso y)
                (isoComp-assoc-at (t ⁻¹) (local ∙ q) α then
                  isoComp-cong (T.idIso (t ⁻¹)) (isoComp-assoc-at local q α) then
                  (Post.local-post-associativity W K P Q (Σ-map g) k f) ⁻¹)) then
          three-prefix v₀ y n d then
          isoComp-cong
            (isoComp-cong (T.idIso v₀) ((preWhisker-isoComp-at (w ◁ βinv) (flatten-post k (Σ-map g)) f) ⁻¹) then
              (preWhisker-isoComp-at (r₀ ⁻¹) ((w ◁ βinv) ∙ flatten-post k (Σ-map g)) f) ⁻¹)
            (T.idIso d))

module FirstVariable {B C D : T.CAT} {f k : T.MAP B C}
  (α : T._=₁_ f k) (g : T.MAP C D) where

  private
    m = W.map (Σ-map g)
    a₀ = action (Σ-map-cong (g ◁ α))
    a₁ = pair D ◁ (g ◁ α)
    a₂ = (pair D ∘ g) ◁ α
    a₃ = (m ∘ pair C) ◁ α
    a₄ = m ◁ (pair C ◁ α)
    a₅ = m ◁ action (Σ-map-cong α)
    a₆ = action (S._◁_ (Σ-map g) (Σ-map-cong α))
    u₀ = (Σ-map-β (g ∘ f)) ⁻¹
    u₁ = (Σ-map-β (g ∘ k)) ⁻¹
    v₀ = (T.comp-assoc f g (pair D)) ⁻¹
    v₁ = (T.comp-assoc k g (pair D)) ⁻¹
    w₀ = Σ-map-β g ▷ f
    w₁ = Σ-map-β g ▷ k
    x₀ = T.comp-assoc f (pair C) m
    x₁ = T.comp-assoc k (pair C) m
    y₀ = m ◁ Σ-map-β f
    y₁ = m ◁ Σ-map-β k
    z₀ = (flatten-post (Σ-map g) (Σ-map f)) ⁻¹
    z₁ = (flatten-post (Σ-map g) (Σ-map k)) ⁻¹

    first = move-square (Σ-map-β (g ∘ k)) a₁ a₀ (Σ-map-β (g ∘ f)) (sum-β-natural (g ◁ α))
    second = move-square (T.comp-assoc k g (pair D)) a₂ a₁
      (T.comp-assoc f g (pair D)) (postWhisker-comp-at α g (pair D))
    third = interchange-at (Σ-map-β g) α
    fourth = postWhisker-comp-at α (pair C) m
    fifth = post-square m (Σ-map-β f) (Σ-map-β k)
      (pair C ◁ α) (action (Σ-map-cong α)) (sum-β-natural α)
    sixth = move-square (flatten-post (Σ-map g) (Σ-map k)) a₆ a₅
      (flatten-post (Σ-map g) (Σ-map f)) (Post.naturality W K P Q (Σ-map g) (Σ-map-cong α))

  restriction-natural : T._=₂_ (restriction-composite k g ∙ a₀) (a₆ ∙ restriction-composite f g)
  restriction-natural = paste (y₀ ∙ (x₀ ∙ (w₀ ∙ (v₀ ∙ u₀)))) (y₁ ∙ (x₁ ∙ (w₁ ∙ (v₁ ∙ u₁))))
    z₀ z₁ a₀ a₅ a₆
    (paste (x₀ ∙ (w₀ ∙ (v₀ ∙ u₀))) (x₁ ∙ (w₁ ∙ (v₁ ∙ u₁))) y₀ y₁ a₀ a₄ a₅
      (paste (w₀ ∙ (v₀ ∙ u₀)) (w₁ ∙ (v₁ ∙ u₁)) x₀ x₁ a₀ a₃ a₄
        (paste (v₀ ∙ u₀) (v₁ ∙ u₁) w₀ w₁ a₀ a₂ a₃
          (paste u₀ u₁ v₀ v₁ a₀ a₁ a₂ first second) third) fourth) fifth) sixth

  naturality : S._=₂_ (S._∙_ (Σ-map-comp k g) (Σ-map-cong (g ◁ α)))
    (S._∙_ (S._◁_ (Σ-map g) (Σ-map-cong α)) (Σ-map-comp f g))
  naturality = reflect₂
    (action-comp (Σ-map-comp k g) (Σ-map-cong (g ◁ α)) then
      isoComp-cong (composition-image k g) (T.idIso _) then restriction-natural then
      isoComp-cong (T.idIso _) ((composition-image f g) ⁻¹) then
      (action-comp (S._◁_ (Σ-map g) (Σ-map-cong α)) (Σ-map-comp f g)) ⁻¹)

module SecondVariable {B C D : T.CAT} (f : T.MAP B C)
  {g h : T.MAP C D} (α : T._=₁_ g h) where

  private
    m₀ = W.map (Σ-map g)
    m₁ = W.map (Σ-map h)
    α′ = W.term (Σ-map-cong α)
    a₀ = action (Σ-map-cong (α ▷ f))
    a₁ = pair D ◁ (α ▷ f)
    a₂ = (pair D ◁ α) ▷ f
    a₃ = action (Σ-map-cong α) ▷ f
    a₄ = α′ ▷ (pair C ∘ f)
    a₅ = α′ ▷ flatten (Σ-map f)
    a₆ = action (S._▷_ (Σ-map-cong α) (Σ-map f))
    u₀ = (Σ-map-β (g ∘ f)) ⁻¹
    u₁ = (Σ-map-β (h ∘ f)) ⁻¹
    v₀ = (T.comp-assoc f g (pair D)) ⁻¹
    v₁ = (T.comp-assoc f h (pair D)) ⁻¹
    w₀ = Σ-map-β g ▷ f
    w₁ = Σ-map-β h ▷ f
    x₀ = T.comp-assoc f (pair C) m₀
    x₁ = T.comp-assoc f (pair C) m₁
    y₀ = m₀ ◁ Σ-map-β f
    y₁ = m₁ ◁ Σ-map-β f
    z₀ = (flatten-post (Σ-map g) (Σ-map f)) ⁻¹
    z₁ = (flatten-post (Σ-map h) (Σ-map f)) ⁻¹

    first = move-square (Σ-map-β (h ∘ f)) a₁ a₀ (Σ-map-β (g ∘ f)) (sum-β-natural (α ▷ f))
    second = move-square (T.comp-assoc f h (pair D)) a₂ a₁
      (T.comp-assoc f g (pair D)) (whisker-mixed-at α f (pair D))
    third = Post.pre-square W K P Q f (Σ-map-β g) (Σ-map-β h)
      (pair D ◁ α) (action (Σ-map-cong α)) (sum-β-natural α)
    fourth = preWhisker-comp-at α′ (pair C) f
    fifth = (interchange-at α′ (Σ-map-β f)) ⁻¹
    sixth = move-square (flatten-post (Σ-map h) (Σ-map f)) a₆ a₅
      (flatten-post (Σ-map g) (Σ-map f)) (Post.outer-naturality W K P Q (Σ-map-cong α) (Σ-map f))

  restriction-natural : T._=₂_ (restriction-composite f h ∙ a₀) (a₆ ∙ restriction-composite f g)
  restriction-natural = paste (y₀ ∙ (x₀ ∙ (w₀ ∙ (v₀ ∙ u₀)))) (y₁ ∙ (x₁ ∙ (w₁ ∙ (v₁ ∙ u₁))))
    z₀ z₁ a₀ a₅ a₆
    (paste (x₀ ∙ (w₀ ∙ (v₀ ∙ u₀))) (x₁ ∙ (w₁ ∙ (v₁ ∙ u₁))) y₀ y₁ a₀ a₄ a₅
      (paste (w₀ ∙ (v₀ ∙ u₀)) (w₁ ∙ (v₁ ∙ u₁)) x₀ x₁ a₀ a₃ a₄
        (paste (v₀ ∙ u₀) (v₁ ∙ u₁) w₀ w₁ a₀ a₂ a₃
          (paste u₀ u₁ v₀ v₁ a₀ a₁ a₂ first second) third) fourth) fifth) sixth

  naturality : S._=₂_ (S._∙_ (Σ-map-comp f h) (Σ-map-cong (α ▷ f)))
    (S._∙_ (S._▷_ (Σ-map-cong α) (Σ-map f)) (Σ-map-comp f g))
  naturality = reflect₂
    (action-comp (Σ-map-comp f h) (Σ-map-cong (α ▷ f)) then
      isoComp-cong (composition-image f h) (T.idIso _) then restriction-natural then
      isoComp-cong (T.idIso _) ((composition-image f g) ⁻¹) then
      (action-comp (S._▷_ (Σ-map-cong α) (Σ-map f)) (Σ-map-comp f g)) ⁻¹)
```
