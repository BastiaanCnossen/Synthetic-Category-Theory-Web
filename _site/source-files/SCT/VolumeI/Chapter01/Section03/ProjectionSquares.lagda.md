# Squares with specified projection witnesses

The projection witnesses below may land in any fixed category. They need
not be product projections. This lets the same calculation track a
parameter before and after a change of base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting as ParameterSquarePasting

module SCT.VolumeI.Chapter01.Section03.ProjectionSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (project-composite; pre-square-projection; substitution-square-projection;
         cancel-left; cancel-left-reflect; move-square)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

Square : {X Y B : CAT} (π : MAP Y B) {f g : MAP X Y} {q : MAP X B}
  → =₁ (π ∘ f) q → =₁ (π ∘ g) q → =₁ f g → Set m
Square π bf bg α = =₂ (bg ∙ (π ◁ α)) bf

compose-base : {X Y Z B : CAT} (π : MAP Z B)
  (g : MAP Y Z) {q : MAP Y B} (bg : =₁ (π ∘ g) q)
  (f : MAP X Y) {r : MAP X B} (bf : =₁ (q ∘ f) r)
  → =₁ (π ∘ (g ∘ f)) r
compose-base π g bg f bf = bf ∙ transport-pre π g bg f

abstract
  compose-square : {X Y B : CAT} (π : MAP Y B)
    {f g h : MAP X Y} {q : MAP X B}
    (bf : =₁ (π ∘ f) q) (bg : =₁ (π ∘ g) q) (bh : =₁ (π ∘ h) q)
    (β : =₁ g h) (α : =₁ f g)
    → Square π bg bh β → Square π bf bg α → Square π bf bh (β ∙ α)
  compose-square π bf bg bh β α b a = a ∙
    (isoComp-cong b (idIso (π ◁ α)) ∙ project-composite π β α bh)

  inverse-square : {X Y B : CAT} (π : MAP Y B)
    {f g : MAP X Y} {q : MAP X B}
    (bf : =₁ (π ∘ f) q) (bg : =₁ (π ∘ g) q) (α : =₁ f g)
    → Square π bf bg α → Square π bg bf (invIso α)
  inverse-square π bf bg α compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            invIso (postWhisker-isoComp-at π α (invIso α)))
    in isoComp-unitʳ-at bg ∙
      (isoComp-cong (idIso bg) cancel-image ∙
      (isoComp-assoc-at bg (π ◁ α) (π ◁ invIso α) ∙
        isoComp-cong (invIso compatible) (idIso (π ◁ invIso α))))

  pre-square : {X Y Z B : CAT} (π : MAP Z B)
    {g g′ : MAP Y Z} {q : MAP Y B} (f : MAP X Y) {r : MAP X B}
    (bg : =₁ (π ∘ g) q) (bg′ : =₁ (π ∘ g′) q)
    (bf : =₁ (q ∘ f) r) (α : =₁ g g′)
    → Square π bg bg′ α
    → Square π (compose-base π g bg f bf) (compose-base π g′ bg′ f bf) (α ▷ f)
  pre-square π {g = g} {g′} {q} f bg bg′ bf α compatible =
    let first = pre-square-projection π α (idIso q) bg bg′ f
          (invIso (isoComp-unitˡ-at bg) ∙ compatible)
        normalized = isoComp-unitˡ-at (transport-pre π g bg f) ∙
          isoComp-cong (preWhisker-idIso q f) (idIso (transport-pre π g bg f))
    in isoComp-cong (idIso bf) (normalized ∙ first) ∙
      isoComp-assoc-at bf (transport-pre π g′ bg′ f) (π ◁ (α ▷ f))

  post-square : {X Y Z B : CAT} (π : MAP Z B)
    (g : MAP Y Z) {q : MAP Y B} {f f′ : MAP X Y} {r : MAP X B}
    (bg : =₁ (π ∘ g) q)
    (bf : =₁ (q ∘ f) r) (bf′ : =₁ (q ∘ f′) r) (α : =₁ f f′)
    → Square q bf bf′ α
    → Square π (compose-base π g bg f bf) (compose-base π g bg f′ bf′) (g ◁ α)
  post-square π g {q} {f} {f′} bg bf bf′ α compatible =
    isoComp-cong compatible (idIso (transport-pre π g bg f)) ∙
    (invIso (isoComp-assoc-at bf′ (q ◁ α) (transport-pre π g bg f)) ∙
    (isoComp-cong (idIso bf′) (substitution-square-projection π g q bg α) ∙
      isoComp-assoc-at bf′ (transport-pre π g bg f′) (π ◁ (g ◁ α))))

  associator-square : {W X Y Z B : CAT} (π : MAP Z B)
    (h : MAP Y Z) (g : MAP X Y) (f : MAP W X)
    {q : MAP Y B} {r : MAP X B} {s : MAP W B}
    (bh : =₁ (π ∘ h) q) (bg : =₁ (q ∘ g) r) (bf : =₁ (r ∘ f) s)
    → Square π
        (compose-base π (h ∘ g) (compose-base π h bh g bg) f bf)
        (compose-base π h bh (g ∘ f) (compose-base q g bg f bf))
        (comp-assoc f g h)
  associator-square π h g f {q} bh bg bf =
    let A = comp-assoc f g q
        D′ = comp-assoc f (h ∘ g) π
        t = transport-pre π h bh g ▷ f
        u = bg ▷ f
        v = transport-pre π h bh (g ∘ f)
        w = π ◁ comp-assoc f g h
        middle = isoComp-cong (invIso (preWhisker-isoComp-at bg (transport-pre π h bh g) f))
            (idIso (invIso D′)) ∙
          (invIso (isoComp-assoc-at u t (invIso D′)) ∙
          (isoComp-cong (idIso u) (isoComp-cong (cancel-left A t) (idIso (invIso D′))) ∙
            reassociateFour u (invIso A) (A ∙ t) (invIso D′)))
    in isoComp-cong (idIso bf)
        (middle ∙ isoComp-cong (idIso (transport-pre q g bg f))
          (invIso (transport-pre-assoc π h q bh g f))) ∙
      (isoComp-assoc-at bf (transport-pre q g bg f) (v ∙ w) ∙
        isoComp-assoc-at (bf ∙ transport-pre q g bg f) v w)
```

Changing the target of a projection also preserves its square. The
associator in `lift-base` is retained explicitly.

```agda
lift-base : {X Y B B′ : CAT} (σ : MAP B B′) (π : MAP Y B)
  (f : MAP X Y) {q : MAP X B} (bf : =₁ (π ∘ f) q)
  → =₁ ((σ ∘ π) ∘ f) (σ ∘ q)
lift-base σ π f bf = (σ ◁ bf) ∙ comp-assoc f π σ

abstract
  lift-square : {X Y B B′ : CAT} (σ : MAP B B′) (π : MAP Y B)
    {f g : MAP X Y} {q : MAP X B}
    (bf : =₁ (π ∘ f) q) (bg : =₁ (π ∘ g) q) (α : =₁ f g)
    → Square π bf bg α
    → Square (σ ∘ π) (lift-base σ π f bf) (lift-base σ π g bg) α
  lift-square σ π {f} {g} bf bg α compatible =
    isoComp-cong
      ((postWhisker σ ◁ compatible) ∙ invIso (postWhisker-isoComp-at σ bg (π ◁ α)))
      (idIso (comp-assoc f π σ)) ∙
    (invIso (isoComp-assoc-at (σ ◁ bg) (σ ◁ (π ◁ α)) (comp-assoc f π σ)) ∙
    (isoComp-cong (idIso (σ ◁ bg)) (postWhisker-comp-at α π σ) ∙
      isoComp-assoc-at (σ ◁ bg) (comp-assoc g π σ) ((σ ∘ π) ◁ α)))

  post-inverse : {X B B′ : CAT} (σ : MAP B B′)
    {u v : MAP X B} (α : =₁ u v)
    → =₂ (σ ◁ invIso α) (invIso (σ ◁ α))
  post-inverse σ {u} α = cancel-right-reflect (σ ◁ α)
    (invIso (isoComp-inverseˡ-at (σ ◁ α)) ∙
    (postWhisker-idIso σ u ∙
    ((postWhisker σ ◁ isoComp-inverseˡ-at α) ∙
      invIso (postWhisker-isoComp-at σ (invIso α) α))))

  lift-compose : {X Y Z B B′ : CAT} (σ : MAP B B′) (π : MAP Z B)
    (g : MAP Y Z) (f : MAP X Y) {q : MAP Y B} {r : MAP X B}
    (bg : =₁ (π ∘ g) q) (bf : =₁ (q ∘ f) r)
    → =₂
        (compose-base (σ ∘ π) g (lift-base σ π g bg) f (lift-base σ q f bf))
        (lift-base σ π (g ∘ f) (compose-base π g bg f bf))
  lift-compose σ π g f {q} bg bf =
    let u = σ ◁ bf
        a = comp-assoc f q σ
        v = (σ ◁ bg) ▷ f
        b = comp-assoc g π σ ▷ f
        c = invIso (comp-assoc f g (σ ∘ π))
        d = σ ◁ (bg ▷ f)
        e = comp-assoc f (π ∘ g) σ
        t = σ ◁ invIso (comp-assoc f g π)
        k = comp-assoc (g ∘ f) π σ
        p = σ ◁ comp-assoc f g π
        pentagon : =₂ (e ∙ (b ∙ c)) (t ∙ k)
        pentagon = isoComp-cong (invIso (post-inverse σ (comp-assoc f g π))) (idIso k) ∙
          (invIso (move-square p (e ∙ b) k (comp-assoc f g (σ ∘ π))
            (invIso (pentagon-whiskered f g π σ))) ∙
            invIso (isoComp-assoc-at e b c))
        middle : =₂ (a ∙ ((v ∙ b) ∙ c)) (d ∙ (t ∙ k))
        middle = isoComp-cong (idIso d) pentagon ∙
          (isoComp-assoc-at d e (b ∙ c) ∙
          (isoComp-cong (whisker-mixed-at bg f σ) (idIso (b ∙ c)) ∙
          (invIso (isoComp-assoc-at a v (b ∙ c)) ∙
            isoComp-cong (idIso a) (isoComp-assoc-at v b c))))
        merge : =₂ (u ∙ (d ∙ t)) (σ ◁ compose-base π g bg f bf)
        merge = invIso (postWhisker-isoComp-at σ bf (transport-pre π g bg f)) ∙
          isoComp-cong (idIso u)
            (invIso (postWhisker-isoComp-at σ (bg ▷ f) (invIso (comp-assoc f g π))))
    in isoComp-cong merge (idIso k) ∙
      (invIso (isoComp-assoc-at u (d ∙ t) k) ∙
      (isoComp-cong (idIso u) (invIso (isoComp-assoc-at d t k)) ∙
      (isoComp-cong (idIso u) middle ∙
      (isoComp-cong (idIso u)
        (isoComp-cong (idIso a)
          (isoComp-cong (preWhisker-isoComp-at (σ ◁ bg) (comp-assoc g π σ) f) (idIso c))) ∙
        isoComp-assoc-at u a ((lift-base σ π g bg ▷ f) ∙ c)))))
```

The five factors of a pasted square preserve its projection witness. The
intermediate witnesses follow the five corresponding parenthesizations.

```agda
module Pasting {X₀ X₁ X₂ Y₀ Y₁ Y₂ B : CAT}
  (p₀ : MAP X₀ B) (p₁ : MAP X₁ B) (p₂ : MAP X₂ B)
  (q₀ : MAP Y₀ B) (q₁ : MAP Y₁ B) (q₂ : MAP Y₂ B)
  (x₀ : MAP X₀ Y₀) (x₁ : MAP X₁ Y₁) (x₂ : MAP X₂ Y₂)
  (f : MAP X₀ X₁) (g : MAP X₁ X₂) (F : MAP Y₀ Y₁) (G : MAP Y₁ Y₂)
  (bf : =₁ (p₁ ∘ f) p₀) (bg : =₁ (p₂ ∘ g) p₁)
  (bF : =₁ (q₁ ∘ F) q₀) (bG : =₁ (q₂ ∘ G) q₁)
  (bx₀ : =₁ (q₀ ∘ x₀) p₀) (bx₁ : =₁ (q₁ ∘ x₁) p₁)
  (bx₂ : =₁ (q₂ ∘ x₂) p₂)
  (α : =₁ (x₁ ∘ f) (F ∘ x₀)) (β : =₁ (x₂ ∘ g) (G ∘ x₁)) where

  b₀ = compose-base q₂ x₂ bx₂ (g ∘ f) (compose-base p₂ g bg f bf)
  b₁ = compose-base q₂ (x₂ ∘ g) (compose-base q₂ x₂ bx₂ g bg) f bf
  b₂ = compose-base q₂ (G ∘ x₁) (compose-base q₂ G bG x₁ bx₁) f bf
  b₃ = compose-base q₂ G bG (x₁ ∘ f) (compose-base q₁ x₁ bx₁ f bf)
  b₄ = compose-base q₂ G bG (F ∘ x₀) (compose-base q₁ F bF x₀ bx₀)
  b₅ = compose-base q₂ (G ∘ F) (compose-base q₂ G bG F bF) x₀ bx₀

  abstract
    paste-square :
      Square q₁ (compose-base q₁ x₁ bx₁ f bf) (compose-base q₁ F bF x₀ bx₀) α
      → Square q₂ (compose-base q₂ x₂ bx₂ g bg) (compose-base q₂ G bG x₁ bx₁) β
      → Square q₂ b₀ b₅ (paste β α)
    paste-square a b =
      let e₁ = invIso (comp-assoc f g x₂)
          e₂ = β ▷ f
          e₃ = comp-assoc f x₁ G
          e₄ = G ◁ α
          e₅ = invIso (comp-assoc x₀ F G)
          s₁ = inverse-square q₂ b₁ b₀ (comp-assoc f g x₂)
            (associator-square q₂ x₂ g f bx₂ bg bf)
          s₂ = pre-square q₂ f
            (compose-base q₂ x₂ bx₂ g bg) (compose-base q₂ G bG x₁ bx₁) bf β b
          s₃ = associator-square q₂ G x₁ f bG bx₁ bf
          s₄ = post-square q₂ G bG
            (compose-base q₁ x₁ bx₁ f bf) (compose-base q₁ F bF x₀ bx₀) α a
          s₅ = inverse-square q₂ b₅ b₄ (comp-assoc x₀ F G)
            (associator-square q₂ G F x₀ bG bF bx₀)
      in compose-square q₂ b₀ b₄ b₅ e₅ (e₄ ∙ (e₃ ∙ (e₂ ∙ e₁))) s₅
        (compose-square q₂ b₀ b₃ b₄ e₄ (e₃ ∙ (e₂ ∙ e₁)) s₄
        (compose-square q₂ b₀ b₂ b₃ e₃ (e₂ ∙ e₁) s₃
          (compose-square q₂ b₀ b₁ b₂ e₂ e₁ s₂ s₁)))
```
