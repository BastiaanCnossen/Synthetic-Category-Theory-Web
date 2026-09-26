# Squares with specified projection witnesses

The projection witnesses below may land in any fixed category. They need
not be product projections. This lets the same calculation track a
parameter before and after a change of base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting as ParameterSquarePasting

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares
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
  → (π ∘ f) =₁ q → (π ∘ g) =₁ q → f =₁ g → Set m
Square π bf bg α = (bg ∙ (π ◁ α)) =₂ bf

compose-base : {X Y Z B : CAT} (π : MAP Z B)
  (g : MAP Y Z) {q : MAP Y B} (bg : (π ∘ g) =₁ q)
  (f : MAP X Y) {r : MAP X B} (bf : (q ∘ f) =₁ r)
  → (π ∘ (g ∘ f)) =₁ r
compose-base π g bg f bf = bf ∙ transport-pre π g bg f

abstract
  compose-square : {X Y B : CAT} (π : MAP Y B)
    {f g h : MAP X Y} {q : MAP X B}
    (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (bh : (π ∘ h) =₁ q)
    (β : g =₁ h) (α : f =₁ g)
    → Square π bg bh β → Square π bf bg α → Square π bf bh (β ∙ α)
  compose-square π bf bg bh β α b a = a ∙
    (isoComp-cong b (idIso (π ◁ α)) ∙ project-composite π β α bh)

  inverse-square : {X Y B : CAT} (π : MAP Y B)
    {f g : MAP X Y} {q : MAP X B}
    (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (α : f =₁ g)
    → Square π bf bg α → Square π bg bf (α ⁻¹)
  inverse-square π bf bg α compatible =
    let cancel-image = postWhisker-idIso π _ ∙
          ((postWhisker π ◁ isoComp-inverseʳ-at α) ∙
            (postWhisker-isoComp-at π α (α ⁻¹)) ⁻¹)
    in isoComp-unitʳ-at bg ∙
      (isoComp-cong (idIso bg) cancel-image ∙
      (isoComp-assoc-at bg (π ◁ α) (π ◁ α ⁻¹) ∙
        isoComp-cong (compatible ⁻¹) (idIso (π ◁ α ⁻¹))))

  pre-square : {X Y Z B : CAT} (π : MAP Z B)
    {g g′ : MAP Y Z} {q : MAP Y B} (f : MAP X Y) {r : MAP X B}
    (bg : (π ∘ g) =₁ q) (bg′ : (π ∘ g′) =₁ q)
    (bf : (q ∘ f) =₁ r) (α : g =₁ g′)
    → Square π bg bg′ α
    → Square π (compose-base π g bg f bf) (compose-base π g′ bg′ f bf) (α ▷ f)
  pre-square π {g = g} {g′} {q} f bg bg′ bf α compatible =
    let first = pre-square-projection π α (idIso q) bg bg′ f
          ((isoComp-unitˡ-at bg) ⁻¹ ∙ compatible)
        normalized = isoComp-unitˡ-at (transport-pre π g bg f) ∙
          isoComp-cong (preWhisker-idIso q f) (idIso (transport-pre π g bg f))
    in isoComp-cong (idIso bf) (normalized ∙ first) ∙
      isoComp-assoc-at bf (transport-pre π g′ bg′ f) (π ◁ (α ▷ f))

  post-square : {X Y Z B : CAT} (π : MAP Z B)
    (g : MAP Y Z) {q : MAP Y B} {f f′ : MAP X Y} {r : MAP X B}
    (bg : (π ∘ g) =₁ q)
    (bf : (q ∘ f) =₁ r) (bf′ : (q ∘ f′) =₁ r) (α : f =₁ f′)
    → Square q bf bf′ α
    → Square π (compose-base π g bg f bf) (compose-base π g bg f′ bf′) (g ◁ α)
  post-square π g {q} {f} {f′} bg bf bf′ α compatible =
    isoComp-cong compatible (idIso (transport-pre π g bg f)) ∙
    ((isoComp-assoc-at bf′ (q ◁ α) (transport-pre π g bg f)) ⁻¹ ∙
    (isoComp-cong (idIso bf′) (substitution-square-projection π g q bg α) ∙
      isoComp-assoc-at bf′ (transport-pre π g bg f′) (π ◁ (g ◁ α))))

  associator-square : {W X Y Z B : CAT} (π : MAP Z B)
    (h : MAP Y Z) (g : MAP X Y) (f : MAP W X)
    {q : MAP Y B} {r : MAP X B} {s : MAP W B}
    (bh : (π ∘ h) =₁ q) (bg : (q ∘ g) =₁ r) (bf : (r ∘ f) =₁ s)
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
        middle = isoComp-cong ((preWhisker-isoComp-at bg (transport-pre π h bh g) f) ⁻¹)
            (idIso (D′ ⁻¹)) ∙
          ((isoComp-assoc-at u t (D′ ⁻¹)) ⁻¹ ∙
          (isoComp-cong (idIso u) (isoComp-cong (cancel-left A t) (idIso (D′ ⁻¹))) ∙
            reassociateFour u (A ⁻¹) (A ∙ t) (D′ ⁻¹)))
    in isoComp-cong (idIso bf)
        (middle ∙ isoComp-cong (idIso (transport-pre q g bg f))
          ((transport-pre-assoc π h q bh g f) ⁻¹)) ∙
      (isoComp-assoc-at bf (transport-pre q g bg f) (v ∙ w) ∙
        isoComp-assoc-at (bf ∙ transport-pre q g bg f) v w)
```

Changing the target of a projection also preserves its square. The
associator in `lift-base` is retained explicitly.

```agda
lift-base : {X Y B B′ : CAT} (σ : MAP B B′) (π : MAP Y B)
  (f : MAP X Y) {q : MAP X B} (bf : (π ∘ f) =₁ q)
  → ((σ ∘ π) ∘ f) =₁ (σ ∘ q)
lift-base σ π f bf = (σ ◁ bf) ∙ comp-assoc f π σ

abstract
  lift-square : {X Y B B′ : CAT} (σ : MAP B B′) (π : MAP Y B)
    {f g : MAP X Y} {q : MAP X B}
    (bf : (π ∘ f) =₁ q) (bg : (π ∘ g) =₁ q) (α : f =₁ g)
    → Square π bf bg α
    → Square (σ ∘ π) (lift-base σ π f bf) (lift-base σ π g bg) α
  lift-square σ π {f} {g} bf bg α compatible =
    isoComp-cong
      ((postWhisker σ ◁ compatible) ∙ (postWhisker-isoComp-at σ bg (π ◁ α)) ⁻¹)
      (idIso (comp-assoc f π σ)) ∙
    ((isoComp-assoc-at (σ ◁ bg) (σ ◁ (π ◁ α)) (comp-assoc f π σ)) ⁻¹ ∙
    (isoComp-cong (idIso (σ ◁ bg)) (postWhisker-comp-at α π σ) ∙
      isoComp-assoc-at (σ ◁ bg) (comp-assoc g π σ) ((σ ∘ π) ◁ α)))

  post-inverse : {X B B′ : CAT} (σ : MAP B B′)
    {u v : MAP X B} (α : u =₁ v)
    → (σ ◁ α ⁻¹) =₂ ((σ ◁ α) ⁻¹)
  post-inverse σ {u} α = cancel-right-reflect (σ ◁ α)
    ((isoComp-inverseˡ-at (σ ◁ α)) ⁻¹ ∙
    (postWhisker-idIso σ u ∙
    ((postWhisker σ ◁ isoComp-inverseˡ-at α) ∙
      (postWhisker-isoComp-at σ (α ⁻¹) α) ⁻¹)))

  lift-compose : {X Y Z B B′ : CAT} (σ : MAP B B′) (π : MAP Z B)
    (g : MAP Y Z) (f : MAP X Y) {q : MAP Y B} {r : MAP X B}
    (bg : (π ∘ g) =₁ q) (bf : (q ∘ f) =₁ r)
    →
        (compose-base (σ ∘ π) g (lift-base σ π g bg) f (lift-base σ q f bf)) =₂
        (lift-base σ π (g ∘ f) (compose-base π g bg f bf))
  lift-compose σ π g f {q} bg bf =
    let u = σ ◁ bf
        a = comp-assoc f q σ
        v = (σ ◁ bg) ▷ f
        b = comp-assoc g π σ ▷ f
        c = (comp-assoc f g (σ ∘ π)) ⁻¹
        d = σ ◁ (bg ▷ f)
        e = comp-assoc f (π ∘ g) σ
        t = σ ◁ (comp-assoc f g π) ⁻¹
        k = comp-assoc (g ∘ f) π σ
        p = σ ◁ comp-assoc f g π
        pentagon : (e ∙ (b ∙ c)) =₂ (t ∙ k)
        pentagon = isoComp-cong ((post-inverse σ (comp-assoc f g π)) ⁻¹) (idIso k) ∙
          ((move-square p (e ∙ b) k (comp-assoc f g (σ ∘ π))
            ((pentagon-whiskered f g π σ) ⁻¹)) ⁻¹ ∙
            (isoComp-assoc-at e b c) ⁻¹)
        middle : (a ∙ ((v ∙ b) ∙ c)) =₂ (d ∙ (t ∙ k))
        middle = isoComp-cong (idIso d) pentagon ∙
          (isoComp-assoc-at d e (b ∙ c) ∙
          (isoComp-cong (whisker-mixed-at bg f σ) (idIso (b ∙ c)) ∙
          ((isoComp-assoc-at a v (b ∙ c)) ⁻¹ ∙
            isoComp-cong (idIso a) (isoComp-assoc-at v b c))))
        merge : (u ∙ (d ∙ t)) =₂ (σ ◁ compose-base π g bg f bf)
        merge = (postWhisker-isoComp-at σ bf (transport-pre π g bg f)) ⁻¹ ∙
          isoComp-cong (idIso u)
            ((postWhisker-isoComp-at σ (bg ▷ f) ((comp-assoc f g π) ⁻¹)) ⁻¹)
    in isoComp-cong merge (idIso k) ∙
      ((isoComp-assoc-at u (d ∙ t) k) ⁻¹ ∙
      (isoComp-cong (idIso u) ((isoComp-assoc-at d t k) ⁻¹) ∙
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
  (bf : (p₁ ∘ f) =₁ p₀) (bg : (p₂ ∘ g) =₁ p₁)
  (bF : (q₁ ∘ F) =₁ q₀) (bG : (q₂ ∘ G) =₁ q₁)
  (bx₀ : (q₀ ∘ x₀) =₁ p₀) (bx₁ : (q₁ ∘ x₁) =₁ p₁)
  (bx₂ : (q₂ ∘ x₂) =₁ p₂)
  (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (β : (x₂ ∘ g) =₁ (G ∘ x₁)) where

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
      let e₁ = (comp-assoc f g x₂) ⁻¹
          e₂ = β ▷ f
          e₃ = comp-assoc f x₁ G
          e₄ = G ◁ α
          e₅ = (comp-assoc x₀ F G) ⁻¹
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
