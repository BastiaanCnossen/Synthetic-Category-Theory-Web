# Naturality of evaluation at an absolute point

The normalization comparisons used to encode a cone comparison must also
respect identifications of its legs. These lemmas keep that naturality
explicit, including the constant terms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.PointEvaluationNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-substitution)
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯

post-evaluation-natural : {X K Y Z : CAT} (F : MAP Y Z) (u : MAP K Y)
  {r s : MAP X K} (δ : r =₁ s) {x y : MAP X Y}
  (b : (u ∘ r) =₁ x) (b′ : (u ∘ s) =₁ y) (η : x =₁ y)
  → (b′ ∙ (u ◁ δ)) =₂ (η ∙ b)
  → (((F ◁ b′) ∙ comp-assoc s u F) ∙ ((F ∘ u) ◁ δ)) =₂
      ((F ◁ η) ∙ ((F ◁ b) ∙ comp-assoc r u F))
post-evaluation-natural F u {r} {s} δ b b′ η p =
  paste-squares (comp-assoc r u F) (comp-assoc s u F) (F ◁ b) (F ◁ b′)
    ((F ∘ u) ◁ δ) (F ◁ (u ◁ δ)) (F ◁ η)
    (postWhisker-comp-at δ u F) (post-square F b b′ (u ◁ δ) η p)

pair-evaluation-natural : {X K C D : CAT} (f : MAP K C) (g : MAP K D)
  {r s : MAP X K} (δ : r =₁ s)
  {x x′ : MAP X C} {y y′ : MAP X D}
  (b : (f ∘ r) =₁ x) (b′ : (f ∘ s) =₁ x′)
  (d : (g ∘ r) =₁ y) (d′ : (g ∘ s) =₁ y′)
  (α : x =₁ x′) (β : y =₁ y′)
  → (b′ ∙ (f ◁ δ)) =₂ (α ∙ b)
  → (d′ ∙ (g ◁ δ)) =₂ (β ∙ d)
  → ((pair-cong b′ d′ ∙ pair-pre f g s) ∙ (pair f g ◁ δ)) =₂
      (pair-cong α β ∙ (pair-cong b d ∙ pair-pre f g r))
pair-evaluation-natural {X} {K} {C} {D} f g {r} {s} δ b b′ d d′ α β p q =
  paste-squares (pair-pre f g r) (pair-pre f g s)
    (pair-cong b d) (pair-cong b′ d′)
    (pair f g ◁ δ) (pair-cong (f ◁ δ) (g ◁ δ)) (pair-cong α β)
    base
    (pair-square b b′ d d′ (f ◁ δ) α (g ◁ δ) β p q)
  where
  base : (pair-pre f g s ∙ (pair f g ◁ δ)) =₂
    (pair-cong (f ◁ δ) (g ◁ δ) ∙ pair-pre f g r)
  base = (pair-pre-natural-substitution f g δ) ⁻¹

terminal-comparison : {X : CAT} {f g : MAP X One}
  (α β : f =₁ g) → α =₂ β
terminal-comparison {f = f} {g} α β =
  equiv-reflect (terminalIso-isEquiv f g) α β (terminal-iso _ _)

const-evaluate-natural : {X C : CAT} (x : Obj-abs C)
  {r s : Obj-abs X} (δ : r =₁ s)
  → (const-evaluate x s ∙ (const x ◁ δ)) =₂
      (idIso x ∙ const-evaluate x r)
const-evaluate-natural {X} x {r} {s} δ =
  paste-squares
    ((x ◁ b) ∙ comp-assoc r (terminate X) x)
    ((x ◁ b′) ∙ comp-assoc s (terminate X) x)
    (const-One x) (const-One x)
    (const x ◁ δ) (x ◁ idIso (terminate One)) (idIso x)
    (post-evaluation-natural x (terminate X) δ b b′ (idIso (terminate One))
      (terminal-comparison _ _))
    ((isoComp-unitˡ-at (const-One x)) ⁻¹ ∙
      (isoComp-unitʳ-at (const-One x) ∙
        isoComp-cong (idIso (const-One x)) (postWhisker-idIso x (terminate One))))
  where
  b = terminal-iso (terminate X ∘ r) (terminate One)
  b′ = terminal-iso (terminate X ∘ s) (terminate One)

identity-square : {X C : CAT} {x y : MAP X C} (δ : x =₁ y)
  → (idIso y ∙ δ) =₂ (δ ∙ idIso x)
identity-square δ = (isoComp-unitʳ-at δ) ⁻¹ ∙ isoComp-unitˡ-at δ

isoComp-evaluate-natural : {X K C D : CAT} {f g h : MAP C D}
  (β : MAP K (g ＝ h)) (α : MAP K (f ＝ g))
  {r s : MAP X K} (δ : r =₁ s)
  {x x′ : MAP X (g ＝ h)} {y y′ : MAP X (f ＝ g)}
  (b : (β ∘ r) =₁ x) (b′ : (β ∘ s) =₁ x′)
  (d : (α ∘ r) =₁ y) (d′ : (α ∘ s) =₁ y′)
  (ξ : x =₁ x′) (η : y =₁ y′)
  → (b′ ∙ (β ◁ δ)) =₂ (ξ ∙ b)
  → (d′ ∙ (α ◁ δ)) =₂ (η ∙ d)
  → (isoComp-evaluate β α s b′ d′ ∙ ((β ∙ α) ◁ δ)) =₂
      (isoComp-cong ξ η ∙ isoComp-evaluate β α r b d)
isoComp-evaluate-natural β α {r} {s} δ b b′ d d′ ξ η p q =
  isoComp-cong (idIso (isoComp-cong ξ η)) (normalize r b d) ∙
  (post-evaluation-natural isoComp (pair β α) δ n n′ (pair-cong ξ η)
    (pair-evaluation-natural β α δ b b′ d d′ ξ η p q) ∙
    isoComp-cong ((normalize s b′ d′) ⁻¹) (idIso ((β ∙ α) ◁ δ)))
  where
  n = pair-cong b d ∙ pair-pre β α r
  n′ = pair-cong b′ d′ ∙ pair-pre β α s
  normalize : ∀ t {u v} (e : (β ∘ t) =₁ u) (k : (α ∘ t) =₁ v)
    → ((isoComp ◁ (pair-cong e k ∙ pair-pre β α t)) ∙ comp-assoc t (pair β α) isoComp) =₂
        (isoComp-evaluate β α t e k)
  normalize t e k = isoComp-assoc-at (isoComp ◁ pair-cong e k)
      (isoComp ◁ pair-pre β α t) (comp-assoc t (pair β α) isoComp) ∙
    isoComp-cong (postWhisker-isoComp-at isoComp (pair-cong e k) (pair-pre β α t))
      (idIso (comp-assoc t (pair β α) isoComp))

left-evaluation : {K C D : CAT} {f g h : MAP C D}
  (τ : g =₁ h) (F : MAP K (f ＝ g)) (r : Obj-abs K)
  → ((const τ ∙ F) ∘ r) =₁ (τ ∙ (F ∘ r))
left-evaluation τ F r = isoComp-evaluate (const τ) F r (const-evaluate τ r) (idIso (F ∘ r))

left-evaluation-natural : {K C D : CAT} {f g h : MAP C D}
  (τ : g =₁ h) (F : MAP K (f ＝ g)) {r s : Obj-abs K} (δ : r =₁ s)
  → (left-evaluation τ F s ∙ ((const τ ∙ F) ◁ δ)) =₂
      (isoComp-cong (idIso τ) (F ◁ δ) ∙ left-evaluation τ F r)
left-evaluation-natural τ F {r} {s} δ = isoComp-evaluate-natural (const τ) F δ
  (const-evaluate τ r) (const-evaluate τ s) (idIso (F ∘ r)) (idIso (F ∘ s))
  (idIso τ) (F ◁ δ) (const-evaluate-natural τ δ) (identity-square (F ◁ δ))

right-evaluation : {K C D : CAT} {f g h : MAP C D}
  (F : MAP K (g ＝ h)) (τ : f =₁ g) (r : Obj-abs K)
  → ((F ∙ const τ) ∘ r) =₁ ((F ∘ r) ∙ τ)
right-evaluation F τ r = isoComp-evaluate F (const τ) r (idIso (F ∘ r)) (const-evaluate τ r)

right-evaluation-natural : {K C D : CAT} {f g h : MAP C D}
  (F : MAP K (g ＝ h)) (τ : f =₁ g) {r s : Obj-abs K} (δ : r =₁ s)
  → (right-evaluation F τ s ∙ ((F ∙ const τ) ◁ δ)) =₂
      (isoComp-cong (F ◁ δ) (idIso τ) ∙ right-evaluation F τ r)
right-evaluation-natural F τ {r} {s} δ = isoComp-evaluate-natural F (const τ) δ
  (idIso (F ∘ r)) (idIso (F ∘ s)) (const-evaluate τ r) (const-evaluate τ s)
  (F ◁ δ) (idIso τ) (identity-square (F ◁ δ)) (const-evaluate-natural τ δ)
```
