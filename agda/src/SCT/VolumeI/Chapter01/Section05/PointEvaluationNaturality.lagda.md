# Naturality of evaluation at an absolute point

The normalization comparisons used to encode a cone comparison must also
respect identifications of its legs. These lemmas keep that naturality
explicit, including the constant terms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.PointEvaluationNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-substitution)
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯

post-evaluation-natural : {X K Y Z : CAT} (F : MAP Y Z) (u : MAP K Y)
  {r s : MAP X K} (δ : NatIso r s) {x y : MAP X Y}
  (b : NatIso (u ∘ r) x) (b′ : NatIso (u ∘ s) y) (η : NatIso x y)
  → Iso₂ (b′ ∙ (u ◁ δ)) (η ∙ b)
  → Iso₂ (((F ◁ b′) ∙ comp-assoc s u F) ∙ ((F ∘ u) ◁ δ))
      ((F ◁ η) ∙ ((F ◁ b) ∙ comp-assoc r u F))
post-evaluation-natural F u {r} {s} δ b b′ η p =
  paste-squares (comp-assoc r u F) (comp-assoc s u F) (F ◁ b) (F ◁ b′)
    ((F ∘ u) ◁ δ) (F ◁ (u ◁ δ)) (F ◁ η)
    (postWhisker-comp-at δ u F) (post-square F b b′ (u ◁ δ) η p)

pair-evaluation-natural : {X K C D : CAT} (f : MAP K C) (g : MAP K D)
  {r s : MAP X K} (δ : NatIso r s)
  {x x′ : MAP X C} {y y′ : MAP X D}
  (b : NatIso (f ∘ r) x) (b′ : NatIso (f ∘ s) x′)
  (d : NatIso (g ∘ r) y) (d′ : NatIso (g ∘ s) y′)
  (α : NatIso x x′) (β : NatIso y y′)
  → Iso₂ (b′ ∙ (f ◁ δ)) (α ∙ b)
  → Iso₂ (d′ ∙ (g ◁ δ)) (β ∙ d)
  → Iso₂ ((pair-cong b′ d′ ∙ pair-pre f g s) ∙ (pair f g ◁ δ))
      (pair-cong α β ∙ (pair-cong b d ∙ pair-pre f g r))
pair-evaluation-natural {X} {K} {C} {D} f g {r} {s} δ b b′ d d′ α β p q =
  paste-squares (pair-pre f g r) (pair-pre f g s)
    (pair-cong b d) (pair-cong b′ d′)
    (pair f g ◁ δ) (pair-cong (f ◁ δ) (g ◁ δ)) (pair-cong α β)
    base
    (pair-square b b′ d d′ (f ◁ δ) α (g ◁ δ) β p q)
  where
  base : Iso₂ (pair-pre f g s ∙ (pair f g ◁ δ))
    (pair-cong (f ◁ δ) (g ◁ δ) ∙ pair-pre f g r)
  base = invIso (pair-pre-natural-substitution f g δ)

terminal-comparison : {X : CAT} {f g : MAP X One}
  (α β : NatIso f g) → Iso₂ α β
terminal-comparison {f = f} {g} α β =
  equiv-reflect (terminalIso-isEquiv f g) α β (terminal-iso _ _)

const-evaluate-natural : {X C : CAT} (x : ObjAbs C)
  {r s : ObjAbs X} (δ : NatIso r s)
  → Iso₂ (const-evaluate x s ∙ (const x ◁ δ))
      (idIso x ∙ const-evaluate x r)
const-evaluate-natural {X} x {r} {s} δ =
  paste-squares
    ((x ◁ b) ∙ comp-assoc r (terminate X) x)
    ((x ◁ b′) ∙ comp-assoc s (terminate X) x)
    (const-One x) (const-One x)
    (const x ◁ δ) (x ◁ idIso (terminate One)) (idIso x)
    (post-evaluation-natural x (terminate X) δ b b′ (idIso (terminate One))
      (terminal-comparison _ _))
    (invIso (isoComp-unitˡ-at (const-One x)) ∙
      (isoComp-unitʳ-at (const-One x) ∙
        isoComp-cong (idIso (const-One x)) (postWhisker-idIso x (terminate One))))
  where
  b = terminal-iso (terminate X ∘ r) (terminate One)
  b′ = terminal-iso (terminate X ∘ s) (terminate One)

identity-square : {X C : CAT} {x y : MAP X C} (δ : NatIso x y)
  → Iso₂ (idIso y ∙ δ) (δ ∙ idIso x)
identity-square δ = invIso (isoComp-unitʳ-at δ) ∙ isoComp-unitˡ-at δ

isoComp-evaluate-natural : {X K C D : CAT} {f g h : MAP C D}
  (β : MAP K (g ≅ h)) (α : MAP K (f ≅ g))
  {r s : MAP X K} (δ : NatIso r s)
  {x x′ : MAP X (g ≅ h)} {y y′ : MAP X (f ≅ g)}
  (b : NatIso (β ∘ r) x) (b′ : NatIso (β ∘ s) x′)
  (d : NatIso (α ∘ r) y) (d′ : NatIso (α ∘ s) y′)
  (ξ : NatIso x x′) (η : NatIso y y′)
  → Iso₂ (b′ ∙ (β ◁ δ)) (ξ ∙ b)
  → Iso₂ (d′ ∙ (α ◁ δ)) (η ∙ d)
  → Iso₂ (isoComp-evaluate β α s b′ d′ ∙ ((β ∙ α) ◁ δ))
      (isoComp-cong ξ η ∙ isoComp-evaluate β α r b d)
isoComp-evaluate-natural β α {r} {s} δ b b′ d d′ ξ η p q =
  isoComp-cong (idIso (isoComp-cong ξ η)) (normalize r b d) ∙
  (post-evaluation-natural isoComp (pair β α) δ n n′ (pair-cong ξ η)
    (pair-evaluation-natural β α δ b b′ d d′ ξ η p q) ∙
    isoComp-cong (invIso (normalize s b′ d′)) (idIso ((β ∙ α) ◁ δ)))
  where
  n = pair-cong b d ∙ pair-pre β α r
  n′ = pair-cong b′ d′ ∙ pair-pre β α s
  normalize : ∀ t {u v} (e : NatIso (β ∘ t) u) (k : NatIso (α ∘ t) v)
    → Iso₂ ((isoComp ◁ (pair-cong e k ∙ pair-pre β α t)) ∙ comp-assoc t (pair β α) isoComp)
        (isoComp-evaluate β α t e k)
  normalize t e k = isoComp-assoc-at (isoComp ◁ pair-cong e k)
      (isoComp ◁ pair-pre β α t) (comp-assoc t (pair β α) isoComp) ∙
    isoComp-cong (postWhisker-isoComp-at isoComp (pair-cong e k) (pair-pre β α t))
      (idIso (comp-assoc t (pair β α) isoComp))

left-evaluation : {K C D : CAT} {f g h : MAP C D}
  (τ : NatIso g h) (F : MAP K (f ≅ g)) (r : ObjAbs K)
  → NatIso ((const τ ∙ F) ∘ r) (τ ∙ (F ∘ r))
left-evaluation τ F r = isoComp-evaluate (const τ) F r (const-evaluate τ r) (idIso (F ∘ r))

left-evaluation-natural : {K C D : CAT} {f g h : MAP C D}
  (τ : NatIso g h) (F : MAP K (f ≅ g)) {r s : ObjAbs K} (δ : NatIso r s)
  → Iso₂ (left-evaluation τ F s ∙ ((const τ ∙ F) ◁ δ))
      (isoComp-cong (idIso τ) (F ◁ δ) ∙ left-evaluation τ F r)
left-evaluation-natural τ F {r} {s} δ = isoComp-evaluate-natural (const τ) F δ
  (const-evaluate τ r) (const-evaluate τ s) (idIso (F ∘ r)) (idIso (F ∘ s))
  (idIso τ) (F ◁ δ) (const-evaluate-natural τ δ) (identity-square (F ◁ δ))

right-evaluation : {K C D : CAT} {f g h : MAP C D}
  (F : MAP K (g ≅ h)) (τ : NatIso f g) (r : ObjAbs K)
  → NatIso ((F ∙ const τ) ∘ r) ((F ∘ r) ∙ τ)
right-evaluation F τ r = isoComp-evaluate F (const τ) r (idIso (F ∘ r)) (const-evaluate τ r)

right-evaluation-natural : {K C D : CAT} {f g h : MAP C D}
  (F : MAP K (g ≅ h)) (τ : NatIso f g) {r s : ObjAbs K} (δ : NatIso r s)
  → Iso₂ (right-evaluation F τ s ∙ ((F ∙ const τ) ◁ δ))
      (isoComp-cong (F ◁ δ) (idIso τ) ∙ right-evaluation F τ r)
right-evaluation-natural F τ {r} {s} δ = isoComp-evaluate-natural F (const τ) δ
  (idIso (F ∘ r)) (idIso (F ∘ s)) (const-evaluate τ r) (const-evaluate τ s)
  (F ◁ δ) (idIso τ) (identity-square (F ◁ δ)) (const-evaluate-natural τ δ)
```
