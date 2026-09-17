# Naturality of evaluation and composition

The comparison between uncurrying a composite and composing evaluations
has a prescribed action on isomorphisms. We construct its naturality square
by pasting the squares for pairing and the specified beta comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.CompositionNaturality
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-cong-comp; pair-cong-triangle₁; pair-cong-triangle₂)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution; move-square)
open Structural vocabulary terminal products productLaws composition whiskering

post-square : {X Y Z : CAT} (F : MAP Y Z)
  {a a′ b b′ : MAP X Y}
  (u : NatIso a b) (u′ : NatIso a′ b′)
  (α : NatIso a a′) (β : NatIso b b′)
  → Iso₂ (u′ ∙ α) (β ∙ u)
  → Iso₂ ((F ◁ u′) ∙ (F ◁ α)) ((F ◁ β) ∙ (F ◁ u))
post-square F u u′ α β p = postWhisker-isoComp-at F β u ∙
  ((postWhisker F ◁ p) ∙ invIso (postWhisker-isoComp-at F u′ α))

identity-square : {X Y : CAT} {f g : MAP X Y} (α : NatIso f g)
  → Iso₂ (idIso g ∙ α) (α ∙ idIso f)
identity-square α = invIso (isoComp-unitʳ-at α) ∙ isoComp-unitˡ-at α

apply-square : {X C D : CAT}
  {f f′ g g′ : MAP X (Map C D)} {x x′ y y′ : MAP X C}
  (u : NatIso f g) (u′ : NatIso f′ g′)
  (v : NatIso x y) (v′ : NatIso x′ y′)
  (α : NatIso f f′) (β : NatIso g g′)
  (γ : NatIso x x′) (δ : NatIso y y′)
  → Iso₂ (u′ ∙ α) (β ∙ u) → Iso₂ (v′ ∙ γ) (δ ∙ v)
  → Iso₂ (applyTerm-cong u′ v′ ∙ applyTerm-cong α γ)
      (applyTerm-cong β δ ∙ applyTerm-cong u v)
apply-square u u′ v v′ α β γ δ p q =
  post-square mapEval (pair-cong u v) (pair-cong u′ v′)
    (pair-cong α γ) (pair-cong β δ) (pair-square u u′ v v′ α β γ δ p q)

apply-cong-Iso₂ : {X C D : CAT}
  {f f′ : MAP X (Map C D)} {x x′ : MAP X C}
  {α α′ : NatIso f f′} {β β′ : NatIso x x′}
  → Iso₂ α α′ → Iso₂ β β′
  → Iso₂ (applyTerm-cong α β) (applyTerm-cong α′ β′)
apply-cong-Iso₂ p q = postWhisker mapEval ◁ pair-cong-Iso₂ p q

binary-pre-inputs : {X Y A B C : CAT} (F : MAP (A × B) C)
  {f f′ : MAP X A} {g g′ : MAP X B}
  (α : NatIso f f′) (β : NatIso g g′) (r : MAP Y X)
  → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
        after = (F ◁ pair-pre f′ g′ r) ∙ comp-assoc r (pair f′ g′) F
    in Iso₂ (after ∙ ((F ◁ pair-cong α β) ▷ r))
        ((F ◁ pair-cong (α ▷ r) (β ▷ r)) ∙ before)
binary-pre-inputs F {f} {f′} {g} {g′} α β r =
  paste-squares (comp-assoc r (pair f g) F) (comp-assoc r (pair f′ g′) F)
    (F ◁ pair-pre f g r) (F ◁ pair-pre f′ g′ r)
    ((F ◁ pair-cong α β) ▷ r) (F ◁ (pair-cong α β ▷ r))
    (F ◁ pair-cong (α ▷ r) (β ▷ r))
    (whisker-mixed-at (pair-cong α β) r F)
    (post-square F (pair-pre f g r) (pair-pre f′ g′ r)
      (pair-cong α β ▷ r) (pair-cong (α ▷ r) (β ▷ r))
      (invIso (pair-pre-natural-inputs α β r)))

binary-pre-substitution : {X Y A B C : CAT} (F : MAP (A × B) C)
  (f : MAP X A) (g : MAP X B) {r s : MAP Y X} (γ : NatIso r s)
  → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
        after = (F ◁ pair-pre f g s) ∙ comp-assoc s (pair f g) F
    in Iso₂ (after ∙ ((F ∘ pair f g) ◁ γ))
        ((F ◁ pair-cong (f ◁ γ) (g ◁ γ)) ∙ before)
binary-pre-substitution F f g {r} {s} γ =
  paste-squares (comp-assoc r (pair f g) F) (comp-assoc s (pair f g) F)
    (F ◁ pair-pre f g r) (F ◁ pair-pre f g s)
    ((F ∘ pair f g) ◁ γ) (F ◁ (pair f g ◁ γ))
    (F ◁ pair-cong (f ◁ γ) (g ◁ γ))
    (postWhisker-comp-at γ (pair f g) F)
    (post-square F (pair-pre f g r) (pair-pre f g s)
      (pair f g ◁ γ) (pair-cong (f ◁ γ) (g ◁ γ))
      (invIso (pair-pre-natural-substitution f g γ)))

coordinate-at : {X K A B : CAT} (F : MAP A B) (π : MAP K A)
  (t : MAP X K) {p : MAP X A} → NatIso (π ∘ t) p
  → NatIso ((F ∘ π) ∘ t) (F ∘ p)
coordinate-at F π t b = (F ◁ b) ∙ comp-assoc t π F

coordinate-at-outer : {X K A B : CAT} {F G : MAP A B}
  (α : NatIso F G) (π : MAP K A) (t : MAP X K)
  {p : MAP X A} (b : NatIso (π ∘ t) p)
  → Iso₂ (coordinate-at G π t b ∙ ((α ▷ π) ▷ t))
      ((α ▷ p) ∙ coordinate-at F π t b)
coordinate-at-outer {F = F} {G} α π t {p} b =
  paste-squares (comp-assoc t π F) (comp-assoc t π G) (F ◁ b) (G ◁ b)
    ((α ▷ π) ▷ t) (α ▷ (π ∘ t)) (α ▷ p)
    (preWhisker-comp-at α π t) (invIso (interchange-at α b))

coordinate-at-inner : {X K A B : CAT} (F : MAP A B) (π : MAP K A)
  {t t′ : MAP X K} {p p′ : MAP X A}
  (b : NatIso (π ∘ t) p) (b′ : NatIso (π ∘ t′) p′)
  (δ : NatIso t t′) (α : NatIso p p′)
  → Iso₂ (b′ ∙ (π ◁ δ)) (α ∙ b)
  → Iso₂ (coordinate-at F π t′ b′ ∙ ((F ∘ π) ◁ δ))
      ((F ◁ α) ∙ coordinate-at F π t b)
coordinate-at-inner F π {t} {t′} b b′ δ α p =
  paste-squares (comp-assoc t π F) (comp-assoc t′ π F) (F ◁ b) (F ◁ b′)
    ((F ∘ π) ◁ δ) (F ◁ (π ◁ δ)) (F ◁ α)
    (postWhisker-comp-at δ π F) (post-square F b b′ (π ◁ δ) α p)

productMap-pair-outer : {X A B C D : CAT}
  {f f′ : MAP A B} {g g′ : MAP C D}
  (α : NatIso f f′) (β : NatIso g g′) (p : MAP X A) (q : MAP X C)
  → Iso₂ (productMap-pair f′ g′ p q ∙ (productMap-cong α β ▷ pair p q))
      (pair-cong (α ▷ p) (β ▷ q) ∙ productMap-pair f g p q)
productMap-pair-outer {f = f} {f′} {g} {g′} α β p q =
  let t = pair p q
      b = pair-β₁ p q
      d = pair-β₂ p q
      left = coordinate-at f pr₁ t b
      left′ = coordinate-at f′ pr₁ t b
      right = coordinate-at g pr₂ t d
      right′ = coordinate-at g′ pr₂ t d
  in paste-squares (pair-pre (f ∘ pr₁) (g ∘ pr₂) t)
    (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) t)
    (pair-cong left right) (pair-cong left′ right′)
    (productMap-cong α β ▷ t) (pair-cong ((α ▷ pr₁) ▷ t) ((β ▷ pr₂) ▷ t))
    (pair-cong (α ▷ p) (β ▷ q))
    (invIso (pair-pre-natural-inputs (α ▷ pr₁) (β ▷ pr₂) t))
    (pair-square left left′ right right′ ((α ▷ pr₁) ▷ t) (α ▷ p)
      ((β ▷ pr₂) ▷ t) (β ▷ q)
      (coordinate-at-outer α pr₁ t b) (coordinate-at-outer β pr₂ t d))

productMap-pair-inner : {X A B C D : CAT} (f : MAP A B) (g : MAP C D)
  {p p′ : MAP X A} {q q′ : MAP X C} (σ : NatIso p p′) (τ : NatIso q q′)
  → Iso₂ (productMap-pair f g p′ q′ ∙ (productMap f g ◁ pair-cong σ τ))
      (pair-cong (f ◁ σ) (g ◁ τ) ∙ productMap-pair f g p q)
productMap-pair-inner f g {p} {p′} {q} {q′} σ τ =
  let t = pair p q
      t′ = pair p′ q′
      δ = pair-cong σ τ
      left = coordinate-at f pr₁ t (pair-β₁ p q)
      left′ = coordinate-at f pr₁ t′ (pair-β₁ p′ q′)
      right = coordinate-at g pr₂ t (pair-β₂ p q)
      right′ = coordinate-at g pr₂ t′ (pair-β₂ p′ q′)
  in paste-squares (pair-pre (f ∘ pr₁) (g ∘ pr₂) t)
    (pair-pre (f ∘ pr₁) (g ∘ pr₂) t′)
    (pair-cong left right) (pair-cong left′ right′)
    (productMap f g ◁ δ) (pair-cong ((f ∘ pr₁) ◁ δ) ((g ∘ pr₂) ◁ δ))
    (pair-cong (f ◁ σ) (g ◁ τ))
    (invIso (pair-pre-natural-substitution (f ∘ pr₁) (g ∘ pr₂) δ))
    (pair-square left left′ right right′ ((f ∘ pr₁) ◁ δ) (f ◁ σ)
      ((g ∘ pr₂) ◁ δ) (g ◁ τ)
      (coordinate-at-inner f pr₁ (pair-β₁ p q) (pair-β₁ p′ q′) δ σ
        (pair-cong-triangle₁ σ τ))
      (coordinate-at-inner g pr₂ (pair-β₂ p q) (pair-β₂ p′ q′) δ τ
        (pair-cong-triangle₂ σ τ)))

unit-input-square : {X C : CAT} (x : MAP X C)
  → Iso₂ (comp-unitˡ x ∙ (idIso (id C) ▷ x)) (idIso x ∙ comp-unitˡ x)
unit-input-square {C = C} x = invIso (isoComp-unitˡ-at (comp-unitˡ x)) ∙
  (isoComp-unitʳ-at (comp-unitˡ x) ∙
    isoComp-cong (idIso (comp-unitˡ x)) (preWhisker-idIso (id C) x))

mapUncurry-at-outer : {Γ X C D : CAT} {f g : MAP X (Map C D)}
  (α : NatIso f g) (p : MAP Γ X) (x : MAP Γ C)
  → Iso₂ (mapUncurry-at g p x ∙ (mapUncurry-cong α ▷ pair p x))
      (applyTerm-cong (α ▷ p) (idIso x) ∙ mapUncurry-at f p x)
mapUncurry-at-outer {C = C} {f = f} {g} α p x =
  let input = productMap-cong α (idIso (id C))
      middle = pair-cong (α ▷ p) (idIso (id C) ▷ x)
      output = pair-cong (α ▷ p) (idIso x)
      normalize = pair-cong (idIso (f ∘ p)) (comp-unitˡ x)
      normalize′ = pair-cong (idIso (g ∘ p)) (comp-unitˡ x)
      square = paste-squares (productMap-pair f (id C) p x)
        (productMap-pair g (id C) p x) normalize normalize′
        (input ▷ pair p x) middle output
        (productMap-pair-outer α (idIso (id C)) p x)
        (pair-square (idIso (f ∘ p)) (idIso (g ∘ p)) (comp-unitˡ x) (comp-unitˡ x)
          (α ▷ p) (α ▷ p) (idIso (id C) ▷ x) (idIso x)
          (identity-square (α ▷ p)) (unit-input-square x))
  in paste-squares (comp-assoc (pair p x) (productMap f (id C)) mapEval)
    (comp-assoc (pair p x) (productMap g (id C)) mapEval)
    (mapEval ◁ (normalize ∙ productMap-pair f (id C) p x))
    (mapEval ◁ (normalize′ ∙ productMap-pair g (id C) p x))
    (mapUncurry-cong α ▷ pair p x) (mapEval ◁ (input ▷ pair p x))
    (mapEval ◁ output) (whisker-mixed-at input (pair p x) mapEval)
    (post-square mapEval (normalize ∙ productMap-pair f (id C) p x)
      (normalize′ ∙ productMap-pair g (id C) p x) (input ▷ pair p x) output square)

mapUncurry-at-inner : {Γ X C D : CAT} (f : MAP X (Map C D))
  {p p′ : MAP Γ X} {x x′ : MAP Γ C} (σ : NatIso p p′) (τ : NatIso x x′)
  → Iso₂ (mapUncurry-at f p′ x′ ∙ (mapUncurry f ◁ pair-cong σ τ))
      (applyTerm-cong (f ◁ σ) τ ∙ mapUncurry-at f p x)
mapUncurry-at-inner {C = C} f {p} {p′} {x} {x′} σ τ =
  let input = pair-cong σ τ
      middle = pair-cong (f ◁ σ) (id C ◁ τ)
      output = pair-cong (f ◁ σ) τ
      normalize = pair-cong (idIso (f ∘ p)) (comp-unitˡ x)
      normalize′ = pair-cong (idIso (f ∘ p′)) (comp-unitˡ x′)
      square = paste-squares (productMap-pair f (id C) p x)
        (productMap-pair f (id C) p′ x′) normalize normalize′
        (productMap f (id C) ◁ input) middle output
        (productMap-pair-inner f (id C) σ τ)
        (pair-square (idIso (f ∘ p)) (idIso (f ∘ p′)) (comp-unitˡ x) (comp-unitˡ x′)
          (f ◁ σ) (f ◁ σ) (id C ◁ τ) τ
          (identity-square (f ◁ σ)) (postWhisker-id-at τ))
  in paste-squares (comp-assoc (pair p x) (productMap f (id C)) mapEval)
    (comp-assoc (pair p′ x′) (productMap f (id C)) mapEval)
    (mapEval ◁ (normalize ∙ productMap-pair f (id C) p x))
    (mapEval ◁ (normalize′ ∙ productMap-pair f (id C) p′ x′))
    (mapUncurry f ◁ input) (mapEval ◁ (productMap f (id C) ◁ input))
    (mapEval ◁ output) (postWhisker-comp-at input (productMap f (id C)) mapEval)
    (post-square mapEval (normalize ∙ productMap-pair f (id C) p x)
      (normalize′ ∙ productMap-pair f (id C) p′ x′) (productMap f (id C) ◁ input) output square)

mapUncurry-as-apply-natural : {X C D : CAT} {f g : MAP X (Map C D)}
  (α : NatIso f g)
  → Iso₂ (mapUncurry-as-apply g ∙ mapUncurry-cong α)
      (applyTerm-cong (α ▷ pr₁) (idIso pr₂) ∙ mapUncurry-as-apply f)
mapUncurry-as-apply-natural {f = f} {g} α =
  post-square mapEval (pair-cong (idIso (f ∘ pr₁)) (comp-unitˡ pr₂))
    (pair-cong (idIso (g ∘ pr₁)) (comp-unitˡ pr₂))
    (pair-cong (α ▷ pr₁) (idIso (id _) ▷ pr₂)) (pair-cong (α ▷ pr₁) (idIso pr₂))
    (pair-square (idIso (f ∘ pr₁)) (idIso (g ∘ pr₁)) (comp-unitˡ pr₂) (comp-unitˡ pr₂)
      (α ▷ pr₁) (α ▷ pr₁) (idIso (id _) ▷ pr₂) (idIso pr₂)
      (identity-square (α ▷ pr₁)) (unit-input-square pr₂))

apply-compose-natural : {Γ C D E : CAT}
  {g g′ : MAP Γ (Map D E)} {f f′ : MAP Γ (Map C D)} {x x′ : MAP Γ C}
  (α : NatIso g g′) (β : NatIso f f′) (τ : NatIso x x′)
  → Iso₂ (apply-compose g′ f′ x′ ∙ applyTerm-cong (composeTerm-cong α β) τ)
      (applyTerm-cong α (applyTerm-cong β τ) ∙ apply-compose g f x)
apply-compose-natural {g = g} {g′} {f} {f′} {x} {x′} α β τ =
  let point = pair (pair g f) x
      point′ = pair (pair g′ f′) x′
      changed = pair-cong (pair-cong α β) τ
      first = pair-β₁ g f ∙ coordinate-at pr₁ pr₁ point (pair-β₁ (pair g f) x)
      first′ = pair-β₁ g′ f′ ∙ coordinate-at pr₁ pr₁ point′ (pair-β₁ (pair g′ f′) x′)
      second = pair-β₂ g f ∙ coordinate-at pr₂ pr₁ point (pair-β₁ (pair g f) x)
      second′ = pair-β₂ g′ f′ ∙ coordinate-at pr₂ pr₁ point′ (pair-β₁ (pair g′ f′) x′)
      third = pair-β₂ (pair g f) x
      third′ = pair-β₂ (pair g′ f′) x′
      first-square = paste-squares
        (coordinate-at pr₁ pr₁ point (pair-β₁ (pair g f) x))
        (coordinate-at pr₁ pr₁ point′ (pair-β₁ (pair g′ f′) x′))
        (pair-β₁ g f) (pair-β₁ g′ f′)
        ((pr₁ ∘ pr₁) ◁ changed) (pr₁ ◁ pair-cong α β) α
        (coordinate-at-inner pr₁ pr₁ (pair-β₁ (pair g f) x)
          (pair-β₁ (pair g′ f′) x′) changed (pair-cong α β)
          (pair-cong-triangle₁ (pair-cong α β) τ))
        (pair-cong-triangle₁ α β)
      second-square = paste-squares
        (coordinate-at pr₂ pr₁ point (pair-β₁ (pair g f) x))
        (coordinate-at pr₂ pr₁ point′ (pair-β₁ (pair g′ f′) x′))
        (pair-β₂ g f) (pair-β₂ g′ f′)
        ((pr₂ ∘ pr₁) ◁ changed) (pr₂ ◁ pair-cong α β) β
        (coordinate-at-inner pr₂ pr₁ (pair-β₁ (pair g f) x)
          (pair-β₁ (pair g′ f′) x′) changed (pair-cong α β)
          (pair-cong-triangle₁ (pair-cong α β) τ))
        (pair-cong-triangle₂ α β)
      inner = applyTerm-cong second third ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point
      inner′ = applyTerm-cong second′ third′ ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point′
      inner-square = paste-squares
        (applyTerm-pre (pr₂ ∘ pr₁) pr₂ point) (applyTerm-pre (pr₂ ∘ pr₁) pr₂ point′)
        (applyTerm-cong second third) (applyTerm-cong second′ third′)
        (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed)
        (applyTerm-cong ((pr₂ ∘ pr₁) ◁ changed) (pr₂ ◁ changed))
        (applyTerm-cong β τ)
        (binary-pre-substitution mapEval (pr₂ ∘ pr₁) pr₂ changed)
        (apply-square second second′ third third′ ((pr₂ ∘ pr₁) ◁ changed) β
          (pr₂ ◁ changed) τ second-square (pair-cong-triangle₂ (pair-cong α β) τ))
      outer = applyTerm-cong first inner ∙
        applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point
      outer′ = applyTerm-cong first′ inner′ ∙
        applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point′
      outer-square = paste-squares
        (applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point)
        (applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point′)
        (applyTerm-cong first inner) (applyTerm-cong first′ inner′)
        (doubleEvaluation ◁ changed)
        (applyTerm-cong ((pr₁ ∘ pr₁) ◁ changed) (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed))
        (applyTerm-cong α (applyTerm-cong β τ))
        (binary-pre-substitution mapEval (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) changed)
        (apply-square first first′ inner inner′ ((pr₁ ∘ pr₁) ◁ changed) α
          (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed) (applyTerm-cong β τ)
          first-square inner-square)
      before = mapUncurry-at mapComp (pair g f) x
      after = mapUncurry-at mapComp (pair g′ f′) x′
      initial = applyTerm-cong (composeTerm-cong α β) τ
      middle = mapUncurry mapComp ◁ changed
      start-square = move-square after middle initial before
        (mapUncurry-at-inner mapComp (pair-cong α β) τ)
      beta-square = paste-squares (invIso before) (invIso after)
        (mapComp-β ▷ point) (mapComp-β ▷ point′)
        initial middle (doubleEvaluation ◁ changed)
        start-square (interchange-at mapComp-β changed)
  in paste-squares ((mapComp-β ▷ point) ∙ invIso before)
    ((mapComp-β ▷ point′) ∙ invIso after) outer outer′ initial
    (doubleEvaluation ◁ changed) (applyTerm-cong α (applyTerm-cong β τ))
    beta-square outer-square

apply-cong-comp : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C}
  (α₂ : NatIso f₁ f₂) (α₁ : NatIso f₀ f₁)
  (β₂ : NatIso x₁ x₂) (β₁ : NatIso x₀ x₁)
  → Iso₂ (applyTerm-cong (α₂ ∙ α₁) (β₂ ∙ β₁))
      (applyTerm-cong α₂ β₂ ∙ applyTerm-cong α₁ β₁)
apply-cong-comp α₂ α₁ β₂ β₁ =
  postWhisker-isoComp-at mapEval (pair-cong α₂ β₂) (pair-cong α₁ β₁) ∙
    (postWhisker mapEval ◁ pair-cong-comp α₂ α₁ β₂ β₁)

chain-input-squares : {X Y : CAT} {a b c d e f : MAP X Y}
  (u : NatIso a d) (v : NatIso b e) (w : NatIso c f)
  (α : NatIso a b) (β : NatIso b c)
  (γ : NatIso d e) (δ : NatIso e f)
  → Iso₂ (v ∙ α) (γ ∙ u) → Iso₂ (w ∙ β) (δ ∙ v)
  → Iso₂ (w ∙ (β ∙ α)) ((δ ∙ γ) ∙ u)
chain-input-squares u v w α β γ δ p q =
  invIso (isoComp-assoc-at δ γ u) ∙
    (isoComp-cong (idIso δ) p ∙
      (isoComp-assoc-at δ v α ∙
        (isoComp-cong q (idIso α) ∙ invIso (isoComp-assoc-at w β α))))

evaluate-compose-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : NatIso g g′) (β : NatIso f f′)
  → Iso₂ (evaluate-compose g′ f′ ∙ mapUncurry-cong (composeTerm-cong α β))
      (applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂)) ∙
        evaluate-compose g f)
evaluate-compose-natural {g = g} {g′} {f} {f′} α β =
  let κ = composeTerm-cong α β
      initial = mapUncurry-cong κ
      first = applyTerm-cong (κ ▷ pr₁) (idIso pr₂)
      second = applyTerm-cong (composeTerm-cong (α ▷ pr₁) (β ▷ pr₁)) (idIso pr₂)
      third = applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
      u = mapUncurry-as-apply (composeTerm g f)
      u′ = mapUncurry-as-apply (composeTerm g′ f′)
      v = applyTerm-cong (composeTerm-pre g f pr₁) (idIso pr₂)
      v′ = applyTerm-cong (composeTerm-pre g′ f′ pr₁) (idIso pr₂)
      w = apply-compose (g ∘ pr₁) (f ∘ pr₁) pr₂
      w′ = apply-compose (g′ ∘ pr₁) (f′ ∘ pr₁) pr₂
      square = apply-square (composeTerm-pre g f pr₁) (composeTerm-pre g′ f′ pr₁)
        (idIso pr₂) (idIso pr₂) (κ ▷ pr₁) (composeTerm-cong (α ▷ pr₁) (β ▷ pr₁))
        (idIso pr₂) (idIso pr₂) (binary-pre-inputs mapComp α β pr₁)
        (identity-square (idIso pr₂))
  in paste-squares (v ∙ u) (v′ ∙ u′) w w′ initial second third
    (paste-squares u u′ v v′ initial first second (mapUncurry-as-apply-natural κ) square)
    (apply-compose-natural (α ▷ pr₁) (β ▷ pr₁) (idIso pr₂))

mapUncurry-at-fixedParameter : {Γ X C D : CAT} {f g : MAP X (Map C D)}
  (α : NatIso f g) (p : MAP Γ X) {x y : MAP Γ C} (τ : NatIso x y)
  → Iso₂ (mapUncurry-at g p y ∙ (mapUncurry-cong α ⋆ pair-cong (idIso p) τ))
      (applyTerm-cong (α ▷ p) τ ∙ mapUncurry-at f p x)
mapUncurry-at-fixedParameter {f = f} {g} α p {x} {y} τ =
  let before = mapUncurry-at f p x
      middle = mapUncurry-at f p y
      after = mapUncurry-at g p y
      source-inner = mapUncurry f ◁ pair-cong (idIso p) τ
      source-outer = mapUncurry-cong α ▷ pair p y
      target-inner = applyTerm-cong (idIso (f ∘ p)) τ
      target-outer = applyTerm-cong (α ▷ p) (idIso y)
      normalized-inner = isoComp-cong
        (apply-cong-Iso₂ (postWhisker-idIso f p) (idIso τ)) (idIso before) ∙
        mapUncurry-at-inner f (idIso p) τ
      normalized-target = apply-cong-Iso₂ (isoComp-unitʳ-at (α ▷ p)) (isoComp-unitˡ-at τ) ∙
        invIso (apply-cong-comp (α ▷ p) (idIso (f ∘ p)) (idIso y) τ)
  in isoComp-cong normalized-target (idIso before) ∙
    chain-input-squares before middle after source-inner source-outer target-inner target-outer
      normalized-inner (mapUncurry-at-outer α p y)

uncurry-compose-cong-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : NatIso g g′) (β : NatIso f f′)
  → Iso₂ (uncurry-compose g′ f′ ∙ mapUncurry-cong (composeTerm-cong α β))
      ((mapUncurry-cong α ⋆ ParameterRetaining.retain-cong P (mapUncurry-cong β)) ∙
        uncurry-compose g f)
uncurry-compose-cong-natural {P = P} {g = g} {g′} {f} {f′} α β =
  let initial = mapUncurry-cong (composeTerm-cong α β)
      first = applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
      second = applyTerm-cong (α ▷ pr₁) (mapUncurry-cong β)
      last = mapUncurry-cong α ⋆ ParameterRetaining.retain-cong P (mapUncurry-cong β)
      u = evaluate-compose g f
      u′ = evaluate-compose g′ f′
      v = applyTerm-cong (idIso (g ∘ pr₁)) (invIso (mapUncurry-as-apply f))
      v′ = applyTerm-cong (idIso (g′ ∘ pr₁)) (invIso (mapUncurry-as-apply f′))
      w = mapUncurry-at g pr₁ (mapUncurry f)
      w′ = mapUncurry-at g′ pr₁ (mapUncurry f′)
      inner-square = move-square (mapUncurry-as-apply f′) (mapUncurry-cong β)
        (applyTerm-cong (β ▷ pr₁) (idIso pr₂)) (mapUncurry-as-apply f)
        (mapUncurry-as-apply-natural β)
      middle-square = apply-square (idIso (g ∘ pr₁)) (idIso (g′ ∘ pr₁))
        (invIso (mapUncurry-as-apply f)) (invIso (mapUncurry-as-apply f′))
        (α ▷ pr₁) (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
        (mapUncurry-cong β) (identity-square (α ▷ pr₁)) inner-square
      final-square = move-square w′ last second w
        (mapUncurry-at-fixedParameter α pr₁ (mapUncurry-cong β))
  in paste-squares (v ∙ u) (v′ ∙ u′) (invIso w) (invIso w′) initial second last
    (paste-squares u u′ v v′ initial first second
      (evaluate-compose-natural α β) middle-square) final-square
```

The final statement uses the actual isomorphism functor of the mapping
anima axiom. Its normalization to product action is a proved comparison,
and is inserted on both sides of the square.

```agda
uncurry-compose-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : NatIso g g′) (β : NatIso f f′)
  → Iso₂ (uncurry-compose g′ f′ ∙ mapUncurryIso (composeTerm-cong α β))
      ((mapUncurryIso α ⋆ ParameterRetaining.retain-cong P (mapUncurryIso β)) ∙
        uncurry-compose g f)
uncurry-compose-natural {P = P} {g = g} {g′} {f} {f′} α β =
  isoComp-cong
    (invIso (hcomp-cong (mapUncurryIso-at α)
      (pair-cong-Iso₂ (idIso (idIso pr₁)) (mapUncurryIso-at β))))
    (idIso (uncurry-compose g f)) ∙
  (uncurry-compose-cong-natural α β ∙
    isoComp-cong (idIso (uncurry-compose g′ f′)) (mapUncurryIso-at (composeTerm-cong α β)))
```

