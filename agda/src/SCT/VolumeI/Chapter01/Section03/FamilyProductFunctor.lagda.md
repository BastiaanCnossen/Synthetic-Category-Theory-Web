# Product comparisons with jointly varying inputs

Every varying input below is a functor with the same parameter category `A`.
Thus a comparison specializes to a natural isomorphism on the whole product
of its input isomorphism animae, rather than merely to individual points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductConstructions
import SCT.VolumeI.Chapter01.Section03.FamilyPairing as FamilyPairing
import SCT.VolumeI.Chapter01.Section03.ProductFunctorCoherence as ProductFunctorCoherence
import SCT.VolumeI.Chapter01.Section03.FamilyNaturality as FamilyNaturality

module SCT.VolumeI.Chapter01.Section03.FamilyProductFunctor
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Parameterized V T P PL S VC
open Parameterized.WhiskeringLaws V T P PL S VC W
open ProductConstructions V T P PL S
open FamilyPairing V T P PL S VC W
open ProductFunctorCoherence V T P PL S VC W using (productMap-cong; coordinate-comparison)
open FamilyNaturality V T P PL S VC W using
  (family-move-square; family-interchange-fixedOuter; family-interchange-fixedInner;
   family-pair-pre-inputs; family-pair-pre-substitution)

productFamily : {A C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  → MAP A (f ＝ f′) → MAP A (g ＝ g′)
  → MAP A (productMap f g ＝ productMap f′ g′)
productFamily α β = pairing (α ▷ pr₁) (β ▷ pr₂)

productFamily-absolute : {C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : f =₁ f′) (β : g =₁ g′)
  → (productFamily α β) =₂ (productMap-cong α β)
productFamily-absolute α β = pairing-absolute (α ▷ pr₁) (β ▷ pr₂)

productFamily-β₁ : {A C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (pr₁ ◁ productFamily α β) =₁
      (const ((pair-β₁ (f′ ∘ pr₁) (g′ ∘ pr₂)) ⁻¹) ∙
        ((α ▷ pr₁) ∙ const (pair-β₁ (f ∘ pr₁) (g ∘ pr₂))))
productFamily-β₁ α β = pairing-β₁ (α ▷ pr₁) (β ▷ pr₂)

productFamily-β₂ : {A C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → (pr₂ ◁ productFamily α β) =₁
      (const ((pair-β₂ (f′ ∘ pr₁) (g′ ∘ pr₂)) ⁻¹) ∙
        ((β ▷ pr₂) ∙ const (pair-β₂ (f ∘ pr₁) (g ∘ pr₂))))
productFamily-β₂ α β = pairing-β₂ (α ▷ pr₁) (β ▷ pr₂)

paste-family-squares : {A X Y : CAT} {a a′ b b′ c c′ : MAP X Y}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (v : b =₁ c) (v′ : b′ =₁ c′)
  (α : MAP A (a ＝ a′)) (β : MAP A (b ＝ b′)) (γ : MAP A (c ＝ c′))
  → (const u′ ∙ α) =₁ (β ∙ const u)
  → (const v′ ∙ β) =₁ (γ ∙ const v)
  → (const (v′ ∙ u′) ∙ α) =₁ (γ ∙ const (v ∙ u))
paste-family-squares u u′ v v′ α β γ p q =
  isoComp-cong (idIso γ) (const-comp v u) ∙
  (assoc γ (const v) (const u) ∙
  (isoComp-cong q (idIso (const u)) ∙
  ((assoc (const v′) β (const u)) ⁻¹ ∙
  (isoComp-cong (idIso (const v′)) p ∙
  (assoc (const v′) (const u′) α ∙
   isoComp-cong ((const-comp v′ u′) ⁻¹) (idIso α))))))

pair-family-square : {A X C D : CAT}
  {a a′ b b′ : MAP X C} {d d′ e e′ : MAP X D}
  (u : a =₁ b) (u′ : a′ =₁ b′)
  (v : d =₁ e) (v′ : d′ =₁ e′)
  (α : MAP A (a ＝ a′)) (β : MAP A (b ＝ b′))
  (γ : MAP A (d ＝ d′)) (δ : MAP A (e ＝ e′))
  → (const u′ ∙ α) =₁ (β ∙ const u)
  → (const v′ ∙ γ) =₁ (δ ∙ const v)
  → (const (pair-cong u′ v′) ∙ pairing α γ) =₁
      (pairing β δ ∙ const (pair-cong u v))
pair-family-square u u′ v v′ α β γ δ p q =
  isoComp-cong (idIso _) (pairing-constant u v) ∙
  (pairing-composition β (const u) δ (const v) ∙
  (pairing-cong p q ∙
  ((pairing-composition (const u′) α (const v′) γ) ⁻¹ ∙
    isoComp-cong ((pairing-constant u′ v′) ⁻¹) (idIso _))))

family-pre-composition : {A B C D : CAT} {f g h : MAP C D}
  (τ : MAP A (g ＝ h)) (σ : MAP A (f ＝ g)) (k : MAP B C)
  → ((τ ∙ σ) ▷ k) =₁ ((τ ▷ k) ∙ (σ ▷ k))
family-pre-composition {f = f} {g} {h} τ σ k =
  let point = pair τ σ
  in specialize (preWhisker-isoComp f g h k) point
    (preWhisker-evaluate (pr₁ ∙ pr₂) k point
      (isoComp-evaluate pr₁ pr₂ point (pair-β₁ τ σ) (pair-β₂ τ σ)))
    (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) point
      (preWhisker-evaluate pr₁ k point (pair-β₁ τ σ))
      (preWhisker-evaluate pr₂ k point (pair-β₂ τ σ)))

productFamily-composition : {A C C′ D D′ : CAT}
  {f₀ f₁ f₂ : MAP C C′} {g₀ g₁ g₂ : MAP D D′}
  (α₂ : MAP A (f₁ ＝ f₂)) (α₁ : MAP A (f₀ ＝ f₁))
  (β₂ : MAP A (g₁ ＝ g₂)) (β₁ : MAP A (g₀ ＝ g₁))
  → (productFamily (α₂ ∙ α₁) (β₂ ∙ β₁)) =₁
      (productFamily α₂ β₂ ∙ productFamily α₁ β₁)
productFamily-composition α₂ α₁ β₂ β₁ =
  pairing-composition (α₂ ▷ pr₁) (α₁ ▷ pr₁) (β₂ ▷ pr₂) (β₁ ▷ pr₂) ∙
  pairing-cong (family-pre-composition α₂ α₁ pr₁) (family-pre-composition β₂ β₁ pr₂)

productFamily-cong : {A C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  {α α′ : MAP A (f ＝ f′)} {β β′ : MAP A (g ＝ g′)}
  → α =₁ α′ → β =₁ β′ → (productFamily α β) =₁ (productFamily α′ β′)
productFamily-cong p q = pairing-cong (preWhisker pr₁ ◁ p) (preWhisker pr₂ ◁ q)

productFamily-constant : {A C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : f =₁ f′) (β : g =₁ g′)
  → (productFamily (const {P = A} α) (const β)) =₁ (const (productMap-cong α β))
productFamily-constant α β = pairing-constant (α ▷ pr₁) (β ▷ pr₂) ∙
  pairing-cong (pre-constant α pr₁) (pre-constant β pr₂)

productFamily-identity : {A C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → (productFamily (const {P = A} (idIso f)) (const (idIso g))) =₁
      (const (idIso (productMap f g)))
productFamily-identity f g = pairing-identity (f ∘ pr₁) (g ∘ pr₂) ∙
  pairing-cong
    (const-cong (preWhisker-idIso f pr₁) ∙ pre-constant (idIso f) pr₁)
    (const-cong (preWhisker-idIso g pr₂) ∙ pre-constant (idIso g) pr₂)

coordinate-outer-family : {A R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : (π ∘ h) =₁ (f ∘ ρ)) {F F′ : MAP C D} (θ : MAP A (F ＝ F′))
  →
      (const (coordinate-comparison ρ f π h b F′) ∙ ((θ ▷ π) ▷ h)) =₁
      (((θ ▷ f) ▷ ρ) ∙ const (coordinate-comparison ρ f π h b F))
coordinate-outer-family ρ f π h b {F} {F′} θ =
  let first = preWhisker-comp-general θ π h
      middle = (family-interchange-fixedInner θ b) ⁻¹
      last = family-move-square (comp-assoc ρ f F′) ((θ ▷ f) ▷ ρ)
        (θ ▷ (f ∘ ρ)) (comp-assoc ρ f F) (preWhisker-comp-general θ f ρ)
      initial = paste-family-squares (comp-assoc h π F) (comp-assoc h π F′)
        (F ◁ b) (F′ ◁ b) ((θ ▷ π) ▷ h) (θ ▷ (π ∘ h)) (θ ▷ (f ∘ ρ))
        first middle
  in paste-family-squares ((F ◁ b) ∙ comp-assoc h π F) ((F′ ◁ b) ∙ comp-assoc h π F′)
    ((comp-assoc ρ f F) ⁻¹) ((comp-assoc ρ f F′) ⁻¹)
    ((θ ▷ π) ▷ h) (θ ▷ (f ∘ ρ)) ((θ ▷ f) ▷ ρ) initial last

coordinate-inner-family : {A R X K C D : CAT}
  (ρ : MAP R X) (π : MAP K C) (F : MAP C D)
  {f f′ : MAP X C} {h h′ : MAP R K}
  (b : (π ∘ h) =₁ (f ∘ ρ)) (b′ : (π ∘ h′) =₁ (f′ ∘ ρ))
  (α : MAP A (f ＝ f′)) (δ : MAP A (h ＝ h′))
  → (const b′ ∙ (π ◁ δ)) =₁ ((α ▷ ρ) ∙ const b)
  →
      (const (coordinate-comparison ρ f′ π h′ b′ F) ∙ ((F ∘ π) ◁ δ)) =₁
      (((F ◁ α) ▷ ρ) ∙ const (coordinate-comparison ρ f π h b F))
coordinate-inner-family ρ π F {f} {f′} {h} {h′} b b′ α δ square =
  let first = postWhisker-comp-general δ π F
      middle = isoComp-cong (idIso _) (post-constant F b) ∙
        (post-composition F (α ▷ ρ) (const b) ∙
        ((postWhisker F ◁ square) ∙
        ((post-composition F (const b′) (π ◁ δ)) ⁻¹ ∙
         isoComp-cong ((post-constant F b′) ⁻¹) (idIso _))))
      last = family-move-square (comp-assoc ρ f′ F) ((F ◁ α) ▷ ρ)
        (F ◁ (α ▷ ρ)) (comp-assoc ρ f F) (whisker-mixed-general α ρ F)
      initial = paste-family-squares (comp-assoc h π F) (comp-assoc h′ π F)
        (F ◁ b) (F ◁ b′) ((F ∘ π) ◁ δ) (F ◁ (π ◁ δ)) (F ◁ (α ▷ ρ))
        first middle
  in paste-family-squares ((F ◁ b) ∙ comp-assoc h π F) ((F ◁ b′) ∙ comp-assoc h′ π F)
    ((comp-assoc ρ f F) ⁻¹) ((comp-assoc ρ f′ F) ⁻¹)
    ((F ∘ π) ◁ δ) (F ◁ (α ▷ ρ)) ((F ◁ α) ▷ ρ) initial last

productMap-comp-family-outer : {A C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (g : MAP D D′)
  {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
  (θ : MAP A (F ＝ F′)) (ψ : MAP A (G ＝ G′))
  →
      (const (productMap-comp f F′ g G′) ∙ (productFamily θ ψ ▷ productMap f g)) =₁
      (productFamily (θ ▷ f) (ψ ▷ g) ∙ const (productMap-comp f F g G))
productMap-comp-family-outer f g {F} {F′} {G} {G′} θ ψ =
  let h = productMap f g
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      e = coordinate-comparison pr₁ f pr₁ h b F
      e′ = coordinate-comparison pr₁ f pr₁ h b F′
      k = coordinate-comparison pr₂ g pr₂ h d G
      k′ = coordinate-comparison pr₂ g pr₂ h d G′
      middle = pairing ((θ ▷ pr₁) ▷ h) ((ψ ▷ pr₂) ▷ h)
      last = productFamily (θ ▷ f) (ψ ▷ g)
      first-square = (family-pair-pre-inputs (θ ▷ pr₁) (ψ ▷ pr₂) h) ⁻¹
      last-square = pair-family-square e e′ k k′ ((θ ▷ pr₁) ▷ h) ((θ ▷ f) ▷ pr₁)
        ((ψ ▷ pr₂) ▷ h) ((ψ ▷ g) ▷ pr₂)
        (coordinate-outer-family pr₁ f pr₁ h b θ)
        (coordinate-outer-family pr₂ g pr₂ h d ψ)
  in paste-family-squares (pair-pre (F ∘ pr₁) (G ∘ pr₂) h)
    (pair-pre (F′ ∘ pr₁) (G′ ∘ pr₂) h)
    (pair-cong e k) (pair-cong e′ k′)
    (productFamily θ ψ ▷ h) middle last first-square last-square

productMap-comp-family-inner : {A C C′ C″ D D′ D″ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) (F : MAP C′ C″) (G : MAP D′ D″)
  →
      (const (productMap-comp f′ F g′ G) ∙ (productMap F G ◁ productFamily α β)) =₁
      (productFamily (F ◁ α) (G ◁ β) ∙ const (productMap-comp f F g G))
productMap-comp-family-inner {f = f} {f′} {g} {g′} α β F G =
  let h = productMap f g
      h′ = productMap f′ g′
      δ = productFamily α β
      b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
      b′ = pair-β₁ (f′ ∘ pr₁) (g′ ∘ pr₂)
      d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
      d′ = pair-β₂ (f′ ∘ pr₁) (g′ ∘ pr₂)
      e = coordinate-comparison pr₁ f pr₁ h b F
      e′ = coordinate-comparison pr₁ f′ pr₁ h′ b′ F
      k = coordinate-comparison pr₂ g pr₂ h d G
      k′ = coordinate-comparison pr₂ g′ pr₂ h′ d′ G
      middle = pairing ((F ∘ pr₁) ◁ δ) ((G ∘ pr₂) ◁ δ)
      last = productFamily (F ◁ α) (G ◁ β)
      first-square = (family-pair-pre-substitution (F ∘ pr₁) (G ∘ pr₂) δ) ⁻¹
      last-square = pair-family-square e e′ k k′ ((F ∘ pr₁) ◁ δ) ((F ◁ α) ▷ pr₁)
        ((G ∘ pr₂) ◁ δ) ((G ◁ β) ▷ pr₂)
        (coordinate-inner-family pr₁ pr₁ F b b′ α δ
          (pairing-triangle₁ (α ▷ pr₁) (β ▷ pr₂)))
        (coordinate-inner-family pr₂ pr₂ G d d′ β δ
          (pairing-triangle₂ (α ▷ pr₁) (β ▷ pr₂)))
  in paste-family-squares (pair-pre (F ∘ pr₁) (G ∘ pr₂) h)
    (pair-pre (F ∘ pr₁) (G ∘ pr₂) h′)
    (pair-cong e k) (pair-cong e′ k′)
    (productMap F G ◁ δ) middle last first-square last-square

productMap-comp-family : {A C C′ C″ D D′ D″ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  (θ : MAP A (F ＝ F′)) (ψ : MAP A (G ＝ G′))
  →
      (const (productMap-comp f′ F′ g′ G′) ∙ (productFamily θ ψ ⋆ productFamily α β)) =₁
      (productFamily (θ ⋆ α) (ψ ⋆ β) ∙ const (productMap-comp f F g G))
productMap-comp-family {f = f} {f′} {g} {g′} {F} {F′} {G} {G′} α β θ ψ =
  let c = const (productMap-comp f F g G)
      c₁ = const (productMap-comp f′ F g′ G)
      c₂ = const (productMap-comp f′ F′ g′ G′)
      u = productMap F G ◁ productFamily α β
      v = productFamily θ ψ ▷ productMap f′ g′
      a = productFamily (F ◁ α) (G ◁ β)
      b = productFamily (θ ▷ f′) (ψ ▷ g′)
  in isoComp-cong ((productFamily-composition (θ ▷ f′) (F ◁ α) (ψ ▷ g′) (G ◁ β)) ⁻¹) (idIso c) ∙
    ((assoc b a c) ⁻¹ ∙
    (isoComp-cong (idIso b) (productMap-comp-family-inner α β F G) ∙
    (assoc b c₁ u ∙
    (isoComp-cong (productMap-comp-family-outer f′ g′ θ ψ) (idIso u) ∙
     (assoc c₂ v u) ⁻¹))))

productFamily-pre : {A R C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) (r : MAP R (C × D))
  →
      (const (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) r) ∙ (productFamily α β ▷ r)) =₁
      (pairing ((α ▷ pr₁) ▷ r) ((β ▷ pr₂) ▷ r) ∙
        const (pair-pre (f ∘ pr₁) (g ∘ pr₂) r))
productFamily-pre α β r = (family-pair-pre-inputs (α ▷ pr₁) (β ▷ pr₂) r) ⁻¹
```

For clarity, here is the simultaneous four-input law on its universal
parameter category, with the inputs given by the four product projections.

```agda
module UniversalComposition {C C′ C″ D D′ D″ : CAT}
  (f f′ : MAP C C′) (g g′ : MAP D D′)
  (F F′ : MAP C′ C″) (G G′ : MAP D′ D″) where

  source : CAT
  source = ((F ＝ F′) × (G ＝ G′)) × ((f ＝ f′) × (g ＝ g′))

  firstOuter : MAP source (F ＝ F′)
  firstOuter = pr₁ ∘ pr₁

  secondOuter : MAP source (G ＝ G′)
  secondOuter = pr₂ ∘ pr₁

  firstInner : MAP source (f ＝ f′)
  firstInner = pr₁ ∘ pr₂

  secondInner : MAP source (g ＝ g′)
  secondInner = pr₂ ∘ pr₂

  comparison :
    (const (productMap-comp f′ F′ g′ G′) ∙
      (productFamily firstOuter secondOuter ⋆ productFamily firstInner secondInner)) =₁
    (productFamily (firstOuter ⋆ firstInner) (secondOuter ⋆ secondInner) ∙
      const (productMap-comp f F g G))
  comparison = productMap-comp-family firstInner secondInner firstOuter secondOuter
```
