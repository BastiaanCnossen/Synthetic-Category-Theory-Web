# Coherence of restriction and postcomposition of triangles

This module continues Triangles with the calculations that compare
restriction and postcomposition of specified triangles when both occur, or
when a restriction is iterated or changed. They are fixed identifications of
specified routes, used by the composition and evaluation calculus of
Section04 and the cone calculus of Section06. Each statement keeps the
selected associators; the proofs use the whiskered pentagon to move
associators past each other.

The parts are: postcomposition of a restricted triangle; postcomposition of
iterated and changed restrictions; frames of a substitution square; restricted
normalizations of projections; constants under restriction; and evaluation of
a functor identified with a composite. `π`, `F`, `e` denote postcomposing
functors; `r`, `s`, `t` restricting functors.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
```

## Postcomposing a restricted triangle

Postcomposing the composite of a restricted triangle with a further
identification agrees with restricting the postcomposed triangle. A square
of triangles with a changed restriction is carried to the corresponding
square after postcomposition, and postcomposition with a composite agrees
with successive postcomposition.

```agda
module _ {Γ : Context} where
  post-restrict-triangle : {Q R K A B : CAT Γ}
    (F : MAP A B) (π : MAP K A) (h : MAP R K) (k : MAP Q R)
    {q : MAP R A} {v : MAP Q A}
    (b : (π ∘ h) =₁ q) (c : (q ∘ k) =₁ v)
    → ((F ◁ (c ∙ restrict-triangle π h b k)) ∙
          (comp-assoc (h ∘ k) π F ∙ comp-assoc k h (F ∘ π))) =₂
        ((F ◁ c) ∙ (comp-assoc k q F ∙ (post-triangle F π h b ▷ k)))
  post-restrict-triangle F π h k {q} b c =
    let A = comp-assoc k h π
        B = comp-assoc k (π ∘ h) F
        C = comp-assoc h π F ▷ k
        D = comp-assoc k q F
        e = F ◁ c
        d = F ◁ (b ▷ k)
        p = F ◁ (c ∙ ((b ▷ k) ∙ A ⁻¹))
        cancellation = inv-comp-right (c ∙ (b ▷ k)) A ∙
          comp₌-cong ((comp₌-assoc c (b ▷ k) (A ⁻¹)) ⁻¹) (id₌ A)
        join = postWhisker-comp₌ F c (b ▷ k) ∙
          ((postWhisker F ◁ cancellation) ∙
            (postWhisker-comp₌ F (c ∙ ((b ▷ k) ∙ A ⁻¹)) A) ⁻¹)
        mixed = (whisker-mixed-One b k F) ⁻¹
        finish = comp₌-cong (id₌ e)
          (comp₌-cong (id₌ D)
            ((preWhisker-comp₌ (F ◁ b) (comp-assoc h π F) k) ⁻¹) ∙
            comp₌-assoc D ((F ◁ b) ▷ k) C)
        exchange = comp₌-cong (id₌ e) (comp₌-cong mixed (id₌ C)) ∙
          (comp₌-cong (id₌ e) ((comp₌-assoc d B C) ⁻¹) ∙
            comp₌-assoc e d (B ∙ C))
    in finish ∙ (exchange ∙
      (comp₌-cong join (id₌ (B ∙ C)) ∙
        ((comp₌-assoc p (F ◁ A) (B ∙ C)) ⁻¹ ∙
          comp₌-cong (id₌ p) (pentagon-whiskered-right k h π F))))

  post-triangle-change : {Q R K A B : CAT Γ}
    (F : MAP A B) (π : MAP K A) (h : MAP R K) (t : MAP Q R)
    (s : MAP Q K) (δ : (h ∘ t) =₁ s)
    {q : MAP R A} {v : MAP Q A}
    (b : (π ∘ h) =₁ q) (b′ : (π ∘ s) =₁ v) (c : (q ∘ t) =₁ v)
    → SquareCell₌ (π ◁ δ) c (restrict-triangle π h b t) b′
    → (post-triangle F π s b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc t h (F ∘ π))) =₂
        ((F ◁ c) ∙ (comp-assoc t q F ∙ (post-triangle F π h b ▷ t)))
  post-triangle-change F π h t s δ b b′ c square =
    let leftImage = F ◁ b′
        inputA = comp-assoc s π F
        change = (F ∘ π) ◁ δ
        sourceA = comp-assoc t h (F ∘ π)
        across = F ◁ (π ◁ δ)
        afterA = comp-assoc (h ∘ t) π F
        projectImage = (postWhisker F ◁ square) ∙ (postWhisker-comp₌ F b′ (π ◁ δ)) ⁻¹
        moveInput = comp₌-assoc across afterA sourceA ∙
          (comp₌-cong (postWhisker-comp-One δ π F) (id₌ sourceA) ∙
            (comp₌-assoc inputA change sourceA) ⁻¹)
        removeInner = comp₌-cong projectImage (id₌ (afterA ∙ sourceA)) ∙
          (comp₌-assoc leftImage across (afterA ∙ sourceA)) ⁻¹
    in post-restrict-triangle F π h t b c ∙
      (removeInner ∙ (comp₌-cong (id₌ leftImage) moveInput ∙
        comp₌-assoc leftImage inputA (change ∙ sourceA)))

  module _ {R K X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-triangle-comp : {Y Z : CAT Γ}
      (F : MAP Y Z) (G : Term Y) (π : MAP K X) (t : MAP R K)
      {p : MAP R X} (b : (π ∘ t) =₁ p)
      → (comp-assoc p G F ∙ post-triangle (F ∘ G) π t b) =₂
          ((F ◁ post-triangle G π t b) ∙ (comp-assoc t (G ∘ π) F ∙ (comp-assoc π G F ▷ t)))
    post-triangle-comp F G π t {p} b =
      let A = comp-assoc p G F
          B = (F ∘ G) ◁ b
          C = comp-assoc t π (F ∘ G)
          D = F ◁ (G ◁ b)
          E = comp-assoc (π ∘ t) G F
          I = F ◁ comp-assoc t π G
          J = comp-assoc t (G ∘ π) F
          K = comp-assoc π G F ▷ t
      in comp₌-cong ((postWhisker-comp₌ F (G ◁ b) (comp-assoc t π G)) ⁻¹) (id₌ (J ∙ K)) ∙
        ((comp₌-assoc D I (J ∙ K)) ⁻¹ ∙
        (comp₌-cong (id₌ D) (pentagon-whiskered-right t π G F) ∙
        (comp₌-assoc D E C ∙
        (comp₌-cong (postWhisker-comp-One b G F) (id₌ C) ∙ (comp₌-assoc A B C) ⁻¹))))
```

## Iterated and changed restrictions under postcomposition

Postcomposition preserves a specified comparison of two successive
restrictions with a restriction along their composite, or along a functor
identified with their composite. With a specified reverse identification,
the image square can be solved for its upper side.

```agda
  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-iterated-restriction : {A B : CAT Γ}
      (F : MAP A B) (H : Term A) (r : MAP R X) (s : MAP Q R)
      {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
      (u : (H ∘ r) =₁ H₁) (v : (H₁ ∘ s) =₁ H₂)
      (w : (H ∘ (r ∘ s)) =₁ H₃) (z : H₂ =₁ H₃)
      → (w ∙ comp-assoc s r H) =₂ (z ∙ (v ∙ (u ▷ s)))
      → (((F ◁ w) ∙ comp-assoc (r ∘ s) H F) ∙ comp-assoc s r (F ∘ H)) =₂
          ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc s H₁ F) ∙ (post-triangle F H r u ▷ s)))
    post-iterated-restriction F H r s {H₁} u v w z p =
      let A = comp-assoc s r H
          pre = u ▷ s
          normalize = comp₌-assoc (z ∙ v) pre (A ⁻¹) ∙
            (comp₌-cong ((comp₌-assoc z v pre) ⁻¹) (id₌ (A ⁻¹)) ∙
              (comp₌-cong p (id₌ (A ⁻¹)) ∙ (comp-inv-right w A) ⁻¹))
          image = post-triangle F H r u ▷ s
          targetA = comp-assoc s H₁ F
          finish = comp₌-cong (id₌ (F ◁ z)) ((comp₌-assoc (F ◁ v) targetA image) ⁻¹) ∙
            (comp₌-assoc (F ◁ z) (F ◁ v) (targetA ∙ image) ∙
              comp₌-cong (postWhisker-comp₌ F z v) (id₌ (targetA ∙ image)))
      in finish ∙
        (post-restrict-triangle F H r s u (z ∙ v) ∙
          (comp₌-cong (postWhisker F ◁ normalize)
            (id₌ (comp-assoc (r ∘ s) H F ∙ comp-assoc s r (F ∘ H))) ∙
            comp₌-assoc (F ◁ w) (comp-assoc (r ∘ s) H F) (comp-assoc s r (F ∘ H))))

    post-changed-restriction : {A B : CAT Γ}
      (F : MAP A B) (H : Term A) (h : MAP R X) (t : MAP Q R)
      (s : MAP Q X) (δ : (h ∘ t) =₁ s)
      {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
      (u : (H ∘ h) =₁ H₁) (v : (H₁ ∘ t) =₁ H₂)
      (w : (H ∘ s) =₁ H₃) (z : H₂ =₁ H₃)
      → (w ∙ ((H ◁ δ) ∙ comp-assoc t h H)) =₂ (z ∙ (v ∙ (u ▷ t)))
      → (((F ◁ w) ∙ comp-assoc s H F) ∙ (((F ∘ H) ◁ δ) ∙ comp-assoc t h (F ∘ H))) =₂
          ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc t H₁ F) ∙ (post-triangle F H h u ▷ t)))
    post-changed-restriction F H h t s δ u v w z square =
      let image = F ◁ w
          inputA = comp-assoc s H F
          change = (F ∘ H) ◁ δ
          outsideA = comp-assoc t h (F ∘ H)
          across = F ◁ (H ◁ δ)
          middleA = comp-assoc (h ∘ t) H F
          normalization = (comp₌-assoc (F ◁ (w ∙ (H ◁ δ))) middleA outsideA) ⁻¹ ∙
            (comp₌-cong ((postWhisker-comp₌ F w (H ◁ δ)) ⁻¹) (id₌ (middleA ∙ outsideA)) ∙
            ((comp₌-assoc image across (middleA ∙ outsideA)) ⁻¹ ∙
            (comp₌-cong (id₌ image) (comp₌-assoc across middleA outsideA) ∙
            (comp₌-cong (id₌ image) (comp₌-cong (postWhisker-comp-One δ H F) (id₌ outsideA)) ∙
            (comp₌-cong (id₌ image) ((comp₌-assoc inputA change outsideA) ⁻¹) ∙
              comp₌-assoc image inputA (change ∙ outsideA))))))
      in post-iterated-restriction F H h t u v (w ∙ (H ◁ δ)) z
          (square ∙ comp₌-assoc w (H ◁ δ) (comp-assoc t h H)) ∙ normalization

    post-changed-restriction-inverse : {A B : CAT Γ}
      (F : MAP A B) (H : Term A) (h : MAP R X) (t : MAP Q R)
      (s : MAP Q X) (δ : (h ∘ t) =₁ s)
      {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
      (u : (H ∘ h) =₁ H₁) (v : (H₁ ∘ t) =₁ H₂)
      (w : (H ∘ s) =₁ H₃) (z : H₂ =₁ H₃)
      (square : (w ∙ ((H ◁ δ) ∙ comp-assoc t h H)) =₂ (z ∙ (v ∙ (u ▷ t))))
      (back : (F ∘ H₁) =₁ ((F ∘ H) ∘ h))
      (inverse : (post-triangle F H h u ∙ back) =₂ id₌ (F ∘ H₁))
      → ((F ◁ z) ∙ ((F ◁ v) ∙ comp-assoc t H₁ F)) =₂
          (((F ◁ w) ∙ comp-assoc s H F) ∙
            (((F ∘ H) ◁ δ) ∙ (comp-assoc t h (F ∘ H) ∙ (back ▷ t))))
    post-changed-restriction-inverse F H h t s δ {H₁} u v w z square back inverse =
      let A = comp-assoc t h (F ∘ H)
          forward = post-triangle F H h u
          before = forward ▷ t
          backT = back ▷ t
          target = (F ◁ z) ∙ ((F ◁ v) ∙ comp-assoc t H₁ F)
          short = (F ◁ w) ∙ comp-assoc s H F
          step = (F ∘ H) ◁ δ
          cancel = preWhisker-id₌ (F ∘ H₁) t ∙
            ((preWhisker t ◁ inverse) ∙ (preWhisker-comp₌ forward back t) ⁻¹)
          compare = (comp₌-assoc (F ◁ z) ((F ◁ v) ∙ comp-assoc t H₁ F) before) ⁻¹ ∙
            post-changed-restriction F H h t s δ u v w z square
      in comp₌-cong (id₌ short) (comp₌-assoc step A backT) ∙
        (comp₌-assoc short (step ∙ A) backT ∙
        (comp₌-cong (compare ⁻¹) (id₌ backT) ∙
        ((comp₌-assoc target before backT) ⁻¹ ∙
        (comp₌-cong (id₌ target) (cancel ⁻¹) ∙ (comp₌-unitʳ-One target) ⁻¹))))
```

## Frames of a substitution square

Suppose `κ : s ∘ t = st` lies over `T` along `π`, with the restricted
triangle of `b : π ∘ s = q₁` and `bst : π ∘ st = q₂` as sides (the
hypothesis `projection`). A frame `v : q = π` carries this to `q`
(`lies-over-reframe`): `κ` lies over `T` along `q`, with the triangles
`S = b ∙ (v ▷ s)` and `Sst = bst ∙ (v ▷ st)`, which are supplied with these
normalizations. Restricting the reframed triangle `S` along `t` is the
reframing of the restricted triangle, by the naturality of the associator
in `v`. The conclusion is stated with the associator moved to the edge.
Postcomposition carries a square of frames, written with the reverse
restriction identification, to the corresponding image square.

```agda
module _ {Γ : Context} where
  module FrameChange {K₀ K₁ K₂ C : CAT Γ}
    (s : MAP K₁ K₀) (t : MAP K₂ K₁) (st : MAP K₂ K₀)
    (κ : (s ∘ t) =₁ st)
    (q π : MAP K₀ C) (q₁ : MAP K₁ C) (q₂ : MAP K₂ C)
    (v : q =₁ π)
    (b : (π ∘ s) =₁ q₁) (bst : (π ∘ st) =₁ q₂)
    (S : (q ∘ s) =₁ q₁) (T : (q₁ ∘ t) =₁ q₂)
    (Sst : (q ∘ st) =₁ q₂)
    (normalize-first : S =₂ (b ∙ (v ▷ s)))
    (normalize-composite : Sst =₂ (bst ∙ (v ▷ st)))
    (projection : (bst ∙ (π ◁ κ)) =₂ (T ∙ restrict-triangle π s b t)) where

    private
      Aq = comp-assoc t s q
      Aπ = comp-assoc t s π
      vv = (v ▷ s) ▷ t
      V = v ▷ (s ∘ t)

      restrict-reframed : (restrict-triangle π s b t ∙ V) =₂ restrict-triangle q s S t
      restrict-reframed =
        comp₌-cong (preWhisker t ◁ normalize-first ⁻¹) (id₌ (Aq ⁻¹)) ∙
          (comp₌-cong ((preWhisker-comp₌ b (v ▷ s) t) ⁻¹) (id₌ (Aq ⁻¹)) ∙
          ((comp₌-assoc (b ▷ t) vv (Aq ⁻¹)) ⁻¹ ∙
          (comp₌-cong (id₌ (b ▷ t))
            (inverse-square₌ {t = vv} {b = V} {l = Aq} {r = Aπ}
              (preWhisker-comp-One v s t)) ∙
            comp₌-assoc (b ▷ t) (Aπ ⁻¹) V)))

      reframed : SquareCell₌ (q ◁ κ) T (restrict-triangle q s S t) Sst
      reframed = replace-sides₌ restrict-reframed (normalize-composite ⁻¹)
        (lies-over-reframe {A = One} {π = π} {q = q} v
          {b = restrict-triangle π s b t} {b′ = bst} {ε = κ} {α = T} projection)

    compatible : (Sst ∙ ((q ◁ κ) ∙ Aq)) =₂ (T ∙ (S ▷ t))
    compatible = unrestrict-square q s t st κ S Sst T reframed

  post-frame-square : {Q R A B : CAT Γ} (e : MAP A B) (s : MAP Q R)
    {H J : MAP R A} {H′ J′ K L : MAP Q A}
    (before : H =₁ J) (after : H′ =₁ J′) (finish : J′ =₁ L)
    (out : K =₁ L) (pre : (J ∘ s) =₁ K) (κ : (H ∘ s) =₁ H′)
    → ((finish ∙ after) ∙ κ) =₂ ((out ∙ pre) ∙ (before ▷ s))
    → ((e ◁ finish) ∙ (e ◁ after)) =₂
      ((e ◁ out) ∙ (((e ◁ pre) ∙ comp-assoc s J e) ∙
        (((e ◁ before) ▷ s) ∙ ((comp-assoc s H e) ⁻¹ ∙ (e ◁ κ ⁻¹)))))
  post-frame-square e s {H} {J} before after finish out pre κ frame-square =
    (let changed = out ∙ pre
         x = e ◁ out
         y = e ◁ pre
         A = comp-assoc s J e
         b = (e ◁ before) ▷ s
         Aold = comp-assoc s H e
         B = Aold ⁻¹
         c = e ◁ κ ⁻¹
         d = e ◁ (before ▷ s)
         natural = whisker-mixed-One before s e
         collapse = comp₌-cong (id₌ d) (comp-inv-left Aold c) ∙
           (comp₌-assoc d Aold (B ∙ c) ∙
           (comp₌-cong natural (id₌ (B ∙ c)) ∙
             (comp₌-assoc A b (B ∙ c)) ⁻¹))
         normalize = comp₌-cong (id₌ x)
           (comp₌-cong (id₌ y) collapse ∙ comp₌-assoc y A (b ∙ (B ∙ c)))
         merge = (postWhisker-comp₌ e out (pre ∙ ((before ▷ s) ∙ κ ⁻¹))) ⁻¹ ∙
           comp₌-cong (id₌ x)
             ((postWhisker-comp₌ e pre ((before ▷ s) ∙ κ ⁻¹)) ⁻¹ ∙
               comp₌-cong (id₌ y) ((postWhisker-comp₌ e (before ▷ s) (κ ⁻¹)) ⁻¹))
         solve = comp-inv-right (finish ∙ after) κ ∙
           (comp₌-cong (frame-square ⁻¹) (id₌ (κ ⁻¹)) ∙
           ((comp₌-assoc changed (before ▷ s) (κ ⁻¹)) ⁻¹ ∙
             (comp₌-assoc out pre ((before ▷ s) ∙ κ ⁻¹)) ⁻¹))
       in postWhisker-comp₌ e finish after ∙
       ((postWhisker e ◁ solve) ∙ (merge ∙ normalize))) ⁻¹

  post-triangle-inverse : {Q R A B : CAT Γ}
    (e : MAP A B) (H : MAP R A) (s : MAP Q R)
    {H′ : MAP Q A} (κ : (H ∘ s) =₁ H′)
    → (post-triangle e H s κ ∙ ((comp-assoc s H e) ⁻¹ ∙ (e ◁ κ ⁻¹))) =₂ id₌ (e ∘ H′)
  post-triangle-inverse e H s {H′} κ =
    let A = comp-assoc s H e
    in postWhisker-id₌ e H′ ∙
      ((postWhisker e ◁ comp₌-inverseʳ-One κ) ∙
      ((postWhisker-comp₌ e κ (κ ⁻¹)) ⁻¹ ∙
      (comp₌-cong (id₌ (e ◁ κ)) (comp-inv-left A (e ◁ κ ⁻¹)) ∙
        comp₌-assoc (e ◁ κ) A (A ⁻¹ ∙ (e ◁ κ ⁻¹)))))
```

## Postcomposition of reversed restriction identifications

For a supplied identification `a : q = p ∘ s`, postcomposition gives
`e ∘ q = (e ∘ p) ∘ s`. Two successive such identifications compose, by the
external pentagon, to the postcomposition of their composite.

```agda
module _ {Γ : Context} where
  private
    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      exchange-middle : {C D : CAT Γ} {a b c d e c′ : MAP C D}
        (δ : d ＝ e) (γ : c ＝ d) (β : b ＝ c) (α : a ＝ b)
        (γ′ : c′ ＝ d) (β′ : b ＝ c′)
        → (γ ∙ β) =₁ (γ′ ∙ β′)
        → ((δ ∙ γ) ∙ (β ∙ α)) =₁ ((δ ∙ γ′) ∙ (β′ ∙ α))
      exchange-middle δ γ β α γ′ β′ p =
        (reassociateFour δ γ′ β′ α) ⁻¹ ∙
          (comp₌-cong (id₌ δ) (comp₌-cong p (id₌ α)) ∙ reassociateFour δ γ β α)

  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-restriction : {Z D : CAT Γ} (e : MAP Z D) (p : Term Z) (s : MAP R X)
      {q : MAP R Z} → q =₁ (p ∘ s) → (e ∘ q) =₁ ((e ∘ p) ∘ s)
    post-restriction e p s a = (comp-assoc s p e) ⁻¹ ∙ (e ◁ a)

  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    post-restriction-iterated : {Z D : CAT Γ}
      (e : MAP Z D) (p : Term Z) (s : MAP R X) (t : MAP Q R)
      {q : MAP R Z} {r : MAP Q Z} (a : q =₁ (p ∘ s)) (b : r =₁ (q ∘ t))
      → (comp-assoc t s (e ∘ p) ∙
            ((post-restriction e p s a ▷ t) ∙ post-restriction e q t b)) =₂
          ((comp-assoc (s ∘ t) p e) ⁻¹ ∙
            (e ◁ (comp-assoc t s p ∙ ((a ▷ t) ∙ b))))
    post-restriction-iterated e p s t {q} {r} a b =
      let A = comp-assoc t s (e ∘ p)
          B = (comp-assoc s p e) ⁻¹ ▷ t
          C = (e ◁ a) ▷ t
          D = (comp-assoc t q e) ⁻¹
          E = e ◁ b
          D′ = (comp-assoc t (p ∘ s) e) ⁻¹
          C′ = e ◁ (a ▷ t)
          total = (comp-assoc (s ∘ t) p e) ⁻¹
          inner = comp-assoc t s p
          exchange = (inverse-square₌ {t = C} {b = C′}
            {l = comp-assoc t q e} {r = comp-assoc t (p ∘ s) e}
            (whisker-mixed-One a t e)) ⁻¹
          pentagon = solve-pentagon (comp-assoc (s ∘ t) p e) A
            (e ◁ inner) (comp-assoc t (p ∘ s) e) (comp-assoc s p e ▷ t)
            (pentagon-whiskered t s p e) ∙
            comp₌-cong (id₌ A) (comp₌-cong (preWhisker-inverse (comp-assoc s p e) t) (id₌ D′))
      in comp₌-cong (id₌ total)
          ((postWhisker-comp₌ e inner ((a ▷ t) ∙ b)) ⁻¹ ∙
            comp₌-cong (id₌ (e ◁ inner)) ((postWhisker-comp₌ e (a ▷ t) b) ⁻¹)) ∙
        (comp₌-assoc total (e ◁ inner) (C′ ∙ E) ∙
        (comp₌-cong pentagon (id₌ (C′ ∙ E)) ∙
        ((comp₌-assoc A (B ∙ D′) (C′ ∙ E)) ⁻¹ ∙
        (comp₌-cong (id₌ A) (exchange-middle B C D E D′ C′ exchange) ∙
          comp₌-cong (id₌ A)
            (comp₌-cong (preWhisker-comp₌ ((comp-assoc s p e) ⁻¹) (e ◁ a) t)
              (id₌ (D ∙ E)))))))
```

## Cancelling routes

Restricting a pair of identifications along `s` and cancelling an inverse
pair inside the restricted route, and comparing two routes postcomposed with
a common triangle.

```agda
module _ {Γ : Context} where
  module _ {R X : CAT Γ} where
    open Terms.InContext X using (Term)

    cancel-restricted-route : {Y : CAT Γ} (s : MAP R X)
      {a b c : Term Y} {t z k l : MAP R Y}
      (W : b =₁ c) (V : a =₁ c)
      (A : (b ∘ s) =₁ t) (B : z =₁ (a ∘ s))
      (P′ : (c ∘ s) =₁ k) (N : k =₁ l)
      → ((N ∙ (P′ ∙ ((W ▷ s) ∙ A ⁻¹))) ∙ (A ∙ (((W ⁻¹ ∙ V) ▷ s) ∙ B))) =₂
          (N ∙ (P′ ∙ ((V ▷ s) ∙ B)))
    cancel-restricted-route s W V A B P′ N =
      let restricted = (W ⁻¹ ∙ V) ▷ s
          tail = restricted ∙ B
          cancelA = comp₌-cong (id₌ (W ▷ s)) (inv-comp-left A tail) ∙
            comp₌-assoc (W ▷ s) (A ⁻¹) (A ∙ tail)
          cancelW = comp₌-cong (preWhisker s ◁ comp-inv-left W V) (id₌ B) ∙
            (comp₌-cong ((preWhisker-comp₌ W (W ⁻¹ ∙ V) s) ⁻¹) (id₌ B) ∙
              (comp₌-assoc (W ▷ s) restricted B) ⁻¹)
          reassociate = comp₌-assoc N P′ ((W ▷ s) ∙ tail) ∙
            comp₌-cong (id₌ (N ∙ P′)) cancelA
      in comp₌-cong (id₌ N) (comp₌-cong (id₌ P′) cancelW) ∙
        (reassociate ∙
          (comp₌-assoc (N ∙ P′) ((W ▷ s) ∙ A ⁻¹) (A ∙ tail) ∙
            comp₌-cong ((comp₌-assoc N P′ ((W ▷ s) ∙ A ⁻¹)) ⁻¹) (id₌ (A ∙ tail))))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    postWhisker-cancel-routes : {Y Z : CAT Γ} (π : MAP Y Z)
      {u v w : Term Y} {z : Term Z}
      (output : v =₁ w) (input : u =₁ w) (b : (π ∘ w) =₁ z)
      {out : (π ∘ v) =₁ z} {inn : (π ∘ u) =₁ z}
      → (b ∙ (π ◁ output)) =₂ out → (b ∙ (π ◁ input)) =₂ inn
      → (out ∙ (π ◁ (output ⁻¹ ∙ input))) =₂ inn
    postWhisker-cancel-routes π output input b outLaw inLaw = inLaw ∙
      (comp₌-cong (id₌ b)
        ((postWhisker π ◁ comp-inv-left output input) ∙
          (postWhisker-comp₌ π output (output ⁻¹ ∙ input)) ⁻¹) ∙
      (comp₌-assoc b (π ◁ output) (π ◁ (output ⁻¹ ∙ input)) ∙
        comp₌-cong (outLaw ⁻¹) (id₌ (π ◁ (output ⁻¹ ∙ input)))))
```

## Restricted normalizations of projections

A normalization `n : π ∘ (H ∘ x) = y` restricts along `r` to
`π ∘ (H ∘ (x ∘ r)) = y ∘ r`. For normalizations built from a triangle
`β : π ∘ H = k`, the restriction is computed with the selected associator,
for a general, a composite and an identity value.

```agda
module _ {Γ : Context} where
  module _ {R T X : CAT Γ} where
    open Terms.InContext X using (Term)

    restricted-normalization : {Y Z : CAT Γ} (π : MAP Y Z) (H : Term Y)
      (x : MAP T X) {y : MAP T Z} (n : (π ∘ (H ∘ x)) =₁ y) (r : MAP R T)
      → (π ∘ (H ∘ (x ∘ r))) =₁ (y ∘ r)
    restricted-normalization π H x n r =
      restrict-triangle π (H ∘ x) n r ∙ (π ◁ comp-assoc r x H) ⁻¹

    simple-normalization-pre : {Y Z : CAT Γ}
      (π : MAP Y Z) (H : Term Y) (w : Term Z)
      (β : (π ∘ H) =₁ w) (u : MAP T X) (r : MAP R T)
      → restricted-normalization π H u (restrict-triangle π H β u) r =₂
          ((comp-assoc r u w) ⁻¹ ∙ restrict-triangle π H β (u ∘ r))
    simple-normalization-pre π H w β u r =
      let A = comp-assoc r u w
          old = restrict-triangle π H β u ▷ r
          corner = (comp-assoc r (H ∘ u) π) ⁻¹
          next = restrict-triangle π H β (u ∘ r)
          edge = π ◁ comp-assoc r u H
      in (inverse-square₌ {t = old ∙ corner} {b = next} {l = edge} {r = A}
        (restrict-triangle-twice π H β u r ∙ (comp₌-assoc A old corner) ⁻¹)) ⁻¹

    normalization-pre : {Y Z : CAT Γ} (π : MAP Y Z) (H : Term Y) (w : Term Z)
      (β : (π ∘ H) =₁ w) (x : MAP T X) (r : MAP R T)
      {y : MAP T Z} (n : (w ∘ x) =₁ y)
      → restricted-normalization π H x (n ∙ restrict-triangle π H β x) r =₂
          (((n ▷ r) ∙ (comp-assoc r x w) ⁻¹) ∙ restrict-triangle π H β (x ∘ r))
    normalization-pre π H w β x r n =
      let A = comp-assoc r x w
          old = restrict-triangle π H β x ▷ r
          next = restrict-triangle π H β (x ∘ r)
          corner = (comp-assoc r (H ∘ x) π) ⁻¹
          edge = π ◁ comp-assoc r x H
          core : ((old ∙ corner) ∙ edge ⁻¹) =₂ (A ⁻¹ ∙ next)
          core = simple-normalization-pre π H w β x r
      in (comp₌-assoc (n ▷ r) (A ⁻¹) next) ⁻¹ ∙
        (comp₌-cong (id₌ (n ▷ r)) core ∙
        (comp₌-assoc (n ▷ r) (old ∙ corner) (edge ⁻¹) ∙
        (comp₌-cong (comp₌-assoc (n ▷ r) old corner) (id₌ (edge ⁻¹)) ∙
          comp₌-cong (comp₌-cong (preWhisker-comp₌ n (restrict-triangle π H β x) r) (id₌ corner))
            (id₌ (edge ⁻¹)))))

    associator-corner : {Y Z : CAT Γ} (r : MAP R T) (u : MAP T X) (π : Term Y) (f : MAP Y Z)
      → ((comp-assoc u π f ▷ r) ∙ (comp-assoc r u (f ∘ π)) ⁻¹) =₂
          (((comp-assoc r (π ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u π) ⁻¹)) ∙ comp-assoc (u ∘ r) π f)
    associator-corner r u π f =
      comp₌-cong
        (comp₌-cong (id₌ ((comp-assoc r (π ∘ u) f) ⁻¹))
          ((postWhisker-inverse f (comp-assoc r u π)) ⁻¹))
        (id₌ (comp-assoc (u ∘ r) π f)) ∙
      ((comp₌-assoc ((comp-assoc r (π ∘ u) f) ⁻¹) ((f ◁ comp-assoc r u π) ⁻¹)
          (comp-assoc (u ∘ r) π f)) ⁻¹ ∙
        (pentagon-left-corner (comp-assoc (u ∘ r) π f) (comp-assoc r u (f ∘ π))
          (f ◁ comp-assoc r u π) (comp-assoc r (π ∘ u) f) (comp-assoc u π f ▷ r)
          (pentagon-whiskered r u π f)) ⁻¹)

  unit-corner : {R T E : CAT Γ} (r : MAP R T) (v : MAP T E)
    → ((comp-unitˡ v ▷ r) ∙ (comp-assoc r v (id E)) ⁻¹) =₂ (comp-unitˡ (v ∘ r))
  unit-corner r v = comp-inv-right (comp-unitˡ (v ∘ r)) (comp-assoc r v (id _)) ∙
    comp₌-cong ((left-unitor-comp r v) ⁻¹) (id₌ ((comp-assoc r v (id _)) ⁻¹))

  module _ {R T X : CAT Γ} where
    open Terms.InContext X using (Term)

    composite-normalization-pre : {Y Z W : CAT Γ}
      (π : MAP Y Z) (H : Term Y) (q : Term W) (f : MAP W Z)
      (β : (π ∘ H) =₁ (f ∘ q)) (u : MAP T X) (r : MAP R T)
      → restricted-normalization π H u (comp-assoc u q f ∙ restrict-triangle π H β u) r =₂
        (((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹)) ∙
          (comp-assoc (u ∘ r) q f ∙ restrict-triangle π H β (u ∘ r)))
    composite-normalization-pre π H q f β u r =
      comp₌-assoc ((comp-assoc r (q ∘ u) f) ⁻¹ ∙ (f ◁ (comp-assoc r u q) ⁻¹))
        (comp-assoc (u ∘ r) q f) (restrict-triangle π H β (u ∘ r)) ∙
      (comp₌-cong (associator-corner r u q f) (id₌ (restrict-triangle π H β (u ∘ r))) ∙
        normalization-pre π H (f ∘ q) β u r (comp-assoc u q f))

  identity-normalization-pre : {R T Y Z : CAT Γ}
    (π : MAP Y Z) (H : MAP Z Y) (β : (π ∘ H) =₁ (id Z)) (v : MAP T Z) (r : MAP R T)
    → restricted-normalization π H v (comp-unitˡ v ∙ restrict-triangle π H β v) r =₂
        (comp-unitˡ (v ∘ r) ∙ restrict-triangle π H β (v ∘ r))
  identity-normalization-pre π H β v r =
    comp₌-cong (unit-corner r v) (id₌ (restrict-triangle π H β (v ∘ r))) ∙
      normalization-pre π H (id _) β v r (comp-unitˡ v)
```

## Constants under restriction

A constant functor restricted along a composite, or along a functor
identified with a composite, agrees with successive restriction. The
comparisons between functors to `One` are unique by the terminal axiom.

```agda
module _ {Γ : Context} where
  const-pre-change : {Q R X A : CAT Γ} (x : Obj-abs A)
    (h : MAP R X) (t : MAP Q R) (s : MAP Q X) (δ : (h ∘ t) =₁ s)
    → (const-pre x s ∙ ((const x ◁ δ) ∙ comp-assoc t h (const x))) =₂
        (const-pre x t ∙ (const-pre x h ▷ t))
  const-pre-change {Q} {R} {X} x h t s δ =
    let u = terminal-identification (terminate X ∘ h) (terminate R)
        v = terminal-identification (terminate R ∘ t) (terminate Q)
        w = terminal-identification (terminate X ∘ s) (terminate Q)
        z = id₌ (terminate Q)
        tail = const-pre x t ∙ (const-pre x h ▷ t)
    in comp₌-unitˡ-One tail ∙
      (comp₌-cong (postWhisker-id₌ x (terminate Q)) (id₌ tail) ∙
        post-changed-restriction x (terminate X) h t s δ u v w z (terminal-unique₂ _ _))

  const-pre-iterated : {Q R X A : CAT Γ} (x : Obj-abs A) (h : MAP R X) (t : MAP Q R)
    → (const-pre x (h ∘ t) ∙ comp-assoc t h (const x)) =₂
        (const-pre x t ∙ (const-pre x h ▷ t))
  const-pre-iterated {Q} {R} {X} x h t =
    let u = terminal-identification (terminate X ∘ h) (terminate R)
        v = terminal-identification (terminate R ∘ t) (terminate Q)
        w = terminal-identification (terminate X ∘ (h ∘ t)) (terminate Q)
        z = id₌ (terminate Q)
        tail = const-pre x t ∙ (const-pre x h ▷ t)
    in comp₌-unitˡ-One tail ∙
      (comp₌-cong (postWhisker-id₌ x (terminate Q)) (id₌ tail) ∙
        post-iterated-restriction x (terminate X) h t u v w z (terminal-unique₂ _ _))
```

## Evaluating a functor identified with a composite

Given `β : A = f ∘ e`, the identification `N z : A ∘ z = f ∘ (e ∘ z)` is
natural in `z`, compatible with iterated restriction (by the whiskered
pentagon), and transported along a change of parameters `s ∘ t = q`.

```agda
module _ {Γ : Context} where
  module CompositeEvaluation {X Y Z C D : CAT Γ} (e : MAP Z C) (f : MAP C D)
    (A : MAP Z D) (β : A =₁ (f ∘ e)) (s : MAP Y Z) (t : MAP X Y)
    (q : MAP X Z) (parameter-law : (s ∘ t) =₁ q) where

    N : {W : CAT Γ} (z : MAP W Z) → (A ∘ z) =₁ (f ∘ (e ∘ z))
    N z = comp-assoc z e f ∙ (β ▷ z)

    natural : (N q ∙ (A ◁ parameter-law)) =₂ ((f ◁ (e ◁ parameter-law)) ∙ N (s ∘ t))
    natural = comp₌-assoc (f ◁ (e ◁ parameter-law)) (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) ∙
      (comp₌-cong (postWhisker-comp-One parameter-law e f) (id₌ (β ▷ (s ∘ t))) ∙
      ((comp₌-assoc (comp-assoc q e f) ((f ∘ e) ◁ parameter-law) (β ▷ (s ∘ t))) ⁻¹ ∙
      (comp₌-cong (id₌ (comp-assoc q e f)) (interchange β parameter-law) ∙
        comp₌-assoc (comp-assoc q e f) (β ▷ q) (A ◁ parameter-law))))

    iterated : (N (s ∘ t) ∙ comp-assoc t s A) =₂
      ((f ◁ comp-assoc t s e) ∙ (comp-assoc t (e ∘ s) f ∙ (N s ▷ t)))
    iterated = comp₌-cong (id₌ (f ◁ comp-assoc t s e))
        (comp₌-cong (id₌ (comp-assoc t (e ∘ s) f))
          ((preWhisker-comp₌ (comp-assoc s e f) (β ▷ s) t) ⁻¹)) ∙
      (comp₌-assoc (f ◁ comp-assoc t s e) (comp-assoc t (e ∘ s) f)
        ((comp-assoc s e f ▷ t) ∙ ((β ▷ s) ▷ t)) ∙
      (comp₌-assoc ((f ◁ comp-assoc t s e) ∙ comp-assoc t (e ∘ s) f)
        (comp-assoc s e f ▷ t) ((β ▷ s) ▷ t) ∙
      (comp₌-cong (pentagon-whiskered t s e f) (id₌ ((β ▷ s) ▷ t)) ∙
      ((comp₌-assoc (comp-assoc (s ∘ t) e f) (comp-assoc t s (f ∘ e)) ((β ▷ s) ▷ t)) ⁻¹ ∙
      (comp₌-cong (id₌ (comp-assoc (s ∘ t) e f)) ((preWhisker-comp-One β s t) ⁻¹) ∙
        comp₌-assoc (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) (comp-assoc t s A))))))

    V : (e ∘ q) =₁ ((e ∘ s) ∘ t)
    V = (comp-assoc t s e) ⁻¹ ∙ (e ◁ parameter-law ⁻¹)

    transport :
      ((f ◁ V) ∙ (N q ∙ ((A ◁ parameter-law) ∙ comp-assoc t s A))) =₂
      (comp-assoc t (e ∘ s) f ∙ (N s ▷ t))
    transport =
      let fa = f ◁ comp-assoc t s e
          fk = f ◁ (e ◁ parameter-law)
          result = comp-assoc t (e ∘ s) f ∙ (N s ▷ t)
          inverseV : (f ◁ V) =₂ (fa ⁻¹ ∙ fk ⁻¹)
          inverseV = comp₌-cong (postWhisker-inverse f (comp-assoc t s e))
            (postWhisker-inverse f (e ◁ parameter-law) ∙
              (postWhisker f ◁ postWhisker-inverse e parameter-law)) ∙
            postWhisker-comp₌ f ((comp-assoc t s e) ⁻¹) (e ◁ parameter-law ⁻¹)
          expanded : (N q ∙ ((A ◁ parameter-law) ∙ comp-assoc t s A)) =₂ (fk ∙ (fa ∙ result))
          expanded = comp₌-cong (id₌ fk) iterated ∙
            (comp₌-assoc fk (N (s ∘ t)) (comp-assoc t s A) ∙
            (comp₌-cong natural (id₌ (comp-assoc t s A)) ∙
              (comp₌-assoc (N q) (A ◁ parameter-law) (comp-assoc t s A)) ⁻¹))
      in inv-comp-left fa result ∙
        (comp₌-cong (id₌ (fa ⁻¹)) (inv-comp-left fk (fa ∙ result)) ∙
        (comp₌-assoc (fa ⁻¹) (fk ⁻¹) (fk ∙ (fa ∙ result)) ∙
        comp₌-cong inverseV expanded))
```
