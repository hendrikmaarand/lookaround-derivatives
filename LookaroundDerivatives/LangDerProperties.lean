import LookaroundDerivatives.Language
import LookaroundDerivatives.LangOpProperties


theorem derLBhd_after_der {l : Lang α}
                          : ∀ (a b : α), derLBhd b (der a l) ≐ ∅ := by
  intro a b t
  simp [derLBhd, der, behind, empty]

theorem derLBhd_after_derLAhd {l : Lang α}
                              : ∀ (a b : α), derLBhd b (derLAhd a l) ≐ ∅ := by
  intro a b t
  simp [derLBhd, derLAhd, behind, empty]

theorem der_after_derLAhd {l : Lang α}
                          : ∀ (a b : α), der b (derLAhd a l) ≐ ∅ := by
  intro a b t
  simp [der, derLAhd, mtch, empty]


------------------------------------------------------------

theorem nlbl_union {k l : Lang α} : nlbl (k ∪ l) ↔ nlbl k ∨ nlbl l := by
  rw [nlbl, union, nlbl, nlbl]

theorem nlbl_concat {k l : Lang α} : nlbl (k ⊙ l) ↔ nlbl k ∧ nlbl l := by
  rw [nlbl, concat, nlbl, nlbl]
  apply Iff.intro
  . rw [behind, mtch, ahead]
    intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    simp at mt_eq
    have ⟨m₁_eq, m₂_eq⟩ := mt_eq
    subst m₁ m₂
    exact ⟨k_m, l_m⟩

  . intro ⟨k_m, l_m⟩
    exists [], []

theorem nlbl_inter {k l : Lang α} : nlbl (k ∩ l) ↔ nlbl k ∧ nlbl l := by
  rw [nlbl, intersection, nlbl, nlbl]

theorem nlbl_diff {k l : Lang α} : nlbl (k \ l) ↔ nlbl k ∧ ¬ nlbl l := by
  rw [nlbl, diff, nlbl, nlbl]

theorem nlbl_kstar {l : Lang α} : nlbl (kstar l) ↔ True := by
  simp [nlbl, kstar]
  apply StarLFP.base
  rw [unit, mtch]

theorem nlbl_lookbehind {l : Lang α} : nlbl (◁ l) ↔ nlbl l := by
  rw [nlbl, lookbehind, mtch, behind, ahead, nlbl]
  simp

theorem nlbl_lookahead {l : Lang α} : nlbl (▷ l) ↔ nlbl l := by
  rw [nlbl, lookahead, mtch, behind, ahead, nlbl]
  simp



---------------------------------------------------------

theorem nlbl_congr {l l' : Lang α} (eq : l ≐ l') : nlbl l ↔ nlbl l' := by
  rw [nlbl, nlbl]
  rw [eq]


theorem derLBhd_congr {l l' : Lang α} (eq : l ≐ l') : ∀ (a : α), derLBhd a l ≐ derLBhd a l' := by
  intro a t
  rw [derLBhd, derLBhd]
  rw [eq]

theorem wderLBhd_congr {l l' : Lang α} (eq : l ≐ l') : ∀ w, wderLBhd w l ≐ wderLBhd w l' := by
  intro w t
  match w with
  | [] => rw [wderLBhd, wderLBhd, eq]
  | a :: w =>
      rw [wderLBhd, wderLBhd]
      rw [wderLBhd_congr (derLBhd_congr eq a)]


theorem der_congr {l l' : Lang α} (eq : l ≐ l') : ∀ a, der a l ≐ der a l' := by
  intro a t
  rw [der, der]
  rw [eq]

theorem wder_congr {l l' : Lang α} (eq : l ≐ l') : ∀ w, wder w l ≐ wder w l' := by
  intro w t
  match w with
  | [] => rw [wder, wder, eq]
  | a :: w =>
      rw [wder, wder]
      rw [wder_congr (der_congr eq a)]


theorem derLAhd_congr {l l' : Lang α} (eq : l ≐ l') : ∀ a, derLAhd a l ≐ derLAhd a l' := by
  intro a t
  rw [derLAhd, derLAhd]
  rw [eq]

theorem wderLAhd_congr {l l' : Lang α} (eq : l ≐ l') : ∀ w, wderLAhd w l ≐ wderLAhd w l' := by
  intro w t
  match w with
  | [] => rw [wderLAhd, wderLAhd, eq]
  | a :: w =>
      rw [wderLAhd, wderLAhd]
      rw [wderLAhd_congr (derLAhd_congr eq a)]




theorem tder_congr {l l' : Lang α} (eq : l ≐ l') : ∀ (t : Triple α), tder t l ≐ tder t l' := by
  intro ⟨x, y, z⟩  u
  rw [tder, tder]
  simp [behind, mtch, ahead]
  rw [wderLAhd_congr (wder_congr (wderLBhd_congr eq x) y) z]


theorem xder_congr {l l' : Lang α} (eq : l ≐ l') : ∀ a, xder a l ≐ xder a l' := by
  intro a t
  rw [xder, xder]
  rw [union_congr (derLBhd_congr eq a)
                  (union_congr (der_congr eq a) (derLAhd_congr eq a))]


theorem wxder_congr {l l' : Lang α} (eq : l ≐ l') : ∀ w, wxder w l ≐ wxder w l' := by
  intro w t
  match w with
  | [] => rw [wxder, wxder, eq]
  | a :: w => rw [wxder, wxder]
              rw [wxder_congr (xder_congr eq a) w]



---------------------------------------------------------
-- derivatives of `$ b`

theorem derLBhd_symb {α} (b : α) : ∀ (a : α),
    derLBhd a ($ b) ≐ $ b := by
  intro a t
  rw [derLBhd, symb, mtch, symb]

theorem der_symb {α} [DecidableEq α] (b : α) : ∀ (a : α),
    der a ($ b) ≐ if a = b then ◁ 𝟙 else ∅ := by
  intro a
  if h : a = b then
    simp [h]
    intro t
    rw [der, symb, mtch]
    rw[lookbehind, unit, mtch]
    simp [and_comm]
  else
    simp [h]
    intro t
    rw [der, symb, mtch]
    rw [empty]
    apply Iff.intro
    . intro ⟨bt_eq, p⟩
      simp at p
      exact h p.1

    . intro bot; contradiction

theorem derLAhd_symb {α} (b : α) : ∀ (a : α),
    derLAhd a ($ b) ≐ ∅ := by
  intro a t
  rw [derLAhd, symb, mtch, empty]
  simp


------------------------------------------------------------
-- derivatives of `∅`

theorem derLBhd_empty : ∀ (a : α), derLBhd a ∅ ≐ ∅ := by
  intro a t
  rw [derLBhd, empty, empty]

theorem der_empty : ∀ (a : α), der a ∅ ≐ ∅ := by
  intro a t
  rw [der, empty, empty]
  simp

theorem derLAhd_empty : ∀ (a : α), derLAhd a ∅ ≐ ∅ := by
  intro a t
  rw [derLAhd, empty, empty]
  simp


------------------------------------------------------------
-- derivatives of `k ∪ l`

theorem derLBhd_union {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ∪ l) ≐ derLBhd a k ∪ derLBhd a l := by
  intro a t
  rw [derLBhd, union, union, derLBhd, derLBhd]

theorem der_union {k l : Lang α} : ∀ (a : α),
    der a (k ∪ l) ≐ der a k ∪ der a l := by
  intro a t
  rw [der, union, union, der, der]
  rw [and_or_left]


theorem derLAhd_union {k l : Lang α} : ∀ (a : α),
    derLAhd a (k ∪ l) ≐ derLAhd a k ∪ derLAhd a l := by
  intro a t
  rw [derLAhd, union, union, derLAhd, derLAhd]
  rw [and_or_left, and_or_left]


------------------------------------------------------------
-- derivatives of `𝟙`

theorem derLBhd_unit : ∀ (a : α), derLBhd a 𝟙 ≐ 𝟙 := by
  intro a t
  rw [derLBhd, unit, mtch, unit]

theorem der_unit : ∀ (a : α), der a 𝟙 ≐ ∅ := by
  intro a t
  rw [der, unit, mtch]
  rw [empty]
  simp

theorem derLAhd_unit : ∀ (a : α), derLAhd a 𝟙 ≐ ◁ 𝟙 := by
  intro a t
  rw [derLAhd, unit, mtch, lookbehind, unit, mtch]
  simp [and_comm]


------------------------------------------------------------
-- derivatives of `k ⊙ l`

theorem derLBhd_concat {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ⊙ l) ≐ derLBhd a k ⊙ derLBhd a l := by
  intro a t
  rw [derLBhd, concat, concat]
  rw [behind, mtch, ahead]

  apply Iff.intro
  . intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    exists m₁, m₂

  . intro ⟨m₁, m₂, mt_eq, dk_m, dl_m⟩
    exists m₁, m₂

theorem der_concat {k l : Lang α} : ∀ (a : α),
    der a (k ⊙ l) ≐ (der a k ⊙ derLBhd a l) ∪ (derLAhd a k ⊙ der a l) := by
  intro a t
  apply Iff.intro
  . intro kl
    rw [der, concat] at kl
    rw [mtch, behind, ahead] at kl
    have ⟨bt_eq, m₁, m₂, mt_eq, k_m, l_m⟩ := kl

    apply Or.elim (List.cons_eq_append_iff.mp mt_eq)
    . intro ⟨m1_eq, m2_eq⟩
      apply Or.inr
      rw [concat, bt_eq]
      rw [m1_eq, m2_eq] at l_m k_m
      exists [], mtch t

    . intro ⟨m₁', m1_eq, mt_eq⟩
      rw [m1_eq] at k_m l_m
      apply Or.inl
      rw [concat, bt_eq, mt_eq]
      exists m₁', m₂

  . intro kl
    rw [union] at kl
    apply Or.elim kl
    . intro kl

      rw [concat] at kl
      have ⟨m₁, m₂, mt_eq, dk, dl⟩ := kl

      rw [der, behind, mtch, ahead] at dk
      rw [derLBhd, behind, mtch, ahead, dk.1] at dl
      rw [der, concat, behind, mtch, ahead, mt_eq]

      apply And.intro dk.1
      exists a :: m₁, m₂
      exact ⟨rfl, dk.2, dl⟩

    . intro kl
      rw [concat] at kl
      have ⟨m₁, m₂, mt_eq, dk, dl⟩ := kl

      rw [derLAhd, behind, mtch, ahead] at dk
      rw [der, behind, mtch, ahead, dk.1] at dl
      rw [der, concat, behind, mtch, ahead, mt_eq, dk.2.1]

      apply And.intro dk.1
      exists [], a :: m₂
      exact ⟨rfl, dk.2.2, dl.2⟩


theorem derLAhd_concat {k l : Lang α} : ∀ (a : α),
    derLAhd a (k ⊙ l) ≐ derLAhd a k ⊙ derLAhd a l := by
  intro a t
  rw [derLAhd, concat, concat]
  rw [behind, mtch, ahead]

  apply Iff.intro
  . intro ⟨bt_eq, mt_eq, m₁, m₂, m12_eq, ⟨k_m, l_m⟩⟩
    simp at m12_eq
    have ⟨m₁_eq, m₂_eq⟩ := m12_eq
    subst m₁ m₂

    exists [], []
    apply And.intro mt_eq
    rw [derLAhd, derLAhd, behind, behind, mtch, mtch, ahead, ahead]
    rw [bt_eq]
    simp
    exact ⟨k_m, l_m⟩

  . intro ⟨m₁, m₂, mt_eq, dk_m, dl_m⟩

    rw [derLAhd, behind, mtch, ahead] at dk_m
    have ⟨bt_eq, m₁_eq, k_m⟩ := dk_m

    rw [derLAhd, behind, mtch, ahead] at dl_m
    have ⟨bt_m₁_eq, m₂_eq, l_m⟩ := dl_m

    subst m₁_eq m₂_eq
    rw [bt_eq, mt_eq] at *
    simp at *

    exists [], []


--------------------------------------------------------------
-- derivatives of `𝕋`

theorem derLBhd_top : ∀ (a : α),
    derLBhd a 𝕋 ≐ 𝕋 := by
  intro a t
  rw [derLBhd, top, top]

theorem der_top : ∀ (a : α),
    der a 𝕋 ≐ (◁ 𝟙) ⊙ 𝕋 := by
  intro a t
  rw [der, top, concat]
  simp [top, lookbehind, unit]
  apply Iff.intro
  . intro bt_eq
    exists [], mtch t
  . intro ⟨_, _, _, _, mt_eq'⟩
    rw [behind, mtch] at mt_eq'
    exact mt_eq'

theorem derLAhd_top : ∀ (a : α),
    derLAhd a 𝕋 ≐ ◁ 𝟙 := by
  intro a t
  rw [derLAhd, top, lookbehind, unit, mtch]
  simp [and_comm]


------------------------------------------------------------
-- derivatives of `k ∩ l`

theorem derLBhd_inter {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ∩ l) ≐ derLBhd a k ∩ derLBhd a l := by
  intro a t
  rw [derLBhd, intersection, intersection, derLBhd, derLBhd]


theorem der_inter {k l : Lang α} : ∀ (a : α),
    der a (k ∩ l) ≐ der a k ∩ der a l := by
  intro a t
  rw [der, intersection, intersection, der, der]
  rw [and_and_and_comm, and_self]

theorem derLAhd_inter {k l : Lang α} : ∀ (a : α),
    derLAhd a (k ∩ l) ≐ derLAhd a k ∩ derLAhd a l := by
  intro a t
  rw [derLAhd, intersection, intersection, derLAhd, derLAhd]
  simp [and_and_and_comm, and_self]


---------------------------------------------------------------
-- derivatives of `k \ l`

theorem derLBhd_diff {k l : Lang α} : ∀ (a : α),
    derLBhd a (k \ l) ≐ derLBhd a k \ derLBhd a l := by
  intro a t
  rw [derLBhd, diff, diff, derLBhd, derLBhd]


theorem der_diff {k l : Lang α} : ∀ (a : α),
    der a (k \ l) ≐ der a k \ der a l := by
  intro a t
  rw [der, diff, diff, der, der]
  apply Iff.intro
  . intro ⟨bt, dk, dl⟩
    simp only [bt, true_and]
    exact ⟨dk, dl⟩

  . intro ⟨⟨bt, dk⟩, dl⟩
    simp [bt] at dl
    exact ⟨bt, dk, dl⟩

theorem derLAhd_diff {k l : Lang α} : ∀ (a : α),
    derLAhd a (k \ l) ≐ derLAhd a k \ derLAhd a l := by
  intro a t
  rw [derLAhd, diff, diff, derLAhd, derLAhd]
  simp
  apply Iff.intro
  . intro ⟨bt_eq, mt_eq, k_m, l_m⟩
    exact ⟨⟨bt_eq, mt_eq, k_m⟩, λ _ _ => l_m⟩

  . intro ⟨⟨bt_eq, mt_eq, k_m⟩, p⟩
    exact ⟨bt_eq, mt_eq, k_m, p bt_eq mt_eq⟩



---------------------------------------------------------------
-- derivatives of Kleene star `l⋆`

theorem derLBhd_StarLFP (a : α) (l : Lang α)(tr : Triple α)
                  {tr' : Triple α} (eq : tr' = (a :: behind tr, mtch tr, ahead tr))
                  : StarLFP l             tr' ↔
                    StarLFP (derLBhd a l) tr := by

  apply Iff.intro
  . intro ls_mem
    induction ls_mem generalizing tr with
    | @base t u_m =>
        rw [unit, eq, mtch] at u_m
        exact StarLFP.base u_m
    | @step lb m₁ m₂ la m eq' l_m ls_m ih =>
        injection eq with p q
        injection q  with q r
        rw [eq'] at q
        rw [p] at l_m

        have w := derLBhd_mem a l (behind tr, m₁, m₂ ++ la)
        rw [behind, mtch, ahead] at w
        rw [←w] at l_m

        rw [triple_eta tr]
        rw [←q]
        rw [r] at l_m

        have ih' := ih (behind tr ++ m₁, m₂, ahead tr)
        rw [behind, mtch, ahead, p, r] at ih'

        exact StarLFP.step rfl l_m (ih' rfl)


  . intro ls_mem'
    induction ls_mem' generalizing tr' with
    | @base t u_m =>
        rw [unit] at u_m
        rw [eq]
        apply StarLFP.base
        rw [unit, mtch]
        exact u_m

    | @step lb m₁ m₂ la m eq' l_m' ls_m' ih =>
        rw [behind, mtch, ahead] at eq
        rw [eq, eq']
        rw [derLBhd_mem, behind, mtch, ahead] at l_m'

        rw [behind, mtch, ahead] at ih
        have ih' := @ih (a :: lb ++ m₁, m₂, la)

        apply StarLFP.step rfl l_m' (ih' rfl)


theorem derLBhd_kstar (a : α) (l : Lang α) :
    derLBhd a l⋆ ≐ (derLBhd a l)⋆ := by
  intro t

  have lem : StarLFP l (a :: behind t, mtch t, ahead t) ↔ StarLFP (derLBhd a l) t :=
    derLBhd_StarLFP a l t rfl

  rw [kstar, derLBhd, kstar]
  rw [lem]


theorem derLAhd_kstar {l : Lang α} : ∀ (a : α), derLAhd a l⋆ ≐ ◁ 𝟙 := by
  intro a t
  rw [derLAhd, lookbehind, unit, mtch]

  apply Iff.intro
  . intro ⟨bt_eq, mt_eq, ls_m⟩
    exact ⟨mt_eq, bt_eq⟩

  . intro ⟨mt_eq, bt_eq⟩
    exact ⟨bt_eq, mt_eq, StarLFP.base (by rw [unit, mtch])⟩



theorem der_help {α : Type}
                 (a : α) (l : Lang α)
                 (m la : List α)
                 {tr : Triple α} (tr_eq  : tr  = ([], a :: m, la))
                 : StarLFP l tr → ∃ (m₁ m₂ : List α),
                                    m = m₁ ++ m₂ ∧
                                    der a l ([], m₁, m₂ ++ la) ∧
                                    StarLFP (derLBhd a l) (m₁, m₂, la) := by
  intro ls_mem
  induction ls_mem with
  | @base t u_m =>
      rw [unit] at u_m
      rw [triple_eta t, u_m] at tr_eq
      injections

  | @step lb' m₁' m₂' la' m' eq l_m ls_m ih =>
      injections lb'_eq _ m'_eq la'_eq
      subst lb'_eq m'_eq la'_eq

      rw  [List.cons_eq_append_iff] at eq
      apply Or.elim eq
      . intro ⟨eq1, eq2⟩
        subst eq1 eq2
        apply ih
        rfl

      . intro ⟨x, m₁'_eq, m_eq⟩
        subst m₁'_eq m_eq

        exists x, m₂'
        simp
        apply And.intro
        . rw [der_mem a l ([], x, m₂' ++ la') rfl]
          exact l_m
        . simp at ls_m
          rw [derLBhd_StarLFP a l (x, m₂', la') (by rw [behind, mtch, ahead])] at ls_m
          exact ls_m

theorem der_help' {α : Type}
                  (a : α) (l : Lang α)
                  (m la : List α)
                  {tr : Triple α} (tr_eq  : tr  = ([], a :: m, la))
                  (h : ∃ (m₁ m₂ : List α),
                         m = m₁ ++ m₂ ∧
                         der a l ([], m₁, m₂ ++ la) ∧
                         StarLFP (derLBhd a l) (m₁, m₂, la))
                  : StarLFP l tr := by
  have ⟨m₁, m₂, mt_eq, dl_m, ls_m⟩ := h
  rw [tr_eq, mt_eq]

  have l_m := der_mem a l ([], m₁, m₂ ++ la) rfl
  rw [l_m, behind, mtch, ahead] at dl_m

  have lbhd_s := derLBhd_StarLFP a l (m₁, m₂, la) rfl
  rw [behind, mtch, ahead] at lbhd_s
  rw [←lbhd_s] at ls_m

  exact StarLFP.step rfl dl_m ls_m


theorem der_kstar {l : Lang α} : ∀ (a : α),
    der a l⋆ ≐ (der a l) ⊙ (derLBhd a l)⋆ := by
  intro a t
  rw [kstar, der, kstar, concat]
  apply Iff.intro
  . intro ⟨bt_eq, p⟩
    simp [bt_eq]
    exact der_help a l (mtch t) (ahead t) rfl p

  . intro ⟨m₁, m₂, mt_eq, dl_m, ls_m⟩

    have bt_eq := der_mem' dl_m
    rw [behind] at bt_eq
    simp [bt_eq]
    simp [bt_eq] at dl_m ls_m

    exact der_help' a l (mtch t) (ahead t) rfl ⟨m₁, m₂, mt_eq, dl_m, ls_m⟩


---------------------------------------------------------------
-- derivatives of lookbehinds `◁ l`

theorem derLBhd_lookbehind {l : Lang α} : ∀ (a : α),
    derLBhd a (◁ l) ≐ ◁ (der a l) := by
  intro a t
  rw [derLBhd, lookbehind, lookbehind, der]
  rw [behind, mtch, ahead, behind, mtch, ahead]
  simp

theorem der_lookbehind {l : Lang α} : ∀ (a : α),
    der a (◁ l) ≐ ∅ := by
  intro a t
  rw [der, lookbehind, mtch, ahead, empty]
  simp

theorem derLAhd_lookbehind {l : Lang α} : ∀ (a : α),
    derLAhd a (◁ l) ≐ derLAhd a l := by
  intro a t
  rw [derLAhd, lookbehind, derLAhd, behind, mtch, ahead]
  simp


---------------------------------------------------------------
-- derivatives of lookaheads `▷ l`

theorem derLBhd_lookahead {l : Lang α} : ∀ (a : α),
    derLBhd a (▷ l) ≐ ▷ (derLBhd a l) := by
  intro a t
  rw [derLBhd, lookahead, lookahead, derLBhd]
  rw [behind, mtch, ahead, behind, mtch, ahead]

theorem der_lookahead {l : Lang α} : ∀ (a : α),
    der a (▷ l) ≐ ∅ := by
  intro a t
  rw [der, lookahead, behind, mtch, ahead, empty]
  simp

theorem derLAhd_lookahead {l : Lang α} : ∀ (a : α),
    derLAhd a (▷ l) ≐ ▷ (der a l) := by
  intro a t
  rw [derLAhd, lookahead, lookahead, der]
  rw [behind, mtch, ahead, behind, mtch, ahead]
  simp [←and_assoc, and_comm]
