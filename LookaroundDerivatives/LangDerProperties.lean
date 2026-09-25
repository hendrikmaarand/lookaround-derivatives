import LookaroundDerivatives.Language
import LookaroundDerivatives.LangOpProperties

namespace Lang
open Triple


theorem derLBhd_after_der {l : Lang α}
                          : ∀ (a b : α), derLBhd b (der a l) = ∅ := by
  intro a b
  ext t
  simp [derLBhd, der, behind, empty]

theorem derLBhd_after_derLAhd {l : Lang α}
                              : ∀ (a b : α), derLBhd b (derLAhd a l) = ∅ := by
  intro a b
  ext t
  simp [derLBhd, derLAhd, behind, empty]

theorem der_after_derLAhd {l : Lang α}
                          : ∀ (a b : α), der b (derLAhd a l) = ∅ := by
  intro a b
  ext t
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
  simp [nlbl]
  apply unit_sub_kstar
  rw [unit, mtch]

theorem nlbl_lookbehind {l : Lang α} : nlbl (◁ l) ↔ nlbl l := by
  rw [nlbl, lookbehind, mtch, behind, ahead, nlbl]
  simp

theorem nlbl_lookahead {l : Lang α} : nlbl (▷ l) ↔ nlbl l := by
  rw [nlbl, lookahead, mtch, behind, ahead, nlbl]
  simp



---------------------------------------------------------

-- derivatives of `$ b`

theorem derLBhd_symb {α} (b : α) : ∀ (a : α),
    derLBhd a ($ b) = $ b := by
  intro a
  ext t
  rw [derLBhd, symb, mtch, symb]

theorem der_symb {α} [DecidableEq α] (b : α) : ∀ (a : α),
    der a ($ b) = if a = b then ◁ 𝟙 else ∅ := by
  intro a
  if h : a = b then
    simp [h]
    ext t
    rw [der, symb, mtch]
    rw[lookbehind, unit, mtch]
    simp [and_comm]
  else
    simp [h]
    ext t
    rw [der, symb, mtch]
    rw [empty]
    apply Iff.intro
    . intro ⟨bt_eq, p⟩
      simp at p
      exact h p.1

    . intro bot; contradiction

theorem derLAhd_symb {α} (b : α) : ∀ (a : α),
    derLAhd a ($ b) = ∅ := by
  intro a
  ext t
  rw [derLAhd, symb, mtch, empty]
  simp


------------------------------------------------------------
-- derivatives of `∅`

theorem derLBhd_empty : ∀ (a : α), derLBhd a ∅ = ∅ := by
  intro a
  ext t
  rw [derLBhd, empty, empty]

theorem der_empty : ∀ (a : α), der a ∅ = ∅ := by
  intro a
  ext t
  rw [der, empty, empty]
  simp

theorem derLAhd_empty : ∀ (a : α), derLAhd a ∅ = ∅ := by
  intro a
  ext t
  rw [derLAhd, empty, empty]
  simp


------------------------------------------------------------
-- derivatives of `k ∪ l`

theorem derLBhd_union {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ∪ l) = derLBhd a k ∪ derLBhd a l := by
  intro a
  ext t
  rw [derLBhd, union, union, derLBhd, derLBhd]

theorem der_union {k l : Lang α} : ∀ (a : α),
    der a (k ∪ l) = der a k ∪ der a l := by
  intro a
  ext t
  rw [der, union, union, der, der]
  rw [and_or_left]


theorem derLAhd_union {k l : Lang α} : ∀ (a : α),
    derLAhd a (k ∪ l) = derLAhd a k ∪ derLAhd a l := by
  intro a
  ext t
  rw [derLAhd, union, union, derLAhd, derLAhd]
  rw [and_or_left, and_or_left]


------------------------------------------------------------
-- derivatives of `𝟙`

theorem derLBhd_unit : ∀ (a : α), derLBhd a 𝟙 = 𝟙 := by
  intro a
  ext t
  rw [derLBhd, unit, mtch, unit]

theorem der_unit : ∀ (a : α), der a 𝟙 = ∅ := by
  intro a
  ext t
  rw [der, unit, mtch]
  rw [empty]
  simp

theorem derLAhd_unit : ∀ (a : α), derLAhd a 𝟙 = ◁ 𝟙 := by
  intro a
  ext t
  rw [derLAhd, unit, mtch, lookbehind, unit, mtch]
  simp [and_comm]


------------------------------------------------------------
-- derivatives of `k ⊙ l`

theorem derLBhd_concat {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ⊙ l) = derLBhd a k ⊙ derLBhd a l := by
  intro a
  ext t
  rw [derLBhd, concat, concat]
  rw [behind, mtch, ahead]

  apply Iff.intro
  . intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    exists m₁, m₂

  . intro ⟨m₁, m₂, mt_eq, dk_m, dl_m⟩
    exists m₁, m₂

theorem der_concat {k l : Lang α} : ∀ (a : α),
    der a (k ⊙ l) = (der a k ⊙ derLBhd a l) ∪ (derLAhd a k ⊙ der a l) := by
  intro a
  ext t
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
    derLAhd a (k ⊙ l) = derLAhd a k ⊙ derLAhd a l := by
  intro a
  ext t
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
    derLBhd a 𝕋 = 𝕋 := by
  intro a
  ext t
  rw [derLBhd, top, top]

theorem der_top : ∀ (a : α),
    der a 𝕋 = (◁ 𝟙) ⊙ 𝕋 := by
  intro a
  ext t
  rw [der, top, concat]
  simp [top, lookbehind, unit]
  apply Iff.intro
  . intro bt_eq
    exists [], mtch t
  . intro ⟨_, _, _, _, mt_eq'⟩
    rw [behind, mtch] at mt_eq'
    exact mt_eq'

theorem derLAhd_top : ∀ (a : α),
    derLAhd a 𝕋 = ◁ 𝟙 := by
  intro a
  ext t
  rw [derLAhd, top, lookbehind, unit, mtch]
  simp [and_comm]


------------------------------------------------------------
-- derivatives of `k ∩ l`

theorem derLBhd_inter {k l : Lang α} : ∀ (a : α),
    derLBhd a (k ∩ l) = derLBhd a k ∩ derLBhd a l := by
  intro a
  ext t
  rw [derLBhd, intersection, intersection, derLBhd, derLBhd]


theorem der_inter {k l : Lang α} : ∀ (a : α),
    der a (k ∩ l) = der a k ∩ der a l := by
  intro a
  ext t
  rw [der, intersection, intersection, der, der]
  rw [and_and_and_comm, and_self]

theorem derLAhd_inter {k l : Lang α} : ∀ (a : α),
    derLAhd a (k ∩ l) = derLAhd a k ∩ derLAhd a l := by
  intro a
  ext t
  rw [derLAhd, intersection, intersection, derLAhd, derLAhd]
  rw [and_and_and_comm, and_self, and_and_and_comm, and_self]


---------------------------------------------------------------
-- derivatives of `k \ l`

theorem derLBhd_diff {k l : Lang α} : ∀ (a : α),
    derLBhd a (k \ l) = derLBhd a k \ derLBhd a l := by
  intro a
  ext t
  rw [derLBhd, diff, diff, derLBhd, derLBhd]


theorem der_diff {k l : Lang α} : ∀ (a : α),
    der a (k \ l) = der a k \ der a l := by
  intro a
  ext t
  rw [der, diff, diff, der, der]
  apply Iff.intro
  . intro ⟨bt, dk, dl⟩
    simp only [bt, true_and]
    exact ⟨dk, dl⟩

  . intro ⟨⟨bt, dk⟩, dl⟩
    simp [bt] at dl
    exact ⟨bt, dk, dl⟩

theorem derLAhd_diff {k l : Lang α} : ∀ (a : α),
    derLAhd a (k \ l) = derLAhd a k \ derLAhd a l := by
  intro a
  ext t
  rw [derLAhd, diff, diff, derLAhd, derLAhd]
  simp
  apply Iff.intro
  . intro ⟨bt_eq, mt_eq, k_m, l_m⟩
    exact ⟨⟨bt_eq, mt_eq, k_m⟩, λ _ _ => l_m⟩

  . intro ⟨⟨bt_eq, mt_eq, k_m⟩, p⟩
    exact ⟨bt_eq, mt_eq, k_m, p bt_eq mt_eq⟩



---------------------------------------------------------------
-- derivatives of Kleene star `l⋆`

theorem derLBhd_kstar (a : α) (l : Lang α) :
    derLBhd a l⋆ = (derLBhd a l)⋆ := by
  apply sub_antisymm
  . -- Invariant: dropping `a` from the lookbehind of a triple of `l⋆`
    -- gives a triple of `(derLBhd a l)⋆`.
    have inv : l⋆ ⊆ (λ t => ∀ {lb}, behind t = a :: lb →
                              (derLBhd a l)⋆ (lb, mtch t, ahead t)) := by
      apply kstar_lowerbound
      intro t p lb eq
      rcases p with u_m | ⟨m₁, m₂, mt_eq, l_m, y_m⟩
      . exact unit_sub_kstar u_m
      . rw [eq] at l_m y_m
        apply concat_kstar_sub
        exact ⟨m₁, m₂, mt_eq, l_m, y_m rfl⟩
    intro t ls_m
    exact inv ls_m rfl
  . apply kstar_lowerbound
    intro t p
    rcases p with u_m | dl_m
    . exact unit_sub_kstar u_m
    . rw [←derLBhd_concat] at dl_m
      exact concat_kstar_sub dl_m


theorem der_kstar {l : Lang α} : ∀ (a : α),
    der a l⋆ = (der a l) ⊙ (derLBhd a l)⋆ := by
  intro a
  apply sub_antisymm
  . -- Invariant: dropping `a` from the match of a triple of `l⋆` with empty
    -- lookbehind gives a triple of `der a l ⊙ (derLBhd a l)⋆`.
    have inv : l⋆ ⊆ (λ t => ∀ {m la}, t = ([], a :: m, la) →
                              (der a l ⊙ (derLBhd a l)⋆) ([], m, la)) := by
      apply kstar_induct
      intro t p m la eq
      subst eq
      rcases p with u_m | ⟨m₁, m₂, mt_eq, l_m, ls_m, y_m⟩
      . rw [unit, mtch] at u_m
        injections
      . rcases List.cons_eq_append_iff.mp mt_eq with ⟨m₁_eq, m₂_eq⟩ | ⟨x, m₁_eq, m_eq⟩
        . subst m₁_eq m₂_eq
          exact y_m rfl
        . subst m₁_eq m_eq
          rw [←derLBhd_kstar]
          exact ⟨x, m₂, rfl, ⟨rfl, l_m⟩, ls_m⟩
    intro t ⟨bt_eq, ls_m⟩
    rw [eta t, bt_eq]
    exact inv ls_m rfl
  . intro t dl_m
    rw [←derLBhd_kstar] at dl_m
    have ⟨bt_eq, ll_m⟩ : der a (l ⊙ l⋆) t := by
      rw [der_concat]
      exact Or.inl dl_m
    rw [der]
    exact ⟨bt_eq, concat_kstar_sub ll_m⟩


theorem derLAhd_kstar {l : Lang α} : ∀ (a : α), derLAhd a l⋆ = ◁ 𝟙 := by
  intro a
  ext t
  rw [derLAhd, lookbehind, unit, mtch]

  apply Iff.intro
  . intro ⟨bt_eq, mt_eq, ls_m⟩
    exact ⟨mt_eq, bt_eq⟩

  . intro ⟨mt_eq, bt_eq⟩
    exact ⟨bt_eq, mt_eq, unit_sub_kstar (by rw [unit, mtch])⟩


---------------------------------------------------------------
-- derivatives of lookbehinds `◁ l`

theorem derLBhd_lookbehind {l : Lang α} : ∀ (a : α),
    derLBhd a (◁ l) = ◁ (der a l) := by
  intro a
  ext t
  rw [derLBhd, lookbehind, lookbehind, der]
  rw [behind, mtch, ahead, behind, mtch, ahead]
  simp

theorem der_lookbehind {l : Lang α} : ∀ (a : α),
    der a (◁ l) = ∅ := by
  intro a
  ext t
  rw [der, lookbehind, mtch, ahead, empty]
  simp

theorem derLAhd_lookbehind {l : Lang α} : ∀ (a : α),
    derLAhd a (◁ l) = derLAhd a l := by
  intro a
  ext t
  rw [derLAhd, lookbehind, derLAhd, behind, mtch, ahead]
  simp


---------------------------------------------------------------
-- derivatives of lookaheads `▷ l`

theorem derLBhd_lookahead {l : Lang α} : ∀ (a : α),
    derLBhd a (▷ l) = ▷ (derLBhd a l) := by
  intro a
  ext t
  rw [derLBhd, lookahead, lookahead, derLBhd]
  rw [behind, mtch, ahead, behind, mtch, ahead]

theorem der_lookahead {l : Lang α} : ∀ (a : α),
    der a (▷ l) = ∅ := by
  intro a
  ext t
  rw [der, lookahead, behind, mtch, ahead, empty]
  simp

theorem derLAhd_lookahead {l : Lang α} : ∀ (a : α),
    derLAhd a (▷ l) = ▷ (der a l) := by
  intro a
  ext t
  rw [derLAhd, lookahead, lookahead, der]
  rw [behind, mtch, ahead, behind, mtch, ahead]
  simp [←and_assoc, and_comm]

end Lang
