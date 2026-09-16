import LookaroundDerivatives.Language

namespace Lang
open Triple


theorem union_assoc : ∀ {l₁ l₂ l₃ : Lang α}, l₁ ∪ (l₂ ∪ l₃) = (l₁ ∪ l₂) ∪ l₃ := by
  intro l₁ l₂ l₃
  ext t
  simp [union, or_assoc]

theorem union_comm : ∀ {k l : Lang α}, k ∪ l = l ∪ k := by
  intro k l
  ext t
  simp [union, or_comm]

theorem union_idem : ∀ {l : Lang α}, l ∪ l = l := by
  intro l
  ext t
  simp [union]


theorem union_identity_l : ∀ {l : Lang α}, ∅ ∪ l = l := by
  intro l
  ext t
  simp [union, empty]

theorem union_identity_r : ∀ {l : Lang α}, l ∪ ∅ = l := by
  intro l
  rw [union_comm, union_identity_l]

-----------------------------------------------------------------------

theorem concat_assoc : ∀ {k l m : Lang α}, k ⊙ (l ⊙ m) = (k ⊙ l) ⊙ m := by
  intro k l m
  ext t
  apply Iff.intro
  . intro ⟨x, y, mt_eq, k_m, lm_m⟩
    have ⟨z, w, mt_eq', l_m, m_m⟩ := lm_m
    rw [behind, mtch, ahead] at *
    subst mt_eq'
    exists (x ++ z), w
    simp at k_m l_m m_m
    simp [mt_eq, m_m]
    exists x, z

  . intro ⟨xy, z, mt_eq, kl_m, m_m⟩
    have ⟨x, y, mt_eq', k_m, l_m⟩ := kl_m
    rw [behind, mtch, ahead] at *
    subst mt_eq'
    exists x, y ++ z
    simp [mt_eq, k_m]
    exists y, z
    rw [behind, mtch, ahead] at *
    simp
    exact ⟨l_m, m_m⟩


theorem concat_zero_l : ∀ {l : Lang α}, ∅ ⊙ l = ∅ := by
  intro l
  ext t
  simp [concat, empty]

theorem concat_zero_r : ∀ {l : Lang α}, l ⊙ ∅ = ∅ := by
  intro l
  ext t
  simp [concat, empty]

theorem concat_unit_l : ∀ {l : Lang α}, 𝟙 ⊙ l = l := by
  intro l
  ext t
  simp [concat, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, eq₂, mem⟩
    rw [mtch] at eq₂
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch]
    simp
    exact mem

theorem concat_unit_r : ∀ {l : Lang α}, l ⊙ 𝟙 = l := by
  intro l
  ext t
  simp [concat, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, mem, eq₂⟩
    rw [mtch] at eq₂
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    exact mem
  . intro mem
    exists mtch t, []
    rw [mtch]
    simp
    exact mem

theorem concat_unit_l_der : ∀ {a : α} {l : Lang α}, ◁ 𝟙 ⊙ (der a l) = der a l := by
  intro a l
  ext t
  simp [concat, lookbehind, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, ⟨eq₂, eq₃⟩, mem⟩
    rw [mtch] at eq₂
    rw [mtch, behind] at eq₃
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    rw [Triple.eta t]
    rw [eq₃]
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch, mtch, behind]
    simp
    exact ⟨der_mem' mem, mem⟩

theorem concat_unit_l_derLAhd : ∀ {a : α} {l : Lang α}, ◁ 𝟙 ⊙ (derLAhd a l) = derLAhd a l := by
  intro a l
  ext t
  simp [concat, lookbehind, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, ⟨eq₂, eq₃⟩, mem⟩
    rw [mtch] at eq₂
    rw [mtch, behind] at eq₃
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    rw [Triple.eta t]
    rw [eq₃]
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch, mtch, behind]
    simp
    exact ⟨(derLAhd_mem' mem).1, mem⟩


theorem concat_subeps_inter {α} : ∀ {k l : Lang α},
                                    k ⊆ 𝟙 → l ⊆ 𝟙 → k ⊙ l = k ∩ l := by
  intro k l k_sub l_sub
  ext t
  apply Iff.intro
  . intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    have m₁_eq : m₁ = [] := k_sub k_m
    have m₂_eq : m₂ = [] := l_sub l_m
    subst m₁_eq
    subst m₂_eq
    simp at mt_eq k_m l_m
    rw [intersection, Triple.eta t, mt_eq]
    exact ⟨k_m, l_m⟩

  . intro ⟨k_m, l_m⟩
    have mt_eq : mtch t = [] := k_sub k_m
    rw [Triple.eta t, mt_eq] at k_m l_m
    rw [concat]
    exists [], []
    simp [mt_eq, k_m, l_m]



-------------------------------------------------------------------------

theorem inter_assoc : ∀ {l₁ l₂ l₃ : Lang α}, l₁ ∩ (l₂ ∩ l₃) = (l₁ ∩ l₂) ∩ l₃ := by
  intro l₁ l₂ l₃
  ext t
  simp [intersection, and_assoc]

theorem inter_comm : ∀ {k l : Lang α}, k ∩ l = l ∩ k := by
  intro k l
  ext t
  simp [intersection, and_comm]

theorem inter_idem : ∀ {l : Lang α}, l ∩ l = l := by
  intro l
  ext t
  simp [intersection]


theorem inter_zero_l : ∀ {l : Lang α}, ∅ ∩ l = ∅ := by
  intro l
  ext t
  simp [intersection, empty]

theorem inter_zero_r : ∀ {l : Lang α}, l ∩ ∅ = ∅ := by
  intro l
  rw [inter_comm, inter_zero_l]

theorem inter_top_l : ∀ {l : Lang α}, 𝕋 ∩ l = l := by
  intro l
  ext t
  simp [intersection, top]

theorem inter_top_r : ∀ {l : Lang α}, l ∩ 𝕋 = l := by
  intro l
  rw [inter_comm, inter_top_l]


theorem union_over_inter : ∀ {k l m : Lang α},
                                 k ∪ (l ∩ m) = (k ∪ l) ∩ (k ∪ m) := by
  intro k l m
  ext t
  rw [union, intersection, intersection, union, union]
  rw [or_and_left]

theorem inter_over_union : ∀ {k l m : Lang α},
                                 k ∩ (l ∪ m) = (k ∩ l) ∪ (k ∩ m) := by
  intro k l m
  ext t
  rw [union, intersection, intersection, union, intersection]
  rw [and_or_left]


theorem union_absorb : ∀ {k l : Lang α},
                         k ∪ (k ∩ l) = k := by
  intro k l
  ext t
  rw [union, intersection]
  calc k t ∨ k t ∧ l t
    _ ↔ k t ∧ True ∨ k t ∧ l t := by rw [and_true]
    _ ↔ k t ∧ (True ∨ l t) := by rw [and_or_left]
    _ ↔ k t := by simp

theorem inter_absorb : ∀ {k l : Lang α},
                         k ∩ (k ∪ l) = k := by
  intro k l
  ext t
  rw [intersection, union]
  calc k t ∧ (k t ∨ l t)
    _ ↔ (k t ∨ False) ∧ (k t ∨ l t)  := by rw [or_false]
    _ ↔ k t ∨  (False ∧ l t)  := by rw[or_and_left]
    _ ↔ k t := by simp


---------------------------------------------------------------------------

theorem diff_zero_l : ∀ {l : Lang α}, ∅ \ l = ∅ := by
  intro l
  ext t
  simp [diff, empty]

theorem diff_top_r : ∀ {l : Lang α}, l \ 𝕋 = ∅ := by
  intro l
  ext t
  simp [diff, top, empty]

theorem union_compl : ∀ {l : Lang α}, l ∪ (𝕋 \ l) = 𝕋 := by
  intro l
  ext t
  simp [union, diff, top]
  open Classical in
  apply em

theorem inter_compl : ∀ {l : Lang α}, l ∩ (𝕋 \ l) = ∅ := by
  intro l
  ext t
  rw [intersection, empty, diff, top]
  simp



-----------------------------------------------------------------------------

theorem lbhd_subeps : ∀ {l : Lang α}, ◁ l ⊆ 𝟙 := by
  intro l t mem
  exact mem.1


theorem lbhd_unit_lahd {α} : (◁ 𝟙 : Lang α) = ▷ (◁ 𝟙 ⊙ 𝕋) := by
  ext t
  rw [lookbehind, unit, mtch, lookahead]
  apply Iff.intro
  . intro ⟨mt_eq, bt_eq⟩
    simp [mt_eq]
    exists [], ahead t

  . intro ⟨mt_eq, mem⟩
    rw [concat, mtch, behind, ahead] at mem
    have ⟨m₁, m₂, at_eq, m, _⟩ := mem
    rw [lookbehind, unit, mtch, mtch, behind] at m
    exact ⟨mt_eq, m.2⟩


theorem lbhd_zero {α} : (◁ ∅ : Lang α) = ∅ := by
  ext t
  simp [lookbehind, empty]

theorem lbhd_top {α} : (◁ 𝕋 : Lang α) = 𝟙 := by
  ext t
  simp [lookbehind, top, unit]

theorem lbhd_inter : ∀ {k l : Lang α}, ◁ k ∩ ◁ l = ◁ (k ∩ l) := by
  intro k l
  ext t
  simp [lookbehind, intersection]
  ac_nf

theorem lbhd_union : ∀ {k l : Lang α}, ◁ k ∪ ◁ l = ◁ (k ∪ l) := by
  intro k l
  ext t
  simp [lookbehind, union, and_or_left]

theorem lbhd_diff : ∀ {k l : Lang α}, ◁ k \ ◁ l = ◁ (k \ l) := by
  intro k l
  ext t
  apply Iff.intro
  . intro ⟨⟨mt_eq, k_m⟩, nl_m⟩
    exact ⟨mt_eq, k_m, λ l_m => nl_m ⟨mt_eq, l_m⟩⟩
  . intro ⟨mt_eq, k_m, nl_m⟩
    exact ⟨⟨mt_eq, k_m⟩, λ l_m => nl_m l_m.2⟩

-------------------------------------------------------------------------------

theorem lahd_subeps : ∀ {l : Lang α}, ▷ l ⊆ 𝟙 := by
  intro l t mem
  exact mem.1


theorem lahd_zero {α} : (▷ ∅ : Lang α) = ∅ := by
  ext t
  simp [lookahead, empty]

theorem lahd_top {α} : (▷ 𝕋 : Lang α) = 𝟙 := by
  ext t
  simp [lookahead, top, unit]

theorem lahd_unit_lbhd : (▷ 𝟙 : Lang α) = ◁ (𝕋 ⊙ ▷ 𝟙) := by
  ext t
  rw [lookahead, unit, mtch, lookbehind]
  apply Iff.intro
  . intro ⟨mt_eq, at_eq⟩
    simp [mt_eq, at_eq]
    exists behind t, []
    simp [top, lookahead, unit, mtch, ahead]

  . intro ⟨mt_eq, mem⟩
    rw [concat, mtch, behind, ahead] at mem
    have ⟨m₁, m₂, at_eq, _, m⟩ := mem
    rw [lookahead, unit, mtch, mtch, ahead] at m
    exact ⟨mt_eq, m.2⟩


theorem lahd_inter : ∀ {k l : Lang α}, ▷ k ∩ ▷ l = ▷ (k ∩ l) := by
  intro k l
  ext t
  simp [lookahead, intersection]
  ac_nf

theorem lahd_union : ∀ {k l : Lang α}, ▷ k ∪ ▷ l = ▷ (k ∪ l) := by
  intro k l
  ext t
  simp [lookahead, union, and_or_left]

theorem lahd_diff : ∀ {k l : Lang α}, ▷ k \ ▷ l = ▷ (k \ l) := by
  intro k l
  ext t
  apply Iff.intro
  . intro ⟨⟨mt_eq, k_m⟩, nl_m⟩
    exact ⟨mt_eq, k_m, λ l_m => nl_m ⟨mt_eq, l_m⟩⟩
  . intro ⟨mt_eq, k_m, nl_m⟩
    exact ⟨⟨mt_eq, k_m⟩, λ l_m => nl_m l_m.2⟩


theorem lahd_concat_assoc : ∀ {l₁ l₂ l₃ : Lang α},
                                ▷ l₁ ⊙ (▷ l₂ ⊙ l₃) = (▷ l₁ ⊙ ▷ l₂) ⊙ l₃ := by
  intro l₁ l₂ l₃
  ext t
  rw [concat_assoc]

theorem lahd_concat_inter {α} : ∀ {k l : Lang α}, ▷ k ⊙ ▷ l = ▷ k ∩ ▷ l := by
  intro k l
  exact concat_subeps_inter lahd_subeps lahd_subeps


--------------------------------------------------------------------------

theorem concat_distr_union_l : ∀ {k l₁ l₂ : Lang α}, k ⊙ (l₁ ∪ l₂) = (k ⊙ l₁) ∪ (k ⊙ l₂) := by
  intro k l₁ l₂
  ext t
  apply Iff.intro
  . intro ⟨m₁, m₂, eq, k_mem, l_mem⟩
    rw [union] at l_mem
    rw [union]
    apply Or.elim l_mem
    . intro l₁_mem
      apply Or.inl
      exists m₁, m₂
    . intro l₂_mem
      apply Or.inr
      exists m₁, m₂

  . intro mem
    apply Or.elim mem
    . intro ⟨m₁, m₂, eq, k_mem, l₁_mem⟩
      exists m₁, m₂
      rw [union]
      simp [eq, k_mem, l₁_mem]

    . intro ⟨m₁, m₂, eq, k_mem, l₂_mem⟩
      exists m₁, m₂
      rw [union]
      simp [eq, k_mem, l₂_mem]


theorem concat_distr_union_r : ∀ {k l m : Lang α}, (k ∪ l) ⊙ m = (k ⊙ m) ∪ (l ⊙ m) := by
  intro k l m
  ext t
  apply Iff.intro
  . intro ⟨x, y, mt_eq, kl_m, m_m⟩
    rw [union] at *
    rcases kl_m with k_m | l_m
    . left
      exists x, y
    . right
      exists x, y

  . intro p
    rcases p with ⟨x, y, mt_eq, k_m, m_m⟩ | ⟨x, y, mt_eq, l_m, m_m⟩
    . exists x, y
      simp [mt_eq, m_m]
      exact Or.inl k_m
    . exists x, y
      simp [mt_eq, m_m]
      exact Or.inr l_m

-------------------------------------------------------------------------------


theorem kstar_lfp_help : ∀ {a b x : Lang α} {t : Triple α},
                               b ∪ a ⊙ x ⊆ x →
                               StarLFP a t →
                               ∀ {m la}, ahead t = m ++ la →
                                 b (behind t ++ mtch t, m, la) →
                                 x (behind t, mtch t ++ m, la) := by
  intro a b x t ss as_m m la eq b_m
  induction as_m with
  | @base t' u_m =>
      rw [unit] at u_m
      simp [u_m] at *
      apply ss
      left
      exact b_m
  | @step lb m₁ m₂ la' m' eq' a_m as_m ih =>
      rw [behind, mtch, ahead] at *
      apply ss
      right
      rw [eq'] at b_m ⊢
      rw [eq] at a_m
      exists m₁, m₂ ++ m
      simp [behind, mtch, ahead]
      rw [←List.append_assoc] at b_m
      exact ⟨a_m, ih eq b_m⟩

theorem kstar_lfp : ∀ {a b x : Lang α}, b ∪ a ⊙ x ⊆ x → a⋆ ⊙ b ⊆ x := by
  intro a b x ss t ⟨m₁, m₂, eq, as_m, b_m⟩
  rw [eta t, eq]
  exact kstar_lfp_help ss as_m rfl b_m




theorem kstar_lfp'_help : ∀ {a b x : Lang α} {t : Triple α},
                                b ∪ x ⊙ a ⊆ x →
                                StarLFP a t →
                                ∀ {lb m}, behind t = lb ++ m →
                                  x (lb, m, mtch t ++ ahead t) →
                                  x (lb, m ++ mtch t, ahead t) := by
  intro a b x t ss as_m lb m eq x_m
  induction as_m generalizing lb m with
  | @base t u_m =>
      rw [unit] at u_m
      simp [u_m] at *
      exact x_m
  | @step lb' m₁ m₂ la m' eq' a_m as_m ih =>
      rw [behind, mtch, ahead] at *
      subst eq eq'
      rw [←List.append_assoc]
      apply @ih lb (m ++ m₁) (by simp)
      apply ss
      right
      exists m, m₁
      rw [behind, mtch, ahead]
      simp at x_m
      simp [a_m, x_m]

theorem kstar_lfp' : ∀ {a b x : Lang α}, b ∪ x ⊙ a ⊆ x → b ⊙ a⋆ ⊆ x := by
  intro a b x ss t ⟨m₁, m₂, eq, b_m, as_m⟩
  rw [eta t, eq]
  exact kstar_lfp'_help ss as_m rfl (ss (Or.inl b_m))




-- Two inclusions that are just the `step` constructor of `StarLFP`.

theorem sub_kstar : ∀ {l : Lang α}, l ⊆ l⋆ := by
  intro l t l_m
  rw [eta t]
  apply StarLFP.step (m₁ := mtch t) (m₂ := []) (by simp)
  . simpa [←eta] using l_m
  . exact StarLFP.base rfl

theorem concat_kstar_sub : ∀ {l : Lang α}, l ⊙ l⋆ ⊆ l⋆ := by
  intro l t ⟨m₁, m₂, eq, l_m, sl_m⟩
  rw [eta t]
  exact StarLFP.step eq l_m sl_m


theorem kstar_concat_lem : ∀ {l : Lang α}, l ⊙ l⋆ = l⋆ ⊙ l := by
  intro l
  have star_l_ss : l⋆ ⊙ l ⊆ l⋆ := by
    apply kstar_lfp
    intro t m
    rcases m with l_m | ll_m
    . exact sub_kstar l_m
    . exact concat_kstar_sub ll_m
  ext t
  apply Iff.intro
  . revert t
    apply kstar_lfp'
    intro t m
    rcases m with l_m | ⟨m₁, m₂, eq, sl_m, l_m⟩
    . exists [], mtch t
      refine ⟨by simp, StarLFP.base rfl, ?_⟩
      simpa [←eta] using l_m
    . exists m₁, m₂
      exact ⟨eq, star_l_ss sl_m, l_m⟩
  . revert t
    apply kstar_lfp
    intro t m
    rcases m with l_m | ⟨m₁, m₂, eq, l_m, sl_m⟩
    . exists mtch t, []
      refine ⟨by simp, ?_, StarLFP.base rfl⟩
      simpa [←eta] using l_m
    . exists m₁, m₂
      exact ⟨eq, l_m, concat_kstar_sub sl_m⟩


theorem kstar_expand : ∀ {l : Lang α}, l⋆ = 𝟙 ∪ l ⊙ l⋆ := by
  intro l
  ext t
  rw [kstar, union]
  apply Iff.intro
  . intro kl_mem
    match kl_mem with
    | .base h => simp [h]
    | .step (m₁ := m₁) (m₂ := m₂) p q r =>
        rw [concat]
        apply Or.inr
        exists m₁, m₂

  . intro p
    apply Or.elim p
    . intro h
      exact .base h
    . intro ⟨m₁, m₂, eq, l_mem, k_mem⟩
      exact .step eq l_mem k_mem

theorem kstar_expand' : ∀ {l : Lang α}, l⋆ = 𝟙 ∪ l⋆ ⊙ l := by
  intro l
  rw [←kstar_concat_lem]
  exact kstar_expand


-------------------------------------------------------------------------------


theorem subset_union_lemma {k l : Lang α} : k ⊆ l ↔ k ∪ l = l := by
  apply Iff.intro
  . intro ss
    ext t
    rw [union]
    simp
    exact ss

  . intro leq
    intro t k_t
    rw [←leq, union]
    simp [k_t]


-------------------------------------------------------------------------------

theorem pla_from_lookahead : ∀ (l : Lang α), ▷ (l ⊙ 𝕋) = pla l := by
  intro l
  ext t
  rw [lookahead, pla]
  apply Iff.intro
  . intro ⟨mt_eq, y, z, at_eq, l_m, _⟩
    rw [behind, mtch, ahead] at *
    simp at l_m
    apply And.intro mt_eq
    exists y, z

  . intro ⟨mt_eq, y, z, at_eq, l_m⟩
    apply And.intro mt_eq
    exists y, z
    rw [behind, mtch, ahead, top]
    simp [at_eq, l_m]


theorem slb_from_lookbehind : ∀ (l : Lang α), ◁ (𝕋 ⊙ l) = slb l := by
  intro l
  ext t
  rw [lookbehind, slb]
  apply Iff.intro
  . intro ⟨mt_eq, x, y, bt_eq, _, l_m⟩
    rw [behind, mtch, ahead] at *
    apply And.intro mt_eq
    exists x, y

  . intro ⟨mt_eq, x, y, bt_eq, l_m⟩
    apply And.intro mt_eq
    exists x, y

end Lang
